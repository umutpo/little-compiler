#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide impose-calling-conventions)

;; Compiles Proc-imp-cmf-lang-v8 to Imp-cmf-lang-v8
;; by imposing calling conventions on all calls and procedure definitions.
;; The parameter registers are defined by the list current-parameter-registers.
;;
;; Proc-imp-cmf-lang-v8 -> Imp-cmf-lang-v8
(define (impose-calling-conventions p)
  (define current-new-frame-variables '())

  ;; (listof Proc-imp-cmf-lang-v8.Opand) boolean -> (listof rloc)
  (define (get-usable-rlocs opands is-non-tail-call)
    (for/fold ([rlocs '()]
               [curr-param-regs (current-parameter-registers)]
               [i 0]
               #:result rlocs)
              ([opand opands])
      (if (empty? curr-param-regs)
          (if is-non-tail-call
              (values (append rlocs (list (fresh `nfv)))
                      '()
                      (add1 i))
              (values (append rlocs (list (make-fvar i)))
                      '()
                      (add1 i)))
          (values (append rlocs (list (first curr-param-regs)))
                  (rest curr-param-regs)
                  i))))

  ;; (listof Any) (listof Any) -> (listof Imp-cmf-lang-v8.Effect)
  (define (set-in-sequence setters settees)
    (for/fold ([loe '()])
              ([s1 setters]
               [s2 settees])
      (append loe (list `(set! ,s1 ,s2)))))

  ;; (listof rloc) -> (listof rloc)
  (define (get-new-frames rlocs)
    (for/fold ([new-frames '()])
              ([rloc rlocs])
      (if (or (register? rloc) (fvar? rloc))
          new-frames
          (append (list rloc) new-frames))))

  ;; Proc-imp-cmf-lang-v8.definition -> Imp-cmf-lang-v8.definition
  (define (impose-calling-conventions-def def)
    (match def
      [`(define ,name (lambda (,params ...) ,entry))
       (let* ([rlocs (get-usable-rlocs params false)]
              [entry (impose-calling-conventions-entry entry (set-in-sequence params rlocs))]
              [new-frame-variables current-new-frame-variables])
         (set! current-new-frame-variables '())
         `(define ,name
            ,(info-set '() 'new-frames new-frame-variables)
            ,entry))]))

  ;; Proc-imp-cmf-lang-v8.Pred (listof rloc) -> Imp-cmf-lang-v8.Pred
  (define (impose-calling-conventions-pred pred)
    (match pred
      [`(true) `(true)]
      [`(false) `(false)]
      [`(not ,pred) `(not ,(impose-calling-conventions-pred pred))]
      [`(begin ,effects ... ,pred)
       `(begin ,@(map impose-calling-conventions-effect effects)
               ,(impose-calling-conventions-pred pred))]
      [`(if ,pred ,pred1 ,pred2)
       `(if ,(impose-calling-conventions-pred pred)
            ,(impose-calling-conventions-pred pred1)
            ,(impose-calling-conventions-pred pred2))]
      [`(,relop ,opand1 ,opand2) pred]))

  ;; Proc-imp-cmf-lang-v8.Tail (listof rloc) -> Imp-cmf-lang-v8.Tail
  (define (impose-calling-conventions-tail tail entry-point)
    (match tail
      [`(begin ,effects ... ,tail)
       `(begin ,@(map impose-calling-conventions-effect effects)
               ,(impose-calling-conventions-tail tail entry-point))]
      [`(if ,pred ,tail1 ,tail2)
       `(if ,(impose-calling-conventions-pred pred)
            ,(impose-calling-conventions-tail tail1 entry-point)
            ,(impose-calling-conventions-tail tail2 entry-point))]
      [`(call ,triv ,opands ...)
       (let ([rlocs (get-usable-rlocs opands false)])
         `(begin ,@(reverse (set-in-sequence rlocs opands))
                 (set! ,(current-return-address-register) ,entry-point)
                 (jump ,triv
                       ,(current-frame-base-pointer-register)
                       ,(current-return-address-register)
                       ,@rlocs)))]
      [value
       `(begin (set! ,(current-return-value-register) ,(impose-calling-conventions-value value))
               (jump ,entry-point ,(current-frame-base-pointer-register) ,(current-return-value-register)))]))

  ;; Proc-imp-cmf-lang-v8.Entry (listof Imp-cmf-lang-v8.Effect) -> Imp-cmf-lang-v8.Entry
  (define (impose-calling-conventions-entry entry loe)
    (let ([entry-point (fresh `tmp-ra)])
      (if (empty? loe)
          `(begin (set! ,entry-point ,(current-return-address-register))
                  ,(impose-calling-conventions-tail entry entry-point))
          `(begin (set! ,entry-point ,(current-return-address-register))
                  (begin ,@loe
                         ,(impose-calling-conventions-tail entry entry-point))))))

  ;; Proc-imp-cmf-lang-v8.Value -> Imp-cmf-lang-v8.Value (listof rloc)
  (define (impose-calling-conventions-value value)
    (match value
      [`(call ,triv ,opands ...)
       (let* ([return-point-label (fresh-label `rp)]
              [rlocs (get-usable-rlocs opands true)]
              [new-frames (get-new-frames rlocs)])
         (set! current-new-frame-variables (append (list new-frames) current-new-frame-variables))
         `(return-point ,return-point-label
                        (begin ,@(set-in-sequence rlocs opands)
                               (set! ,(current-return-address-register) ,return-point-label)
                               (jump ,triv
                                     ,(current-frame-base-pointer-register)
                                     ,(current-return-address-register)
                                     ,@rlocs))))]
      [`(mref ,aloc ,opand) `(mref ,aloc ,opand)]
      [`(alloc ,opand) `(alloc ,opand)]
      [`(,binop ,opand1 ,opand2) `(,binop ,opand1 ,opand2)]
      [triv triv]))

  ;; Proc-imp-cmf-lang-v8.Effect -> Imp-cmf-lang-v8.Effect
  (define (impose-calling-conventions-effect effect)
    (match effect
      [`(set! ,aloc (call ,triv ,opands ...))
       `(begin ,(impose-calling-conventions-value `(call ,triv ,@opands))
               (set! ,aloc ,(current-return-value-register)))]
      [`(set! ,aloc ,value) `(set! ,aloc ,(impose-calling-conventions-value value))]
      [`(mset! ,aloc ,opand ,triv) `(mset! ,aloc ,opand ,triv)]
      [`(begin ,effects ... ,effect)
       `(begin ,@(map impose-calling-conventions-effect effects)
               ,(impose-calling-conventions-effect effect))]
      [`(if ,pred ,effect1 ,effect2)
       `(if ,(impose-calling-conventions-pred pred)
            ,(impose-calling-conventions-effect effect1)
            ,(impose-calling-conventions-effect effect2))]))

  (match p
    [`(module ,defs ... ,entry)
     (let* ([entry (impose-calling-conventions-entry entry '())]
            [new-frame-variables current-new-frame-variables])
       (set! current-new-frame-variables '())
       `(module ,(info-set '() 'new-frames new-frame-variables)
          ,@(map impose-calling-conventions-def defs)
          ,entry))]))

(module+ tests
  (check-equal?
    (impose-calling-conventions
    '(module (+ 2 2)))
    '(module
        ((new-frames ()))
      (begin
        (set! tmp-ra.1 r15)
        (begin (set! rax (+ 2 2)) (jump tmp-ra.1 rbp rax)))))

  (check-equal?
    (impose-calling-conventions
    '(module (begin (set! x.1 5) x.1)))
    '(module
        ((new-frames ()))
      (begin
        (set! tmp-ra.2 r15)
        (begin (set! x.1 5) (begin (set! rax x.1) (jump tmp-ra.2 rbp rax))))))

  (check-equal?
    (impose-calling-conventions
    '(module
          (begin
            (if (true) (begin (set! y.2 14) (set! x.5 12)) (begin (set! x.5 15)))
            x.5)))
    '(module
        ((new-frames ()))
      (begin
        (set! tmp-ra.3 r15)
        (begin
          (if (true) (begin (set! y.2 14) (set! x.5 12)) (begin (set! x.5 15)))
          (begin (set! rax x.5) (jump tmp-ra.3 rbp rax))))))

  (check-equal?
    (impose-calling-conventions
    '(module
          (define L.odd?.5
            (lambda (x.51)
              (if (= x.51 0) 0 (begin (set! y.52 (+ x.51 -1)) (call L.even?.6 y.52)))))
        (define L.even?.6
          (lambda (x.53)
            (if (= x.53 0) 1 (begin (set! y.54 (+ x.53 -1)) (call L.odd?.5 y.54)))))
        (call L.even?.6 5)))
    '(module
        ((new-frames ()))
      (define L.odd?.5
        ((new-frames ()))
        (begin
          (set! tmp-ra.5 r15)
          (begin
            (set! x.51 rdi)
            (if (= x.51 0)
                (begin (set! rax 0) (jump tmp-ra.5 rbp rax))
                (begin
                  (set! y.52 (+ x.51 -1))
                  (begin
                    (set! rdi y.52)
                    (set! r15 tmp-ra.5)
                    (jump L.even?.6 rbp r15 rdi)))))))
      (define L.even?.6
        ((new-frames ()))
        (begin
          (set! tmp-ra.6 r15)
          (begin
            (set! x.53 rdi)
            (if (= x.53 0)
                (begin (set! rax 1) (jump tmp-ra.6 rbp rax))
                (begin
                  (set! y.54 (+ x.53 -1))
                  (begin
                    (set! rdi y.54)
                    (set! r15 tmp-ra.6)
                    (jump L.odd?.5 rbp r15 rdi)))))))
      (begin
        (set! tmp-ra.4 r15)
        (begin (set! rdi 5) (set! r15 tmp-ra.4) (jump L.even?.6 rbp r15 rdi)))))

  (check-equal?
    (impose-calling-conventions
    '(module
          (define L.id.2 (lambda (x.15) x.15))
        (begin (set! y.16 L.id.2) (call y.16 5))))
    '(module
        ((new-frames ()))
      (define L.id.2
        ((new-frames ()))
        (begin
          (set! tmp-ra.8 r15)
          (begin (set! x.15 rdi) (begin (set! rax x.15) (jump tmp-ra.8 rbp rax)))))
      (begin
        (set! tmp-ra.7 r15)
        (begin
          (set! y.16 L.id.2)
          (begin (set! rdi 5) (set! r15 tmp-ra.7) (jump y.16 rbp r15 rdi))))))

  (check-equal?
    (impose-calling-conventions
    '(module (define L.zero.8 (lambda (v0.77 v1.78 v2.79 v3.80) 0)) 0))
    '(module
        ((new-frames ()))
      (define L.zero.8
        ((new-frames ()))
        (begin
          (set! tmp-ra.10 r15)
          (begin
            (set! v0.77 rdi)
            (set! v1.78 rsi)
            (set! v2.79 rdx)
            (set! v3.80 rcx)
            (begin (set! rax 0) (jump tmp-ra.10 rbp rax)))))
      (begin (set! tmp-ra.9 r15) (begin (set! rax 0) (jump tmp-ra.9 rbp rax)))))

  (check-equal?
    (impose-calling-conventions
    '(module (define L.zero.8 (lambda (v0.77 v1.78 v2.79 v3.80 v4.81 v5.82 v6.83 v7.84 v8.85) 0))
        (begin (set! y.16 L.zero.8) (call y.16 1 2 3 4 5 6 7 8 9))))
    '(module
        ((new-frames ()))
      (define L.zero.8
        ((new-frames ()))
        (begin
          (set! tmp-ra.12 r15)
          (begin
            (set! v0.77 rdi)
            (set! v1.78 rsi)
            (set! v2.79 rdx)
            (set! v3.80 rcx)
            (set! v4.81 r8)
            (set! v5.82 r9)
            (set! v6.83 fv0)
            (set! v7.84 fv1)
            (set! v8.85 fv2)
            (begin (set! rax 0) (jump tmp-ra.12 rbp rax)))))
      (begin
        (set! tmp-ra.11 r15)
        (begin
          (set! y.16 L.zero.8)
          (begin
            (set! fv2 9)
            (set! fv1 8)
            (set! fv0 7)
            (set! r9 6)
            (set! r8 5)
            (set! rcx 4)
            (set! rdx 3)
            (set! rsi 2)
            (set! rdi 1)
            (set! r15 tmp-ra.11)
            (jump y.16 rbp r15 rdi rsi rdx rcx r8 r9 fv0 fv1 fv2))))))
)