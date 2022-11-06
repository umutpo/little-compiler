#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide assign-call-undead-variables)

(define (my-flatten lst)
  (foldr append '() lst))

;; Compiles Asm-pred-lang-v6/conflicts to Asm-pred-lang-v6/pre-framed by
;; pre-assigning all variables in the call-undead sets to to frame variables.
;;
;; asm-pred-lang-v6/conflicts -> asm-pred-lang-v6/pre-framed
(define (assign-call-undead-variables p)
  ;; Graph -> (list aloc (listof aloc))
  (define (sort-graph graph)
    (sort (dict->list graph) #:key (λ (x) (length (second x))) <))

  ;; (listof loc) Graph (dict loc -> (listof loc)) -> (dict loc -> (listof loc))
  (define (assign-call-undead-variables-helper call-undead conflict-graph assignments)

    ;; loc (listof fvar) -> fvar
    (define (assigner curr-call-undead cannot-be-assigned curr-index)
      (let ([curr-fvar (make-fvar curr-index)])
        (if (member curr-fvar cannot-be-assigned)
            (assigner curr-call-undead cannot-be-assigned (add1 curr-index))
            curr-fvar)))

    ;; loc (listof loc) (dict loc -> (listof loc)) -> (dict loc -> (listof loc))
    (define (assign-call-undead-variables--one curr-call-undead conflicts assignments)
      (let ([cannot-be-assigned
             (for/fold ([conflict-assigned '()])
                       ([conflict conflicts])
               (if (fvar? conflict)
                   (append conflict-assigned (list conflict))
                   (append conflict-assigned (my-flatten (list (dict-ref assignments conflict '()))))))])
        (let ([suitable-fvar (assigner curr-call-undead cannot-be-assigned 0)])
          (dict-set assignments curr-call-undead (list suitable-fvar)))))

    ;; (listof loc) Graph (dict loc -> (listof loc)) -> (dict loc -> (listof loc))
    (define (assign-call-undead-variables--all call-undead conflicts-graph assignments)
      (if (empty? call-undead)
          assignments
          (let* ([first-call-undead (first call-undead)]
                 [next-call-undead (rest call-undead)]
                 [new-assignments (assign-call-undead-variables--all next-call-undead conflicts-graph assignments)])
            (assign-call-undead-variables--one first-call-undead (get-neighbors conflicts-graph first-call-undead) new-assignments))))

    (assign-call-undead-variables--all call-undead (sort-graph conflict-graph) assignments))

  ;; (listof loc) (setof loc) -> (setof loc)
  (define (remove-call-undead-from-locals call-undead locals)
    (cond
      [(empty? call-undead) (reverse locals)]
      [else (remove-call-undead-from-locals (rest call-undead) (set-remove locals (first call-undead)))]))

  ;; asm-pred-lang-v6/conflicts.Info -> asm-pred-lang-v6/pre-framed.Info
  (define (assign-call-undead-variables-info info)
    (let ([call-undead (info-ref info 'call-undead)]
          [locals (info-ref info 'locals)]
          [conflicts (info-ref info 'conflicts)])
      (info-set (info-set info 'locals (remove-call-undead-from-locals call-undead locals))
                'assignment
                (assign-call-undead-variables-helper call-undead conflicts '()))))

  ;; asm-pred-lang-v6/conflicts.Definition -> asm-pred-lang-v6/pre-framed.Definition
  (define (assign-call-undead-variables-def def)
    (match def
      [`(define ,label ,info ,tail)
       `(define ,label
          ,(assign-call-undead-variables-info info)
          ,tail)]))

  (match p
    [`(module ,info ,defs ... ,tail)
     `(module ,(assign-call-undead-variables-info info)
        ,@(map assign-call-undead-variables-def defs)
        ,tail)]))

(module+ tests
  (check-equal?
    (assign-call-undead-variables
    '(module
          ((new-frames ())
          (locals (tmp-ra.2))
          (call-undead ())
          (undead-out
            ((tmp-ra.2 rbp)
            (tmp-ra.2 rsi rbp)
            (tmp-ra.2 rsi rdi rbp)
            (rsi rdi r15 rbp)
            (rsi rdi r15 rbp)))
          (conflicts
            ((tmp-ra.2 (rdi rsi rbp))
            (rbp (r15 rdi rsi tmp-ra.2))
            (rsi (r15 rdi rbp tmp-ra.2))
            (rdi (r15 rbp rsi tmp-ra.2))
            (r15 (rbp rdi rsi)))))
        (define L.swap.1
          ((new-frames (()))
          (locals (z.3 tmp-ra.1 x.1 y.2))
          (undead-out
            ((rdi rsi tmp-ra.1 rbp)
            (rsi x.1 tmp-ra.1 rbp)
            (y.2 x.1 tmp-ra.1 rbp)
            ((y.2 x.1 tmp-ra.1 rbp)
              ((tmp-ra.1 rax rbp) (rax rbp))
              (((rax tmp-ra.1 rbp)
                ((y.2 rsi rbp) (rsi rdi rbp) (rsi rdi r15 rbp) (rsi rdi r15 rbp)))
              (z.3 tmp-ra.1 rbp)
              (tmp-ra.1 rax rbp)
              (rax rbp)))))
          (call-undead (tmp-ra.1))
          (conflicts
            ((y.2 (rbp tmp-ra.1 x.1 rsi))
            (x.1 (y.2 rbp tmp-ra.1 rsi))
            (tmp-ra.1 (y.2 x.1 rbp rsi rdi rax z.3))
            (z.3 (rbp tmp-ra.1))
            (rsi (x.1 tmp-ra.1 r15 rdi rbp y.2))
            (rbp (y.2 x.1 tmp-ra.1 rax z.3 r15 rdi rsi))
            (rdi (tmp-ra.1 r15 rbp rsi))
            (r15 (rbp rdi rsi))
            (rax (rbp tmp-ra.1)))))
          (begin
            (set! tmp-ra.1 r15)
            (set! x.1 rdi)
            (set! y.2 rsi)
            (if (< y.2 x.1)
                (begin (set! rax x.1) (jump tmp-ra.1 rbp rax))
                (begin
                  (return-point L.rp.1
                                (begin
                                  (set! rsi x.1)
                                  (set! rdi y.2)
                                  (set! r15 L.rp.1)
                                  (jump L.swap.1 rbp r15 rdi rsi)))
                  (set! z.3 rax)
                  (set! rax z.3)
                  (jump tmp-ra.1 rbp rax)))))
        (begin
          (set! tmp-ra.2 r15)
          (set! rsi 2)
          (set! rdi 1)
          (set! r15 tmp-ra.2)
          (jump L.swap.1 rbp r15 rdi rsi))))
    '(module
        ((new-frames ())
          (locals (tmp-ra.2))
          (call-undead ())
          (undead-out
          ((tmp-ra.2 rbp)
            (tmp-ra.2 rsi rbp)
            (tmp-ra.2 rsi rdi rbp)
            (rsi rdi r15 rbp)
            (rsi rdi r15 rbp)))
          (conflicts
          ((tmp-ra.2 (rdi rsi rbp))
            (rbp (r15 rdi rsi tmp-ra.2))
            (rsi (r15 rdi rbp tmp-ra.2))
            (rdi (r15 rbp rsi tmp-ra.2))
            (r15 (rbp rdi rsi))))
          (assignment ()))
      (define L.swap.1
        ((new-frames (()))
          (locals (y.2 x.1 z.3))
          (undead-out
          ((rdi rsi tmp-ra.1 rbp)
            (rsi x.1 tmp-ra.1 rbp)
            (y.2 x.1 tmp-ra.1 rbp)
            ((y.2 x.1 tmp-ra.1 rbp)
            ((tmp-ra.1 rax rbp) (rax rbp))
            (((rax tmp-ra.1 rbp)
              ((y.2 rsi rbp) (rsi rdi rbp) (rsi rdi r15 rbp) (rsi rdi r15 rbp)))
              (z.3 tmp-ra.1 rbp)
              (tmp-ra.1 rax rbp)
              (rax rbp)))))
          (call-undead (tmp-ra.1))
          (conflicts
          ((y.2 (rbp tmp-ra.1 x.1 rsi))
            (x.1 (y.2 rbp tmp-ra.1 rsi))
            (tmp-ra.1 (y.2 x.1 rbp rsi rdi rax z.3))
            (z.3 (rbp tmp-ra.1))
            (rsi (x.1 tmp-ra.1 r15 rdi rbp y.2))
            (rbp (y.2 x.1 tmp-ra.1 rax z.3 r15 rdi rsi))
            (rdi (tmp-ra.1 r15 rbp rsi))
            (r15 (rbp rdi rsi))
            (rax (rbp tmp-ra.1))))
          (assignment ((tmp-ra.1 fv0))))
        (begin
          (set! tmp-ra.1 r15)
          (set! x.1 rdi)
          (set! y.2 rsi)
          (if (< y.2 x.1)
              (begin (set! rax x.1) (jump tmp-ra.1 rbp rax))
              (begin
                (return-point L.rp.1
                              (begin
                                (set! rsi x.1)
                                (set! rdi y.2)
                                (set! r15 L.rp.1)
                                (jump L.swap.1 rbp r15 rdi rsi)))
                (set! z.3 rax)
                (set! rax z.3)
                (jump tmp-ra.1 rbp rax)))))
      (begin
        (set! tmp-ra.2 r15)
        (set! rsi 2)
        (set! rdi 1)
        (set! r15 tmp-ra.2)
        (jump L.swap.1 rbp r15 rdi rsi))))

  (check-equal?
    (assign-call-undead-variables
    '(module
          ((new-frames ())
          (locals (tmp-ra.3))
          (call-undead ())
          (undead-out
            ((tmp-ra.3 rbp)
            (tmp-ra.3 rsi rbp)
            (tmp-ra.3 rsi rdi rbp)
            (rsi rdi r15 rbp)
            (rsi rdi r15 rbp)))
          (conflicts
            ((tmp-ra.3 (rdi rsi rbp))
            (rbp (r15 rdi rsi tmp-ra.3))
            (rsi (r15 rdi rbp tmp-ra.3))
            (rdi (r15 rbp rsi tmp-ra.3))
            (r15 (rbp rdi rsi)))))
        (define L.add.1
          ((new-frames (()))
          (locals (tmp-ra.1 z.3 x.1 y.2))
          (undead-out
            ((rdi rsi tmp-ra.1 rbp)
            (rsi x.1 tmp-ra.1 rbp)
            (x.1 y.2 tmp-ra.1 rbp)
            ((x.1 y.2 tmp-ra.1 rbp)
              (((rax tmp-ra.1 rbp)
                ((y.2 rsi rbp) (rsi rdi rbp) (rsi rdi r15 rbp) (rsi rdi r15 rbp)))
              (z.3 tmp-ra.1 rbp)
              (tmp-ra.1 rax rbp)
              (rax rbp))
              ((y.2 rax tmp-ra.1 rbp) (tmp-ra.1 rax rbp) (rax rbp)))))
          (call-undead (tmp-ra.1))
          (conflicts
            ((y.2 (rbp tmp-ra.1 x.1 rsi rax))
            (x.1 (y.2 rbp tmp-ra.1 rsi))
            (z.3 (rbp tmp-ra.1))
            (tmp-ra.1 (y.2 x.1 rbp rsi rdi z.3 rax))
            (rax (rbp tmp-ra.1 y.2))
            (rbp (y.2 x.1 tmp-ra.1 z.3 r15 rdi rsi rax))
            (rsi (x.1 tmp-ra.1 r15 rdi rbp y.2))
            (rdi (tmp-ra.1 r15 rbp rsi))
            (r15 (rbp rdi rsi)))))
          (begin
            (set! tmp-ra.1 r15)
            (set! x.1 rdi)
            (set! y.2 rsi)
            (if (= y.2 x.1)
                (begin
                  (return-point L.rp.1
                                (begin
                                  (set! rsi 2)
                                  (set! rdi y.2)
                                  (set! r15 L.rp.1)
                                  (jump L.add.1 rbp r15 rdi rsi)))
                  (set! z.3 rax)
                  (set! rax z.3)
                  (jump tmp-ra.1 rbp rax))
                (begin
                  (set! rax x.1)
                  (set! rax (+ rax y.2))
                  (jump tmp-ra.1 rbp rax)))))
        (define L.add.2
          ((new-frames (()))
          (locals (tmp-ra.2 z.4 x.2 y.3))
          (undead-out
            ((rdi rsi tmp-ra.2 rbp)
            (rsi x.2 tmp-ra.2 rbp)
            (x.2 y.3 tmp-ra.2 rbp)
            ((x.2 y.3 tmp-ra.2 rbp)
              (((rax tmp-ra.2 rbp)
                ((y.3 rsi rbp) (rsi rdi rbp) (rsi rdi r15 rbp) (rsi rdi r15 rbp)))
              (z.4 tmp-ra.2 rbp)
              (tmp-ra.2 rax rbp)
              (rax rbp))
              ((y.3 rax tmp-ra.2 rbp) (tmp-ra.2 rax rbp) (rax rbp)))))
          (call-undead (tmp-ra.2))
          (conflicts
            ((y.3 (rbp tmp-ra.2 x.2 rsi rax))
            (x.2 (y.3 rbp tmp-ra.2 rsi))
            (z.4 (rbp tmp-ra.2))
            (tmp-ra.2 (y.3 x.2 rbp rsi rdi z.4 rax))
            (rax (rbp tmp-ra.2 y.3))
            (rbp (y.3 x.2 tmp-ra.2 z.4 r15 rdi rsi rax))
            (rsi (x.2 tmp-ra.2 r15 rdi rbp y.3))
            (rdi (tmp-ra.2 r15 rbp rsi))
            (r15 (rbp rdi rsi)))))
          (begin
            (set! tmp-ra.2 r15)
            (set! x.2 rdi)
            (set! y.3 rsi)
            (if (= y.3 x.2)
                (begin
                  (return-point L.rp.2
                                (begin
                                  (set! rsi 3)
                                  (set! rdi y.3)
                                  (set! r15 L.rp.2)
                                  (jump L.add.1 rbp r15 rdi rsi)))
                  (set! z.4 rax)
                  (set! rax z.4)
                  (jump tmp-ra.2 rbp rax))
                (begin
                  (set! rax x.2)
                  (set! rax (+ rax y.3))
                  (jump tmp-ra.2 rbp rax)))))
        (begin
          (set! tmp-ra.3 r15)
          (set! rsi 2)
          (set! rdi 1)
          (set! r15 tmp-ra.3)
          (jump L.swap.1 rbp r15 rdi rsi))))
    '(module
        ((new-frames ())
          (locals (tmp-ra.3))
          (call-undead ())
          (undead-out
          ((tmp-ra.3 rbp)
            (tmp-ra.3 rsi rbp)
            (tmp-ra.3 rsi rdi rbp)
            (rsi rdi r15 rbp)
            (rsi rdi r15 rbp)))
          (conflicts
          ((tmp-ra.3 (rdi rsi rbp))
            (rbp (r15 rdi rsi tmp-ra.3))
            (rsi (r15 rdi rbp tmp-ra.3))
            (rdi (r15 rbp rsi tmp-ra.3))
            (r15 (rbp rdi rsi))))
          (assignment ()))
      (define L.add.1
        ((new-frames (()))
          (locals (y.2 x.1 z.3))
          (undead-out
          ((rdi rsi tmp-ra.1 rbp)
            (rsi x.1 tmp-ra.1 rbp)
            (x.1 y.2 tmp-ra.1 rbp)
            ((x.1 y.2 tmp-ra.1 rbp)
            (((rax tmp-ra.1 rbp)
              ((y.2 rsi rbp) (rsi rdi rbp) (rsi rdi r15 rbp) (rsi rdi r15 rbp)))
              (z.3 tmp-ra.1 rbp)
              (tmp-ra.1 rax rbp)
              (rax rbp))
            ((y.2 rax tmp-ra.1 rbp) (tmp-ra.1 rax rbp) (rax rbp)))))
          (call-undead (tmp-ra.1))
          (conflicts
          ((y.2 (rbp tmp-ra.1 x.1 rsi rax))
            (x.1 (y.2 rbp tmp-ra.1 rsi))
            (z.3 (rbp tmp-ra.1))
            (tmp-ra.1 (y.2 x.1 rbp rsi rdi z.3 rax))
            (rax (rbp tmp-ra.1 y.2))
            (rbp (y.2 x.1 tmp-ra.1 z.3 r15 rdi rsi rax))
            (rsi (x.1 tmp-ra.1 r15 rdi rbp y.2))
            (rdi (tmp-ra.1 r15 rbp rsi))
            (r15 (rbp rdi rsi))))
          (assignment ((tmp-ra.1 fv0))))
        (begin
          (set! tmp-ra.1 r15)
          (set! x.1 rdi)
          (set! y.2 rsi)
          (if (= y.2 x.1)
              (begin
                (return-point L.rp.1
                              (begin
                                (set! rsi 2)
                                (set! rdi y.2)
                                (set! r15 L.rp.1)
                                (jump L.add.1 rbp r15 rdi rsi)))
                (set! z.3 rax)
                (set! rax z.3)
                (jump tmp-ra.1 rbp rax))
              (begin
                (set! rax x.1)
                (set! rax (+ rax y.2))
                (jump tmp-ra.1 rbp rax)))))
      (define L.add.2
        ((new-frames (()))
          (locals (y.3 x.2 z.4))
          (undead-out
          ((rdi rsi tmp-ra.2 rbp)
            (rsi x.2 tmp-ra.2 rbp)
            (x.2 y.3 tmp-ra.2 rbp)
            ((x.2 y.3 tmp-ra.2 rbp)
            (((rax tmp-ra.2 rbp)
              ((y.3 rsi rbp) (rsi rdi rbp) (rsi rdi r15 rbp) (rsi rdi r15 rbp)))
              (z.4 tmp-ra.2 rbp)
              (tmp-ra.2 rax rbp)
              (rax rbp))
            ((y.3 rax tmp-ra.2 rbp) (tmp-ra.2 rax rbp) (rax rbp)))))
          (call-undead (tmp-ra.2))
          (conflicts
          ((y.3 (rbp tmp-ra.2 x.2 rsi rax))
            (x.2 (y.3 rbp tmp-ra.2 rsi))
            (z.4 (rbp tmp-ra.2))
            (tmp-ra.2 (y.3 x.2 rbp rsi rdi z.4 rax))
            (rax (rbp tmp-ra.2 y.3))
            (rbp (y.3 x.2 tmp-ra.2 z.4 r15 rdi rsi rax))
            (rsi (x.2 tmp-ra.2 r15 rdi rbp y.3))
            (rdi (tmp-ra.2 r15 rbp rsi))
            (r15 (rbp rdi rsi))))
          (assignment ((tmp-ra.2 fv0))))
        (begin
          (set! tmp-ra.2 r15)
          (set! x.2 rdi)
          (set! y.3 rsi)
          (if (= y.3 x.2)
              (begin
                (return-point L.rp.2
                              (begin
                                (set! rsi 3)
                                (set! rdi y.3)
                                (set! r15 L.rp.2)
                                (jump L.add.1 rbp r15 rdi rsi)))
                (set! z.4 rax)
                (set! rax z.4)
                (jump tmp-ra.2 rbp rax))
              (begin
                (set! rax x.2)
                (set! rax (+ rax y.3))
                (jump tmp-ra.2 rbp rax)))))
      (begin
        (set! tmp-ra.3 r15)
        (set! rsi 2)
        (set! rdi 1)
        (set! r15 tmp-ra.3)
        (jump L.swap.1 rbp r15 rdi rsi))))

  (check-equal?
    (assign-call-undead-variables
    '(module
          ((new-frames ())
          (locals (tmp-ra.4))
          (call-undead ())
          (undead-out
            ((tmp-ra.4 rbp)
            (tmp-ra.4 fv1 rbp)
            (tmp-ra.4 fv1 fv0 rbp)
            (fv1 fv0 r15 rbp)
            (fv1 fv0 r15 rbp)))
          (conflicts
            ((tmp-ra.4 (fv0 fv1 rbp))
            (rbp (r15 fv0 fv1 tmp-ra.4))
            (fv1 (r15 fv0 rbp tmp-ra.4))
            (fv0 (r15 rbp fv1 tmp-ra.4))
            (r15 (rbp fv0 fv1)))))
        (define L.add.1
          ((new-frames ((nfv.2 nfv.3)))
          (locals (nfv.2 nfv.3 z.3 tmp-ra.1 x.2 x.3 x.1 y.2))
          (undead-out
            ((fv0 fv1 tmp-ra.1 rbp)
            (fv1 x.1 tmp-ra.1 rbp)
            (x.1 y.2 tmp-ra.1 rbp)
            (x.1 y.2 x.2 tmp-ra.1 rbp)
            (x.1 y.2 x.2 x.3 tmp-ra.1 rbp)
            ((y.2 x.2 x.3 tmp-ra.1 rbp)
              ((x.3 rax tmp-ra.1 rbp) (tmp-ra.1 rax rbp) (rax rbp))
              (((rax tmp-ra.1 rbp)
                ((y.2 nfv.3 rbp)
                (nfv.3 nfv.2 rbp)
                (nfv.3 nfv.2 r15 rbp)
                (nfv.3 nfv.2 r15 rbp)))
              (z.3 tmp-ra.1 rbp)
              (tmp-ra.1 rax rbp)
              (rax rbp)))))
          (call-undead (tmp-ra.1 x.2 x.3))
          (conflicts
            ((y.2 (x.3 x.2 rbp tmp-ra.1 x.1 nfv.3))
            (x.1 (x.3 x.2 y.2 rbp tmp-ra.1 fv1))
            (x.3 (rbp tmp-ra.1 x.2 y.2 x.1 rax))
            (x.2 (x.3 rbp tmp-ra.1 y.2 x.1))
            (tmp-ra.1 (x.3 x.2 y.2 x.1 rbp fv1 fv0 rax z.3))
            (z.3 (rbp tmp-ra.1))
            (nfv.3 (r15 nfv.2 rbp y.2))
            (nfv.2 (r15 rbp nfv.3))
            (rbp (x.3 x.2 y.2 x.1 tmp-ra.1 rax z.3 r15 nfv.2 nfv.3))
            (r15 (rbp nfv.2 nfv.3))
            (rax (x.3 rbp tmp-ra.1))
            (fv0 (tmp-ra.1))
            (fv1 (x.1 tmp-ra.1)))))
          (begin
            (set! tmp-ra.1 r15)
            (set! x.1 fv0)
            (set! y.2 fv1)
            (set! x.2 6)
            (set! x.3 8)
            (if (< y.2 x.1)
                (begin (set! rax x.2) (set! rax (+ rax x.3)) (jump tmp-ra.1 rbp rax))
                (begin
                  (return-point L.rp.1
                                (begin
                                  (set! nfv.3 x.2)
                                  (set! nfv.2 y.2)
                                  (set! r15 L.rp.1)
                                  (jump L.add.1 rbp r15 nfv.2 nfv.3)))
                  (set! z.3 rax)
                  (set! rax z.3)
                  (jump tmp-ra.1 rbp rax)))))
        (begin
          (set! tmp-ra.4 r15)
          (set! fv1 2)
          (set! fv0 1)
          (set! r15 tmp-ra.4)
          (jump L.add.1 rbp r15 fv0 fv1))))
    '(module
        ((new-frames ())
          (locals (tmp-ra.4))
          (call-undead ())
          (undead-out
          ((tmp-ra.4 rbp)
            (tmp-ra.4 fv1 rbp)
            (tmp-ra.4 fv1 fv0 rbp)
            (fv1 fv0 r15 rbp)
            (fv1 fv0 r15 rbp)))
          (conflicts
          ((tmp-ra.4 (fv0 fv1 rbp))
            (rbp (r15 fv0 fv1 tmp-ra.4))
            (fv1 (r15 fv0 rbp tmp-ra.4))
            (fv0 (r15 rbp fv1 tmp-ra.4))
            (r15 (rbp fv0 fv1))))
          (assignment ()))
      (define L.add.1
        ((new-frames ((nfv.2 nfv.3)))
          (locals (y.2 x.1 z.3 nfv.3 nfv.2))
          (undead-out
          ((fv0 fv1 tmp-ra.1 rbp)
            (fv1 x.1 tmp-ra.1 rbp)
            (x.1 y.2 tmp-ra.1 rbp)
            (x.1 y.2 x.2 tmp-ra.1 rbp)
            (x.1 y.2 x.2 x.3 tmp-ra.1 rbp)
            ((y.2 x.2 x.3 tmp-ra.1 rbp)
            ((x.3 rax tmp-ra.1 rbp) (tmp-ra.1 rax rbp) (rax rbp))
            (((rax tmp-ra.1 rbp)
              ((y.2 nfv.3 rbp)
                (nfv.3 nfv.2 rbp)
                (nfv.3 nfv.2 r15 rbp)
                (nfv.3 nfv.2 r15 rbp)))
              (z.3 tmp-ra.1 rbp)
              (tmp-ra.1 rax rbp)
              (rax rbp)))))
          (call-undead (tmp-ra.1 x.2 x.3))
          (conflicts
          ((y.2 (x.3 x.2 rbp tmp-ra.1 x.1 nfv.3))
            (x.1 (x.3 x.2 y.2 rbp tmp-ra.1 fv1))
            (x.3 (rbp tmp-ra.1 x.2 y.2 x.1 rax))
            (x.2 (x.3 rbp tmp-ra.1 y.2 x.1))
            (tmp-ra.1 (x.3 x.2 y.2 x.1 rbp fv1 fv0 rax z.3))
            (z.3 (rbp tmp-ra.1))
            (nfv.3 (r15 nfv.2 rbp y.2))
            (nfv.2 (r15 rbp nfv.3))
            (rbp (x.3 x.2 y.2 x.1 tmp-ra.1 rax z.3 r15 nfv.2 nfv.3))
            (r15 (rbp nfv.2 nfv.3))
            (rax (x.3 rbp tmp-ra.1))
            (fv0 (tmp-ra.1))
            (fv1 (x.1 tmp-ra.1))))
          (assignment ((x.3 fv0) (x.2 fv1) (tmp-ra.1 fv2))))
        (begin
          (set! tmp-ra.1 r15)
          (set! x.1 fv0)
          (set! y.2 fv1)
          (set! x.2 6)
          (set! x.3 8)
          (if (< y.2 x.1)
              (begin (set! rax x.2) (set! rax (+ rax x.3)) (jump tmp-ra.1 rbp rax))
              (begin
                (return-point L.rp.1
                              (begin
                                (set! nfv.3 x.2)
                                (set! nfv.2 y.2)
                                (set! r15 L.rp.1)
                                (jump L.add.1 rbp r15 nfv.2 nfv.3)))
                (set! z.3 rax)
                (set! rax z.3)
                (jump tmp-ra.1 rbp rax)))))
      (begin
        (set! tmp-ra.4 r15)
        (set! fv1 2)
        (set! fv0 1)
        (set! r15 tmp-ra.4)
        (jump L.add.1 rbp r15 fv0 fv1))))
)