#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide select-instructions)

;; Compiles imp-cmf-lang-v8 to asm-alloc-lang-v8,
;; selecting appropriate sequences of abstract assembly instructions
;; to implement the operations of the source language.
;;
;; imp-cmf-lang-v8 -> asm-alloc-lang-v8
(define (select-instructions p)

  ;; Any -> Boolean
  (define (opand? opand)
    (or (aloc? opand)
        (int64? opand)
        (register? opand)
        (fvar? opand)))

  ; imp-cmf-lang-v8.Value -> (listof asm-alloc-lang-v8.Effect) and asm-alloc-lang-v8.aloc
  ; Assigns the value v to a fresh temporary, returning two values: the list of
  ; statements the implement the assignment in Loc-lang, and the aloc that the
  ; value is stored in.
  (define (assign-tmp v)
    (match v
      [`(mref ,loc ,opand)
       (let ([tmp (fresh)])
         (values (list `(set! ,tmp (mref ,loc ,opand))) tmp))]
      [`(alloc ,opand)
       (let ([tmp (fresh)])
         (values (list `(set! ,tmp (alloc ,opand))) tmp))]
      [`(,binop ,opand_1 ,opand_2)
       #:when (and (opand? opand_1) (opand? opand_2))
       (let ([tmp (fresh)])
         (values (list `(set! ,tmp ,opand_1) `(set! ,tmp (,binop ,tmp ,opand_2))) tmp))]))

  ;; imp-cmf-lang-v8.Def -> asm-alloc-lang-v8.Def
  (define (select-instructions-def e)
    (match e
      [`(define ,label ,info ,tail)
       `(define ,label ,info ,(select-instructions-tail tail))]))

  ;; imp-cmf-lang-v8.Tail -> asm-alloc-lang-v8.Tail
  (define (select-instructions-tail e)
    (match e
      [`(begin ,effects ... ,tail)
       `(begin ,@(map select-instructions-effect effects) ,(select-instructions-tail tail))]
      [`(if ,pred ,tail1 ,tail2)
       `(if ,(select-instructions-pred pred)
            ,(select-instructions-tail tail1)
            ,(select-instructions-tail tail2))]
      [`(jump ,trg ,locs ...) `(jump ,trg ,@locs)]))

  ;; imp-cmf-lang-v8.Value -> (listof asm-alloc-lang-v8.Effect) aloc
  (define (select-instructions-value e)
    (match e
      [`(mref ,loc ,opand) (assign-tmp e)]
      [`(alloc ,opand) (assign-tmp e)]
      [`(,binop ,triv1 ,triv2) (assign-tmp e)]
      [triv (values '() triv)]))

  ;; imp-cmf-lang-v8.Effect -> asm-alloc-lang-v8.Effect
  (define (select-instructions-effect e)
    (match e
      [`(set! ,aloc ,value)
       (let-values ([(is rhs) (select-instructions-value value)])
         `(begin ,@is (set! ,aloc ,rhs)))]
      [`(mset! ,loc ,opand ,triv) `(mset! ,loc ,opand ,triv)]
      [`(begin ,effects ...) `(begin ,@(map select-instructions-effect effects))]
      [`(if ,pred ,effect1 ,effect2)
       `(if ,(select-instructions-pred pred)
            ,(select-instructions-effect effect1)
            ,(select-instructions-effect effect2))]
      [`(return-point ,label ,tail)
       `(return-point ,label ,(select-instructions-tail tail))]))

  ;; imp-cmf-lang-v8.Pred -> asm-alloc-lang-v8.Pred
  (define (select-instructions-pred e)
    (match e
      [`(true) `(true)]
      [`(false) `(false)]
      [`(not ,pred) `(not ,(select-instructions-pred pred))]
      [`(begin ,effects ... ,pred)
       `(begin ,@(map select-instructions-effect effects) ,(select-instructions-pred pred))]
      [`(if ,pred ,pred1 ,pred2)
       `(if ,(select-instructions-pred pred)
            ,(select-instructions-pred pred1)
            ,(select-instructions-pred pred2))]
      [`(,relop ,opand_1 ,opand_2)
       (let ([tmp (fresh)])
         `(begin (set! ,tmp ,opand_1) (,relop ,tmp ,opand_2)))]))

  (match p
    [`(module ,info ,defs ... ,tail)
     `(module ,info ,@(map select-instructions-def defs) ,(select-instructions-tail tail))]))

(module+ tests
  (check-equal? 
    (select-instructions
    '(module
          ((new-frames ()))
        (define L.swap.1
          ((new-frames (())))
          (begin
            (set! tmp-ra.1 r15)
            (begin
              (set! x.1 rdi)
              (set! y.2 rsi)
              (if (< y.2 x.1)
                  (begin (set! rax x.1) (jump tmp-ra.1 rbp rax))
                  (begin
                    (begin
                      (return-point L.rp.4
                                    (begin
                                      (set! rsi x.1)
                                      (set! rdi y.2)
                                      (set! r15 L.rp.4)
                                      (jump L.swap.1 rbp r15 rdi rsi)))
                      (set! z.3 rax))
                    (begin (set! rax z.3) (jump tmp-ra.1 rbp rax)))))))
        (begin
          (set! tmp-ra.2 r15)
          (begin
            (set! rsi 2)
            (set! rdi 1)
            (set! r15 tmp-ra.2)
            (jump L.swap.1 rbp r15 rdi rsi)))))
    '(module
        ((new-frames ()))
      (define L.swap.1
        ((new-frames (())))
        (begin
          (set! tmp-ra.1 r15)
          (set! x.1 rdi)
          (set! y.2 rsi)
          (if (< y.2 x.1)
              (begin (set! rax x.1) (jump tmp-ra.1 rbp rax))
              (begin
                (return-point L.rp.4
                              (begin
                                (set! rsi x.1)
                                (set! rdi y.2)
                                (set! r15 L.rp.4)
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
)