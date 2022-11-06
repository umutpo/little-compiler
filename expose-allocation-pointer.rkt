#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide expose-allocation-pointer)

;; Implements the allocation primitive in terms of
;; pointer arithmetic on the current-heap-base-pointer-register
;;
;; Asm-alloc-lang-v8 -> Asm-pred-lang-v8
(define (expose-allocation-pointer p)

  ;; Asm-alloc-lang-v8.Def -> Asm-pred-lang-v8.Def
  (define (expose-allocation-pointer-def e)
    (match e
      [`(define ,label ,info ,tail)
       `(define ,label ,info ,(expose-allocation-pointer-tail tail))]))

  ;; Asm-alloc-lang-v8.Pred -> Asm-pred-lang-v8.Pred
  (define (expose-allocation-pointer-pred e)
    (match e
      [`(true) `(true)]
      [`(false) `(false)]
      [`(not ,pred) `(not ,(expose-allocation-pointer-pred pred))]
      [`(begin ,effects ... ,pred)
       `(begin ,@(map expose-allocation-pointer-effect effects)
               ,(expose-allocation-pointer-pred pred))]
      [`(if ,pred ,pred1 ,pred2)
       `(if ,(expose-allocation-pointer-pred pred)
            ,(expose-allocation-pointer-pred pred1)
            ,(expose-allocation-pointer-pred pred2))]
      [`(,relop ,opand1 ,opand2) `(,relop ,opand1 ,opand2)]))

  ;; Asm-alloc-lang-v8.Tail -> Asm-pred-lang-v8.Tail
  (define (expose-allocation-pointer-tail e)
    (match e
      [`(jump ,trg ,locs ...) `(jump ,trg ,@locs)]
      [`(begin ,effects ... ,tail)
       `(begin ,@(map expose-allocation-pointer-effect effects)
               ,(expose-allocation-pointer-tail tail))]
      [`(if ,pred ,tail1 ,tail2)
       `(if ,(expose-allocation-pointer-pred pred)
            ,(expose-allocation-pointer-tail tail1)
            ,(expose-allocation-pointer-tail tail2))]))

  ;; Asm-alloc-lang-v8.Effect -> Asm-pred-lang-v8.Effect
  (define (expose-allocation-pointer-effect e)
    (match e
      [`(set! ,loc1 (mref ,loc2 ,index)) e]
      [`(set! ,loc (alloc ,index))
       `(begin
          (set! ,loc ,(current-heap-base-pointer-register))
          (set! ,(current-heap-base-pointer-register) (+ ,(current-heap-base-pointer-register) ,index)))]
      [`(set! ,loc (,binop ,loc ,opand)) e]
      [`(set! ,loc ,triv) e]
      [`(mset! ,loc ,index ,triv) e]
      [`(begin ,effects ...)
       `(begin ,@(map expose-allocation-pointer-effect effects))]
      [`(if ,pred ,effect1 ,effect2)
       `(if ,(expose-allocation-pointer-pred pred)
            ,(expose-allocation-pointer-effect effect1)
            ,(expose-allocation-pointer-effect effect2))]
      [`(return-point ,label ,tail)
       `(return-point ,label ,(expose-allocation-pointer-tail tail))]))

  (match p
    [`(module ,info ,defs ... ,tail)
     `(module
          ,info
        ,@(map expose-allocation-pointer-def defs)
        ,(expose-allocation-pointer-tail tail))]))

(module+ tests
  (check-equal?
    (expose-allocation-pointer
    '(module
          ((new-frames ()))
        (begin
          (set! tmp-ra.3 r15)
          (set! tmp.2 (alloc 16))
          (set! tmp.2 (+ tmp.2 1))
          (mset! tmp.2 -1 40)
          (mset! tmp.2 7 48)
          (set! tmp.1 tmp.2)
          (set! rax (mref tmp.1 -1))
          (jump tmp-ra.3 rbp rax))))
    '(module
        ((new-frames ()))
      (begin
        (set! tmp-ra.3 r15)
        (begin (set! tmp.2 r12) (set! r12 (+ r12 16)))
        (set! tmp.2 (+ tmp.2 1))
        (mset! tmp.2 -1 40)
        (mset! tmp.2 7 48)
        (set! tmp.1 tmp.2)
        (set! rax (mref tmp.1 -1))
        (jump tmp-ra.3 rbp rax))))

  (check-equal?
    (expose-allocation-pointer
    '(module
          ((new-frames ()))
        (begin
          (set! tmp-ra.2 r15)
          (set! tmp.1 (alloc 16))
          (set! tmp.1 (+ tmp.1 1))
          (mset! tmp.1 -1 40)
          (mset! tmp.1 7 48)
          (set! rax tmp.1)
          (jump tmp-ra.2 rbp rax))))
    '(module
        ((new-frames ()))
      (begin
        (set! tmp-ra.2 r15)
        (begin (set! tmp.1 r12) (set! r12 (+ r12 16)))
        (set! tmp.1 (+ tmp.1 1))
        (mset! tmp.1 -1 40)
        (mset! tmp.1 7 48)
        (set! rax tmp.1)
        (jump tmp-ra.2 rbp rax))))

  (check-equal?
    (expose-allocation-pointer
    '(module
          ((new-frames ()))
        (begin
          (set! tmp-ra.3 r15)
          (set! tmp.2 (alloc 32))
          (set! tmp.3 tmp.2)
          (set! tmp.3 (+ tmp.3 3))
          (mset! tmp.3 -3 24)
          (set! tmp.1 tmp.3)
          (set! rax (mref tmp.1 53))
          (jump tmp-ra.3 rbp rax))))
    '(module
        ((new-frames ()))
      (begin
        (set! tmp-ra.3 r15)
        (begin (set! tmp.2 r12) (set! r12 (+ r12 32)))
        (set! tmp.3 tmp.2)
        (set! tmp.3 (+ tmp.3 3))
        (mset! tmp.3 -3 24)
        (set! tmp.1 tmp.3)
        (set! rax (mref tmp.1 53))
        (jump tmp-ra.3 rbp rax))))
)