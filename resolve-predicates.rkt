#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide resolve-predicates)

;; Compiles the given block-pred-lang-v4? program to block-asm-lang-v4
;; by compiling predicates to (relop loc opand) or eliminating them
;;
;; block-pred-lang-v4 -> block-asm-lang-v4
(define (resolve-predicates p)

  ;; block-pred-lang-v4.b -> block-asm-lang-v4.b
  (define (resolve-predicates-b e)
    (match e
      [`(define ,label ,tail) `(define ,label ,(resolve-predicates-tail tail))]))

  ;; block-pred-lang-v4.tail -> block-asm-lang-v4.tail
  (define (resolve-predicates-tail e)
    (match e
      [`(if ,pred (jump ,trg1) (jump ,trg2))
       (resolve-predicates-pred pred trg1 trg2)]
      [`(begin ,effects ... ,tail) `(begin ,@effects ,(resolve-predicates-tail tail))]
      [`(jump ,trg) `(jump ,trg)]))

  ;; block-pred-lang-v4.pred -> block-asm-lang-v4.tail
  (define (resolve-predicates-pred e trg1 trg2)
    (match e
      [`(true) `(jump ,trg1)]
      [`(false) `(jump ,trg2)]
      [`(not ,pred) (resolve-predicates-pred pred trg2 trg1)]
      [`(,relop ,loc ,opand) `(if ,e (jump ,trg1) (jump ,trg2))]))

  (match p
    [`(module ,bs ...) `(module ,@(map resolve-predicates-b bs))]))

(module+ tests
  (check-equal?
    (resolve-predicates '(module
                            (define L.main.1 (begin (set! rbx 1) (set! rcx 2) (if (false) (jump L.t.1) (jump L.t.2))))
                          (define L.t.1 (begin (set! rdx 4) (halt rdx)))
                          (define L.t.2 (begin (set! rdx 8) (halt rdx)))))

    '(module
        (define L.main.1 (begin (set! rbx 1) (set! rcx 2) (jump L.t.2)))
      (define L.t.1 (begin (set! rdx 4) (halt rdx)))
      (define L.t.2 (begin (set! rdx 8) (halt rdx)))))

  (check-equal?
    (resolve-predicates '(module
                            (define L.start.1 (if (not (not (false))) (jump L.start.2) (jump L.start.3)))
                          (define L.start.2 (halt 0))
                          (define L.start.3 (halt 120))))
    '(module
        (define L.start.1 (jump L.start.3))
      (define L.start.2 (halt 0))
      (define L.start.3 (halt 120))))
)