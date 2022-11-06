#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide flatten-program)

(define (my-flatten lst)
  (foldr append '() lst))

;; Compiles the given block-asm-lang-v7 program to para-asm-lang-v7 by
;; flattening basic blocks into labeled instructions.
;;
;; Block-asm-lang-v7 -> Para-asm-lang-v7
(define (flatten-program p)

  ;; Block-asm-lang-v7.Tail -> (listof Para-asm-lang-v7.Statement)
  (define (flatten-program-tail t)
    (match t
      [`(jump ,trg) `((jump ,trg))]
      [`(begin ,effects ... ,tail)
       `(,@effects ,@(flatten-program-tail tail))]
      [`(if (,relop ,loc ,opand) (jump ,trg1) (jump ,trg2))
       `((compare ,loc ,opand)
         (jump-if ,relop ,trg1)
         (jump ,trg2))]))

  ;; Block-asm-lang-v7.Block -> (listof Para-asm-lang-v7.Statement)
  (define (flatten-program-block b)
    (match b
      [`(define ,label ,tail)
       (let ([flattened-tail (flatten-program-tail tail)])
         `((with-label ,label ,(first flattened-tail)) ,@(rest flattened-tail)))]))

  (match p
    [`(module ,bs ... ,b)
     `(begin ,@(my-flatten (map flatten-program-block bs)) ,@(flatten-program-block b))]))

(module+ tests
  (check-equal? (flatten-program
                  '(module
                      (define L.A.0
                        (begin (set! rbx 1)
                                (jump L.A.1)))
                    (define L.A.1
                      (begin (set! rax 1)
                              (jump L.A.2)))
                    (define L.A.2
                      (begin (set! rbx (+ rbx rax))
                              (if (= rbx 5)
                                  (jump L.done.0)
                                  (jump L.A.2))))))
                '(begin
                    (with-label L.A.0 (set! rbx 1))
                    (jump L.A.1)
                    (with-label L.A.1 (set! rax 1))
                    (jump L.A.2)
                    (with-label L.A.2 (set! rbx (+ rbx rax)))
                    (compare rbx 5)
                    (jump-if = L.done.0)
                    (jump L.A.2)))
)