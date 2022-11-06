#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace)

(provide flatten-begins)

;; Compiles the given Nested-asm-lang-v2 program to a Para-asm-lang-v2
;; by flattening/appending the nested instructions
;;
;; Nested-asm-lang-v2 -> Para-asm-lang-v2
(define (flatten-begins p)
  (define (program->para-asm-lang-v2 p)
    (let ([instructions (tail->para-asm-lang-v2 p)])
      `(begin ,@instructions)))

  (define (tail->para-asm-lang-v2 tail)
    (match tail
      [`(begin ,effect ...)
       (foldl (lambda (e list) (append list (tail->para-asm-lang-v2 e))) empty effect)]
      [_ (list tail)]))

  (program->para-asm-lang-v2 p))