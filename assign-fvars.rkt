#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace)

(provide assign-fvars)

;; Compiles the given Asm-lang-v2/locals program to Asm-lang-v2/assignments
;; by specifying the assignment of each abstract location to a physical location
;; in the info field
;;
;; Asm-lang-v2/locals -> Asm-lang-v2/assignments
(define (assign-fvars p)
  (define (allocate-vars vars)
    (for/list ([var vars]
               [i (build-list (length vars) values)])
      `(,var ,(make-fvar i))))

  (match p
    [`(module ((locals ,vars)) ,tail)
     `(module ((locals ,vars) (assignment ,(allocate-vars vars))) ,tail)]))