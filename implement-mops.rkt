#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide implement-mops)

;; Compiles mops to instructions on pointers with index- and displacement-mode operands.
;;
;; paren-x64-mops-v8 -> paren-x64-v8
(define (implement-mops p)

  ;; paren-x64-mops-v8.s -> paren-x64-v8.s
  (define (implement-mops-s s)
    (match s
      [`(set! ,reg_1 (mref ,reg_2 ,index)) `(set! ,reg_1 (,reg_2 + ,index))]
      [`(mset! ,reg_1 ,index ,int32)
        #:when (int32? int32)
        `(set! (,reg_1 + ,index) ,int32)]
      [`(mset! ,reg_1 ,index ,trg) `(set! (,reg_1 + ,index) ,trg)]
      [`(with-label ,label ,s) `(with-label ,label ,(implement-mops-s s))]
      [_ s]))

  (match p
    [`(begin ,s ...) `(begin ,@(map implement-mops-s s))]))

(module+ tests
  (check-equal?
  (implement-mops
    '(begin
      (set! r12 (mref r8 r11))
      (mset! r8 r9 5)
      (mset! r8 r9 r11)
      (mset! r8 r9 L.start.1)
      (mset! r8 8 r11)
      (mset! r8 -7 r11)))
  '(begin
      (set! r12 (r8 + r11))
      (set! (r8 + r9) 5)
      (set! (r8 + r9) r11)
      (set! (r8 + r9) L.start.1)
      (set! (r8 + 8) r11)
      (set! (r8 + -7) r11)))
)