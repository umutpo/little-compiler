#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide implement-fvars)

;; Reifies fvars into displacement mode operands.
;;
;; nested-asm-lang-fvars-v8 -> nested-asm-lang-v8
(define (implement-fvars p)
  (define (binop? e)
    (and (member e '(* + - bitwise-and bitwise-ior bitwise-xor arithmetic-shift-right)) #t))

  (define offset 0)

  ;; (Source triv) -> (Target triv)
  (define (replace-fvar loc)
    (if (fvar? loc)
        `(,(current-frame-base-pointer-register) - ,(- (* (fvar->index loc) (current-word-size-bytes)) offset))
        loc))

  ;; binop Number -> void
  (define (update-offset! sign num)
    (match sign
      [`- (set! offset (+ offset num))]
      [`+ (set! offset (- offset num))]))

  ;; (Source Pred) -> (Target Pred)
  (define (implement-fvars-pred e)
    (match e
      [`(true) `(true)]
      [`(false) `(false)]
      [`(not ,pred) `(not ,(implement-fvars-pred pred))]
      [`(begin ,effects ... ,pred)
       `(begin ,@(map (lambda (e) (implement-fvars-effect e)) effects)
               ,(implement-fvars-pred pred))]
      [`(if ,pred ,pred1 ,pred2)
       `(if ,(implement-fvars-pred pred)
            ,(implement-fvars-pred pred1)
            ,(implement-fvars-pred pred2))]
      [`(,relop ,loc ,triv) `(,relop ,(replace-fvar loc) ,(replace-fvar triv))]))

  ;; (Source Effect) -> (Target Effect)
  (define (implement-fvars-effect e)
    (match e
      [`(set! ,loc_1 (mref ,loc_2 ,index))
          `(set! ,(replace-fvar loc_1)
              (mref ,(replace-fvar loc_2) ,(replace-fvar index)))]
      [`(set! ,loc (,binop ,loc ,triv))
       #:when (binop? binop)
       (when (eq? (current-frame-base-pointer-register) loc)
         (update-offset! binop triv))
       `(set! ,(replace-fvar loc)
              (,binop ,(replace-fvar loc) ,(replace-fvar triv)))]
      [`(set! ,loc ,triv)
       `(set! ,(replace-fvar loc) ,(replace-fvar triv))]
      [`(mset! ,loc ,index ,triv)
        `(mset! ,(replace-fvar loc) ,(replace-fvar index) ,(replace-fvar triv))]
      [`(begin ,effects ... ,effect)
       `(begin ,@(map implement-fvars-effect effects)
               ,(implement-fvars-effect effect))]
      [`(if ,pred ,effect1 ,effect2)
       `(if ,(implement-fvars-pred pred)
            ,(implement-fvars-effect effect1)
            ,(implement-fvars-effect effect2))]
      [`(return-point ,label ,tail)
       `(return-point ,label ,(implement-fvars-tail tail))]))

  ;; (Source Tail) -> (Target Tail)
  (define (implement-fvars-tail e)
    (match e
      [`(jump ,trg) `(jump ,(replace-fvar trg))]
      [`(begin ,effects ... ,tail)
       `(begin ,@(map (lambda (e) (implement-fvars-effect e)) effects)
               ,(implement-fvars-tail tail))]
      [`(if ,pred ,tail1 ,tail2)
       `(if ,(implement-fvars-pred pred)
            ,(implement-fvars-tail tail1)
            ,(implement-fvars-tail tail2))]))

  ;; (Source Definition) -> (Target Definition)
  (define (implement-fvars-definition def)
    (match def
      [`(define ,label ,tail)
       (set! offset 0)
       `(define ,label ,(implement-fvars-tail tail))]))

  (match p
    [`(module ,defs ... ,tail)
     `(module ,@(map implement-fvars-definition defs)
        ,(implement-fvars-tail tail))]))

(module+ tests
  (check-equal?
    (implement-fvars '(module
                          (define L.swap.1
                            (begin
                              (set! fv2 r15)
                              (set! r14 fv0)
                              (set! r15 fv1)
                              (if (< r15 r14)
                                  (begin (set! rax r14) (jump fv2))
                                  (begin
                                    (begin
                                      (set! rbp (- rbp 24))
                                      (return-point L.rp.1
                                                    (begin
                                                      (set! fv4 r14)
                                                      (set! fv3 r15)
                                                      (set! r15 L.rp.1)
                                                      (jump L.swap.1)))
                                      (set! rbp (+ rbp 24)))
                                    (set! r15 rax)
                                    (set! rax r15)
                                    (jump fv2)))))
                        (begin
                          (set! r15 r15)
                          (set! fv1 2)
                          (set! fv0 1)
                          (set! r15 r15)
                          (jump L.swap.1))))

    '(module
          (define L.swap.1
            (begin
              (set! (rbp - 16) r15)
              (set! r14 (rbp - 0))
              (set! r15 (rbp - 8))
              (if (< r15 r14)
                  (begin (set! rax r14) (jump (rbp - 16)))
                  (begin
                    (begin
                      (set! rbp (- rbp 24))
                      (return-point L.rp.1
                                    (begin
                                      (set! (rbp - 8) r14)
                                      (set! (rbp - 0) r15)
                                      (set! r15 L.rp.1)
                                      (jump L.swap.1)))
                      (set! rbp (+ rbp 24)))
                    (set! r15 rax)
                    (set! rax r15)
                    (jump (rbp - 16))))))
        (begin
          (set! r15 r15)
          (set! (rbp - 8) 2)
          (set! (rbp - 0) 1)
          (set! r15 r15)
          (jump L.swap.1))))
)