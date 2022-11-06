#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide expose-basic-blocks)

;; Compiles the given nested-asm-lang-v8 program to block-pred-lang-v8 by
;; eliminating all nested expressions by generating fresh basic blocks and jumps.
;;
;; Nested-asm-lang-v8 -> Block-pred-lang-v8
(define (expose-basic-blocks p)
  (define blocks (box `()))

  ;; Nested-asm-lang-v8.Label Nested-asm-lang-v8.Tail -> (void)
  (define (add-block! label tail)
    (set-box! blocks `(,@(unbox blocks) (define ,label ,tail))))

  ;; Any -> Boolean
  (define (addr? e)
    (match e
      [`(,fbp - ,dispoffset) (and (frame-base-pointer-register? fbp) (dispoffset? dispoffset))]
      [_ #f]))

  ;; Any -> Boolean
  (define (triv? e)
    (or (int64? e) (register? e) (addr? e) (label? e)))

  ;; Nested-asm-lang-v8.Pred Nested-asm-lang-v8.Tail Nested-asm-lang-v8.Tail -> Block-pred-lang-v8.Tail
  (define (expose-basic-blocks-pred p k-true k-false)
    (match p
      [`(begin ,effects ... ,pred)
       (expose-basic-blocks-effects effects (expose-basic-blocks-pred pred k-true k-false))]
      [`(if ,pred ,pred1 ,pred2)
       (let* ([pred1-label (fresh-label)]
              [pred2-label (fresh-label)])
         (add-block! pred2-label (expose-basic-blocks-pred pred2 k-true k-false))
         (add-block! pred1-label (expose-basic-blocks-pred pred1 k-true k-false))
         (expose-basic-blocks-pred pred pred1-label pred2-label))]
      [`(not ,pred)
       (expose-basic-blocks-pred pred k-false k-true)]
      [_
       `(if ,p
            (jump ,k-true)
            (jump ,k-false))]))

  ;; Nested-asm-lang-v8.Effect Nested-asm-lang-v8.Tail -> Block-pred-lang-v8.Tail
  (define (expose-basic-blocks-effect e tail)
    (match e
      [`(set! ,loc1 (mref ,loc2 ,index)) (merge-tail-effect e tail)]
      [`(set! ,loc (,binop ,loc ,triv)) (merge-tail-effect e tail)]
      [`(set! ,loc ,triv) (merge-tail-effect e tail)]
      [`(mset! ,loc ,index ,triv) (merge-tail-effect e tail)]
      [`(begin ,effects ...)
       (expose-basic-blocks-effects effects tail)]
      [`(if ,pred ,effect1 ,effect2)
       (let* ([join-label (fresh-label `join)]
              [effect2-label (fresh-label)]
              [effect1-label (fresh-label)]
              [effect2-label (fresh-label)])
         (add-block! join-label (expose-basic-blocks-tail tail))
         (add-block! effect1-label (expose-basic-blocks-effect effect1 `(jump ,join-label)))
         (add-block! effect2-label (expose-basic-blocks-effect effect2 `(jump ,join-label)))
         (expose-basic-blocks-pred pred effect1-label effect2-label))]
      [`(return-point ,label ,tail1)
       (add-block! label (expose-basic-blocks-tail tail))
       (expose-basic-blocks-tail tail1)]))

  ;; (listof Nested-asm-lang-v8.Effect) Nested-asm-lang-v8.Tail -> Block-pred-lang-v8.Tail
  (define (expose-basic-blocks-effects es tail)
    (cond
      [(empty? es) tail]
      [else
       (for/fold ([tail tail])
                 ([effect (reverse es)])
         (expose-basic-blocks-effect effect tail))]))

  ;; Nested-asm-lang-v8.Tail -> Block-pred-lang-v8.Tail
  (define (expose-basic-blocks-tail e)
    (match e
      [`(jump ,trg) `(jump ,trg)]
      [`(begin ,effects ... ,tail) (expose-basic-blocks-effects effects (expose-basic-blocks-tail tail))]
      [`(if ,pred ,tail1 ,tail2)
       (let* ([tail1-label (fresh-label)]
              [tail2-label (fresh-label)])
         (add-block! tail2-label (expose-basic-blocks-tail tail2))
         (add-block! tail1-label (expose-basic-blocks-tail tail1))
         (expose-basic-blocks-pred pred tail1-label tail2-label))]))

  ;; Nested-asm-lang-v8.Definition -> Block-pred-lang-v8.Block
  (define (expose-basic-blocks-definition def)
    (match def
      [`(define ,label ,tail) (add-block! label (expose-basic-blocks-tail tail))]))

  ;; block-pred-lang-v8.Effect block-pred-lang-v8.Tail -> block-pred-lang-v8.Tail
  (define (merge-tail-effect effect tail)
    (match tail
      [`(begin ,effects ... ,tail^) `(begin ,effect ,@effects ,tail^)]
      [_ `(begin ,effect ,tail)]))

  (match p
    [`(module ,defs ... ,tail)
     (map expose-basic-blocks-definition defs)
     `(module (define ,(fresh-label `__main) ,(expose-basic-blocks-tail tail)) ,@(unbox blocks))]))


(module+ tests
  (check-equal? (expose-basic-blocks '(module (begin (set! r15 r15) (set! rax 5) (jump r15))))
                '(module (define L.__main.1 (begin (set! r15 r15) (set! rax 5) (jump r15)))))

  (check-equal? (expose-basic-blocks
                  '(module (begin (set! r15 r15)
                                  (set! r8 4)
                                  (set! r9 5)
                                  (if (< r8 r9)
                                      (set! rax 5)
                                      (set! rax 10))
                                  (jump r15))))
                '(module
                      (define L.__main.2
                        (begin
                          (set! r15 r15)
                          (set! r8 4)
                          (set! r9 5)
                          (if (< r8 r9) (jump L.tmp.5) (jump L.tmp.6))))
                    (define L.join.3 (jump r15))
                    (define L.tmp.5 (begin (set! rax 5) (jump L.join.3)))
                    (define L.tmp.6 (begin (set! rax 10) (jump L.join.3)))))

  (check-equal? (expose-basic-blocks
                  '(module
                      (define L.add.1
                        (begin
                          (set! r15 r15)
                          (set! r14 (rbp - 0))
                          (set! r13 (rbp - 8))
                          (set! rax r14)
                          (set! rax (+ rax r13))
                          (jump r15)))
                    (begin
                      (set! r15 r15)
                      (set! r14 4)
                      (set! r13 5)
                      (set! (rbp - 8) r13)
                      (set! (rbp - 0) r14)
                      (set! r15 r15)
                      (jump L.add.1))))
                '(module
                      (define L.__main.7
                        (begin
                          (set! r15 r15)
                          (set! r14 4)
                          (set! r13 5)
                          (set! (rbp - 8) r13)
                          (set! (rbp - 0) r14)
                          (set! r15 r15)
                          (jump L.add.1)))
                    (define L.add.1
                      (begin
                        (set! r15 r15)
                        (set! r14 (rbp - 0))
                        (set! r13 (rbp - 8))
                        (set! rax r14)
                        (set! rax (+ rax r13))
                        (jump r15)))))

  (check-equal? (expose-basic-blocks
                  '(module
                      (define L.add.1
                        (begin
                          (set! r15 r15)
                          (set! r14 (rbp - 0))
                          (set! r13 (rbp - 8))
                          (set! rax r14)
                          (set! rax (+ rax r13))
                          (jump r15)))
                    (begin
                      (set! (rbp - 0) r15)
                      (set! (rbp - 8) 4)
                      (set! r15 5)
                      (begin
                        (set! rbp (- rbp 16))
                        (return-point L.rp.1
                                      (begin
                                        (set! (rbp - 8) r15)
                                        (set! (rbp - 0) (rbp - -8))
                                        (set! r15 L.rp.1)
                                        (jump L.add.1)))
                        (set! rbp (+ rbp 16)))
                      (set! r15 rax)
                      (set! rax r15)
                      (set! rax (+ rax (rbp - 8)))
                      (jump (rbp - 0)))))
                '(module
                      (define L.__main.8
                        (begin
                          (set! (rbp - 0) r15)
                          (set! (rbp - 8) 4)
                          (set! r15 5)
                          (set! rbp (- rbp 16))
                          (set! (rbp - 8) r15)
                          (set! (rbp - 0) (rbp - -8))
                          (set! r15 L.rp.1)
                          (jump L.add.1)))
                    (define L.add.1
                      (begin
                        (set! r15 r15)
                        (set! r14 (rbp - 0))
                        (set! r13 (rbp - 8))
                        (set! rax r14)
                        (set! rax (+ rax r13))
                        (jump r15)))
                    (define L.rp.1
                      (begin
                        (set! rbp (+ rbp 16))
                        (set! r15 rax)
                        (set! rax r15)
                        (set! rax (+ rax (rbp - 8)))
                        (jump (rbp - 0))))))

  (check-equal? (expose-basic-blocks
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
                '(module
                      (define L.__main.11
                        (begin
                          (set! r15 r15)
                          (set! (rbp - 8) 2)
                          (set! (rbp - 0) 1)
                          (set! r15 r15)
                          (jump L.swap.1)))
                    (define L.rp.1
                      (begin
                        (set! rbp (+ rbp 24))
                        (set! r15 rax)
                        (set! rax r15)
                        (jump (rbp - 16))))
                    (define L.tmp.10
                      (begin
                        (set! rbp (- rbp 24))
                        (set! (rbp - 8) r14)
                        (set! (rbp - 0) r15)
                        (set! r15 L.rp.1)
                        (jump L.swap.1)))
                    (define L.tmp.9 (begin (set! rax r14) (jump (rbp - 16))))
                    (define L.swap.1
                      (begin
                        (set! (rbp - 16) r15)
                        (set! r14 (rbp - 0))
                        (set! r15 (rbp - 8))
                        (if (< r15 r14) (jump L.tmp.9) (jump L.tmp.10))))))
)