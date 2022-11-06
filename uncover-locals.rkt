#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide uncover-locals)

(define (my-flatten lst)
  (foldr append '() lst))

;; Compiles Asm-pred-lang-v8 to Asm-pred-lang-v8/locals,
;; analysing which abstract locations are used in each block,
;; and each block and the module with the set of variables in an info? fields.
;;
;; Asm-pred-lang-v8 -> Asm-pred-lang-v8/locals
(define (uncover-locals p)

  ;; Asm-pred-lang-v8.Def -> Asm-pred-lang-v8/locals.Def
  (define (uncover-locals-def e)
    (match e
      [`(define ,label ,info ,tail)
       (let ([locals (sort (set->list (uncover-locals-tail tail '())) symbol<?)]
             [frame-vars (my-flatten (info-ref info `new-frames))])
         `(define
            ,label
            ,(info-set info `locals (set-union locals frame-vars))
            ,tail))]))

  ;; Asm-pred-lang-v8.Tail (setof aloc) -> (setof aloc)
  (define (uncover-locals-tail tail acc)
    (match tail
      [`(begin ,effects ... ,tail)
       (uncover-locals-tail tail (uncover-locals-effect--loe effects acc))]
      [`(if ,pred ,tail1 ,tail2)
       (uncover-locals-tail tail2 (uncover-locals-tail tail1 (uncover-locals-pred pred acc)))]
      [`(jump ,trg ,locs ...) (extend-locals trg acc)]))

  ;; Asm-pred-lang-v8.Effect (setof aloc) -> (setof aloc)
  (define (uncover-locals-effect e acc)
    (match e
      [`(set! ,loc (mref ,loc ,index))
       (extend-locals index (extend-locals loc acc))]
      [`(set! ,loc (,binop ,loc ,opand))
       (extend-locals opand (extend-locals loc acc))]
      [`(set! ,loc ,triv)
       (extend-locals triv (extend-locals loc acc))]
      [`(mset! ,loc ,index ,triv)
       (extend-locals triv (extend-locals index (extend-locals loc acc)))]
      [`(begin ,effects ...) (uncover-locals-effect--loe effects acc)]
      [`(if ,pred ,effect1 ,effect2)
       (uncover-locals-effect--loe (list effect1 effect2) (uncover-locals-pred pred acc))]
      [`(return-point ,label ,tail)
       (uncover-locals-tail tail acc)]))

  ;; (listof Asm-pred-lang-v8.Effect) (setof aloc) -> (setof aloc)
  (define (uncover-locals-effect--loe loe acc)
    (for/fold ([acc acc])
              ([e loe])
      (uncover-locals-effect e acc)))

  ;; Asm-pred-lang-v8.Pred (setof aloc) -> (setof aloc)
  (define (uncover-locals-pred e acc)
    (match e
      [`(true) acc]
      [`(false) acc]
      [`(not ,pred) (uncover-locals-pred pred acc)]
      [`(begin ,effects ... ,pred)
       (uncover-locals-pred pred (uncover-locals-effect--loe effects acc))]
      [`(if ,pred ,pred1 ,pred2)
       (uncover-locals-pred pred2 (uncover-locals-pred pred1 (uncover-locals-pred pred acc)))]
      [`(,relop ,loc ,opand)
       (extend-locals opand (extend-locals loc acc))]))

  ;; Asm-pred-lang-v8.Triv or Trg or Opand or Index (setof aloc) -> (setof aloc)
  (define (extend-locals e acc)
    (cond
      [(aloc? e) (set-add acc e)]
      [else acc]))

  (match p
    [`(module ,info ,defs ... ,tail)
     (let ([locals (sort (set->list (uncover-locals-tail tail '())) symbol<?)]
           [frame-vars (my-flatten (info-ref info `new-frames))])
       `(module
            ,(info-set info `locals (set-union locals frame-vars))
          ,@(map uncover-locals-def defs)
          ,tail))]))

(module+ tests
  (check-equal?
    (uncover-locals
    '(module ((new-frames ())) (begin (set! x.1 5) (begin (set! rax x.1) (jump r15)))))
    '(module
        ((new-frames ()) (locals (x.1)))
      (begin (set! x.1 5) (begin (set! rax x.1) (jump r15)))))

  (check-equal?
    (uncover-locals
    '(module ((new-frames ()))
        (begin
          (set! x.1 1)
          (set! y.1 x.1)
          (set! y.1 (+ y.1 1))
          (set! z.1 y.1)
          (set! z.1 (+ z.1 1))
          (begin (set! rax z.1) (jump r15)))))
    '(module
        ((new-frames ()) (locals (x.1 y.1 z.1)))
      (begin
        (set! x.1 1)
        (set! y.1 x.1)
        (set! y.1 (+ y.1 1))
        (set! z.1 y.1)
        (set! z.1 (+ z.1 1))
        (begin (set! rax z.1) (jump r15)))))

  (check-equal?
    (uncover-locals
    '(module ((new-frames ()))
        (begin
          (set! x.1 0)
          (set! w.1 0)
          (set! y.1 x.1)
          (set! w.1 (+ w.1 x.1))
          (set! w.1 (+ w.1 y.1))
          (begin (set! rax w.1) (jump r15)))))
    '(module
        ((new-frames ()) (locals (w.1 x.1 y.1)))
      (begin
        (set! x.1 0)
        (set! w.1 0)
        (set! y.1 x.1)
        (set! w.1 (+ w.1 x.1))
        (set! w.1 (+ w.1 y.1))
        (begin (set! rax w.1) (jump r15)))))

  (check-equal?
    (uncover-locals
    '(module ((new-frames (())))
        (define L.id.14 ((new-frames ()))
          (begin (begin (set! tmp-ra.246 r15))
                (begin (begin (set! x.127 rdi))
                        (begin (begin (set! rax x.127))
                              (jump tmp-ra.246 rbp rax)))))
        (begin (begin (set! tmp-ra.245 r15))
              (begin (begin (return-point L.rp.28
                                          (begin (begin (set! rdi 5))
                                                  (begin (set! r15 L.rp.28))
                                                  (jump L.id.14 rbp r15 rdi)))
                            (begin (set! x.128 rax)))
                      (begin (begin (set! rdi x.128))
                            (begin (set! r15 tmp-ra.245))
                            (jump L.id.14 rbp r15 rdi))))))
    '(module
        ((new-frames (())) (locals (tmp-ra.245 x.128)))
      (define L.id.14
        ((new-frames ()) (locals (tmp-ra.246 x.127)))
        (begin
          (begin (set! tmp-ra.246 r15))
          (begin
            (begin (set! x.127 rdi))
            (begin (begin (set! rax x.127)) (jump tmp-ra.246 rbp rax)))))
      (begin
        (begin (set! tmp-ra.245 r15))
        (begin
          (begin
            (return-point L.rp.28
                          (begin
                            (begin (set! rdi 5))
                            (begin (set! r15 L.rp.28))
                            (jump L.id.14 rbp r15 rdi)))
            (begin (set! x.128 rax)))
          (begin
            (begin (set! rdi x.128))
            (begin (set! r15 tmp-ra.245))
            (jump L.id.14 rbp r15 rdi))))))

  (check-equal?
    (uncover-locals
    '(module
          ((new-frames ()))
        (define L.*.4
          ((new-frames ()))
          (begin
            (set! tmp-ra.37 r15)
            (set! tmp.4 rdi)
            (set! tmp.5 rsi)
            (if (begin
                  (if (begin
                        (begin
                          (set! tmp.28 tmp.5)
                          (set! tmp.28 (bitwise-and tmp.28 7)))
                        (= tmp.28 0))
                      (set! tmp.27 14)
                      (set! tmp.27 6))
                  (!= tmp.27 6))
                (if (begin
                      (if (begin
                            (begin
                              (set! tmp.30 tmp.4)
                              (set! tmp.30 (bitwise-and tmp.30 7)))
                            (= tmp.30 0))
                          (set! tmp.29 14)
                          (set! tmp.29 6))
                      (!= tmp.29 6))
                    (begin
                      (set! tmp.31 tmp.5)
                      (set! tmp.31 (arithmetic-shift-right tmp.31 3))
                      (set! rax tmp.4)
                      (set! rax (* rax tmp.31))
                      (jump tmp-ra.37 rbp rax))
                    (begin (set! rax 318) (jump tmp-ra.37 rbp rax)))
                (begin (set! rax 318) (jump tmp-ra.37 rbp rax)))))
        (define L.+.3
          ((new-frames ()))
          (begin
            (set! tmp-ra.38 r15)
            (set! tmp.6 rdi)
            (set! tmp.7 rsi)
            (if (begin
                  (if (begin
                        (begin
                          (set! tmp.33 tmp.7)
                          (set! tmp.33 (bitwise-and tmp.33 7)))
                        (= tmp.33 0))
                      (set! tmp.32 14)
                      (set! tmp.32 6))
                  (!= tmp.32 6))
                (if (begin
                      (if (begin
                            (begin
                              (set! tmp.35 tmp.6)
                              (set! tmp.35 (bitwise-and tmp.35 7)))
                            (= tmp.35 0))
                          (set! tmp.34 14)
                          (set! tmp.34 6))
                      (!= tmp.34 6))
                    (begin
                      (set! rax tmp.6)
                      (set! rax (+ rax tmp.7))
                      (jump tmp-ra.38 rbp rax))
                    (begin (set! rax 574) (jump tmp-ra.38 rbp rax)))
                (begin (set! rax 574) (jump tmp-ra.38 rbp rax)))))
        (define L.eq?.2
          ((new-frames ()))
          (begin
            (set! tmp-ra.39 r15)
            (set! tmp.18 rdi)
            (set! tmp.19 rsi)
            (if (= tmp.18 tmp.19)
                (begin (set! rax 14) (jump tmp-ra.39 rbp rax))
                (begin (set! rax 6) (jump tmp-ra.39 rbp rax)))))
        (define L.fact.1
          ((new-frames (() () ())))
          (begin
            (set! tmp-ra.40 r15)
            (set! x.1 rdi)
            (if (begin
                  (begin
                    (return-point L.rp.5
                                  (begin
                                    (set! rsi 0)
                                    (set! rdi x.1)
                                    (set! r15 L.rp.5)
                                    (jump L.eq?.2 rbp r15 rdi rsi)))
                    (set! tmp.36 rax))
                  (!= tmp.36 6))
                (begin (set! rax 8) (jump tmp-ra.40 rbp rax))
                (begin
                  (return-point L.rp.6
                                (begin
                                  (set! rsi -8)
                                  (set! rdi x.1)
                                  (set! r15 L.rp.6)
                                  (jump L.+.3 rbp r15 rdi rsi)))
                  (set! z.2 rax)
                  (return-point L.rp.7
                                (begin
                                  (set! rdi z.2)
                                  (set! r15 L.rp.7)
                                  (jump L.fact.1 rbp r15 rdi)))
                  (set! y.3 rax)
                  (set! rsi y.3)
                  (set! rdi x.1)
                  (set! r15 tmp-ra.40)
                  (jump L.*.4 rbp r15 rdi rsi)))))
        (begin
          (set! tmp-ra.41 r15)
          (set! rdi 80)
          (set! r15 tmp-ra.41)
          (jump L.fact.1 rbp r15 rdi))))
    '(module
        ((new-frames ()) (locals (tmp-ra.41)))
      (define L.*.4
        ((new-frames ())
          (locals (tmp-ra.37 tmp.27 tmp.28 tmp.29 tmp.30 tmp.31 tmp.4 tmp.5)))
        (begin
          (set! tmp-ra.37 r15)
          (set! tmp.4 rdi)
          (set! tmp.5 rsi)
          (if (begin
                (if (begin
                      (begin
                        (set! tmp.28 tmp.5)
                        (set! tmp.28 (bitwise-and tmp.28 7)))
                      (= tmp.28 0))
                    (set! tmp.27 14)
                    (set! tmp.27 6))
                (!= tmp.27 6))
              (if (begin
                    (if (begin
                          (begin
                            (set! tmp.30 tmp.4)
                            (set! tmp.30 (bitwise-and tmp.30 7)))
                          (= tmp.30 0))
                        (set! tmp.29 14)
                        (set! tmp.29 6))
                    (!= tmp.29 6))
                  (begin
                    (set! tmp.31 tmp.5)
                    (set! tmp.31 (arithmetic-shift-right tmp.31 3))
                    (set! rax tmp.4)
                    (set! rax (* rax tmp.31))
                    (jump tmp-ra.37 rbp rax))
                  (begin (set! rax 318) (jump tmp-ra.37 rbp rax)))
              (begin (set! rax 318) (jump tmp-ra.37 rbp rax)))))
      (define L.+.3
        ((new-frames ())
          (locals (tmp-ra.38 tmp.32 tmp.33 tmp.34 tmp.35 tmp.6 tmp.7)))
        (begin
          (set! tmp-ra.38 r15)
          (set! tmp.6 rdi)
          (set! tmp.7 rsi)
          (if (begin
                (if (begin
                      (begin
                        (set! tmp.33 tmp.7)
                        (set! tmp.33 (bitwise-and tmp.33 7)))
                      (= tmp.33 0))
                    (set! tmp.32 14)
                    (set! tmp.32 6))
                (!= tmp.32 6))
              (if (begin
                    (if (begin
                          (begin
                            (set! tmp.35 tmp.6)
                            (set! tmp.35 (bitwise-and tmp.35 7)))
                          (= tmp.35 0))
                        (set! tmp.34 14)
                        (set! tmp.34 6))
                    (!= tmp.34 6))
                  (begin
                    (set! rax tmp.6)
                    (set! rax (+ rax tmp.7))
                    (jump tmp-ra.38 rbp rax))
                  (begin (set! rax 574) (jump tmp-ra.38 rbp rax)))
              (begin (set! rax 574) (jump tmp-ra.38 rbp rax)))))
      (define L.eq?.2
        ((new-frames ()) (locals (tmp-ra.39 tmp.18 tmp.19)))
        (begin
          (set! tmp-ra.39 r15)
          (set! tmp.18 rdi)
          (set! tmp.19 rsi)
          (if (= tmp.18 tmp.19)
              (begin (set! rax 14) (jump tmp-ra.39 rbp rax))
              (begin (set! rax 6) (jump tmp-ra.39 rbp rax)))))
      (define L.fact.1
        ((new-frames (() () ())) (locals (tmp-ra.40 tmp.36 x.1 y.3 z.2)))
        (begin
          (set! tmp-ra.40 r15)
          (set! x.1 rdi)
          (if (begin
                (begin
                  (return-point L.rp.5
                                (begin
                                  (set! rsi 0)
                                  (set! rdi x.1)
                                  (set! r15 L.rp.5)
                                  (jump L.eq?.2 rbp r15 rdi rsi)))
                  (set! tmp.36 rax))
                (!= tmp.36 6))
              (begin (set! rax 8) (jump tmp-ra.40 rbp rax))
              (begin
                (return-point L.rp.6
                              (begin
                                (set! rsi -8)
                                (set! rdi x.1)
                                (set! r15 L.rp.6)
                                (jump L.+.3 rbp r15 rdi rsi)))
                (set! z.2 rax)
                (return-point L.rp.7
                              (begin
                                (set! rdi z.2)
                                (set! r15 L.rp.7)
                                (jump L.fact.1 rbp r15 rdi)))
                (set! y.3 rax)
                (set! rsi y.3)
                (set! rdi x.1)
                (set! r15 tmp-ra.40)
                (jump L.*.4 rbp r15 rdi rsi)))))
      (begin
        (set! tmp-ra.41 r15)
        (set! rdi 80)
        (set! r15 tmp-ra.41)
        (jump L.fact.1 rbp r15 rdi))))

  (check-equal?
    (uncover-locals
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
    '(module
        ((new-frames ()) (locals (tmp-ra.3 tmp.1 tmp.2)))
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
    (uncover-locals
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
    '(module
        ((new-frames ()) (locals (tmp-ra.3 tmp.1 tmp.2)))
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
    (uncover-locals
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
    '(module
        ((new-frames ()) (locals (tmp-ra.3 tmp.1 tmp.2 tmp.3)))
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