#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide sequentialize-let)

;; Compiles Values-bits-lang-v8 to Imp-mf-lang-v8
;; by picking a particular order to implement let expressions using set!.
;;
;; Values-bits-lang-v8 -> Imp-mf-lang-v8
(define (sequentialize-let p)

  ;; Any -> Boolean
  (define (opand? e)
    (or (int64? e) (aloc? e)))

  ;; Any -> Boolean
  (define (triv? e)
    (or (opand? e) (label? e)))

  ;; (listof Values-bits-lang-v8.definition) -> (listof Imp-mf-lang-v8.definition)
  (define (sequentialize-let-defs defs)
    (for/list ([def defs])
      (match def
        [`(define ,name (lambda (,params ...) ,tail))
         `(define ,name (lambda (,@params) ,(sequentialize-let-tail tail)))])))

  ;; Values-bits-lang-v8.Pred -> Imp-mf-lang-v8.Pred
  (define (sequentialize-let-pred pred)
    (match pred
      [`(true) `(true)]
      [`(false) `(false)]
      [`(not ,pred) `(not ,(sequentialize-let-pred pred))]
      [`(let ([,alocs ,values] ...) ,pred)
       `(begin
          ,@(for/list ([aloc alocs]
                       [val values])
              `(set! ,aloc ,(sequentialize-let-value val)))
          ,(sequentialize-let-pred pred))]
      [`(if ,pred ,pred1 ,pred2)
       `(if ,(sequentialize-let-pred pred)
            ,(sequentialize-let-pred pred1)
            ,(sequentialize-let-pred pred2))]
      [`(begin ,effects ... ,pred)
       `(begin ,@(map sequentialize-let-effect effects) ,(sequentialize-let-pred pred))]
      [`(,relop ,opand1 ,opand2) pred]))

  ;; Values-bits-lang-v8.Effect -> Imp-mf-lang-v8.Effect
  (define (sequentialize-let-effect e)
    (match e
      [`(mset! ,aloc ,opand ,value)
       `(mset! ,aloc ,opand ,(sequentialize-let-value value))]
      [`(let ([,alocs ,values] ...) ,effect)
       `(begin
          ,@(for/list ([aloc alocs]
                       [val values])
              `(set! ,aloc ,(sequentialize-let-value val)))
          ,(sequentialize-let-effect effect))]
      [`(begin ,effects ... ,effect)
       `(begin ,@(map sequentialize-let-effect (cons effect effects)))]))

  ;; Values-bits-lang-v8.Tail -> Imp-mf-lang-v8.Tail
  (define (sequentialize-let-tail tail)
    (match tail
      [`(let ([,alocs ,values] ...) ,tail)
       `(begin
          ,@(for/list ([aloc alocs]
                       [val values])
              `(set! ,aloc ,(sequentialize-let-value val)))
          ,(sequentialize-let-tail tail))]
      [`(if ,pred ,tail1 ,tail2)
       `(if ,(sequentialize-let-pred pred) ,(sequentialize-let-tail tail1) ,(sequentialize-let-tail tail2))]
      [`(call ,triv ,opands ...) `(call ,triv ,@opands)]
      [`(begin ,effects ... ,tail)
       `(begin ,@(map sequentialize-let-effect effects) ,(sequentialize-let-tail tail))]
      [value (sequentialize-let-value value)]))

  ;; Values-bits-lang-v8.Value -> Imp-mf-lang-v8.Value
  (define (sequentialize-let-value value)
    (match value
      [`(let ([,alocs ,values] ...) ,value)
       `(begin
          ,@(for/list ([aloc alocs]
                       [val values])
              `(set! ,aloc ,(sequentialize-let-value val)))
          ,(sequentialize-let-value value))]
      [`(mref ,aloc ,opand) `(mref ,aloc ,opand)]
      [`(alloc ,opand) `(alloc ,opand)]
      [`(begin ,effects ... ,value)
       `(begin ,@(map sequentialize-let-effect effects) ,(sequentialize-let-value value))]
      [`(if ,pred ,value1 ,value2)
       `(if ,(sequentialize-let-pred pred) ,(sequentialize-let-value value1) ,(sequentialize-let-value value2))]
      [`(,binop ,triv1 ,triv2) value]
      [`(call ,triv ,opands ...) `(call ,triv ,@opands)]
      [triv triv]))

  (match p
    [`(module ,defs ... ,tail)
     `(module ,@(sequentialize-let-defs defs) ,(sequentialize-let-tail tail))]))

(module+ tests
  (check-equal?
    (sequentialize-let
    '(module (let ([x.1 5] [y.2 6])
                (+ x.1 y.2))))
    '(module (begin (set! x.1 5)
                    (set! y.2 6)
                    (+ x.1 y.2))))

  (check-equal?
    (sequentialize-let
    '(module (let ((bar.1 1)) (let ((foo.1 2)) (+ foo.1 bar.1)))))
    '(module (begin (set! bar.1 1)
                    (begin (set! foo.1 2)
                          (+ foo.1 bar.1)))))

  (check-equal?
    (sequentialize-let
    '(module
          (let ((x.7 1))
            (let ((y.8 (let ((z.9 3)) z.9)))
              (let ((z.10 (let ((y.11 2)) (+ y.11 y.11))))
                (if (let ((x.12 6)) (> x.12 7))
                    9
                    10))))))
    '(module
        (begin
          (set! x.7 1)
          (begin
            (set! y.8 (begin (set! z.9 3) z.9))
            (begin
              (set! z.10 (begin (set! y.11 2) (+ y.11 y.11)))
              (if (begin (set! x.12 6) (> x.12 7)) 9 10))))))

  (check-equal?
    (sequentialize-let
    '(module
          (define L.odd?.5 (lambda (x.51) (if (= x.51 0) 0 (let ((y.52 (+ x.51 -1))) (call L.even?.6 y.52)))))
        (define L.even?.6 (lambda (x.53) (if (= x.53 0) 1 (let ((y.54 (+ x.53 -1))) (call L.odd?.5 y.54))))) (call L.even?.6 5)))
    '(module
        (define L.odd?.5
          (lambda (x.51)
            (if (= x.51 0) 0 (begin (set! y.52 (+ x.51 -1)) (call L.even?.6 y.52)))))
      (define L.even?.6
        (lambda (x.53)
          (if (= x.53 0) 1 (begin (set! y.54 (+ x.53 -1)) (call L.odd?.5 y.54)))))
      (call L.even?.6 5)))

  (check-equal?
    (sequentialize-let
    '(module (define L.id.2 (lambda (x.15) x.15)) (let ((y.16 L.id.2)) (call y.16 5))))
    '(module
        (define L.id.2 (lambda (x.15) x.15))
      (begin (set! y.16 L.id.2) (call y.16 5))))

  (check-equal?
    (sequentialize-let
    '(module (define L.zero.8 (lambda (v0.77 v1.78 v2.79 v3.80) 0)) 0))
    '(module (define L.zero.8 (lambda (v0.77 v1.78 v2.79 v3.80) 0)) 0))

  (check-equal?
    (sequentialize-let
    '(module
          (define L.odd?.7
            (lambda (x.17)
              (if (= x.17 0) 0 (let ((y.18 (+ x.17 -1))) (call L.even?.8 y.18)))))
        (define L.even?.8
          (lambda (x.19)
            (if (= x.19 0) 1 (let ((y.20 (+ x.19 -1))) (call L.odd?.7 y.20)))))
        (define L.end-it.9 (lambda (x.21) (+ x.21 1)))
        (let ((x.22 (call L.even?.8 5)) (y.23 10))
          (if (= x.22 0) (call L.end-it.9 x.22) (call L.end-it.9 y.23)))))
    '(module
        (define L.odd?.7
          (lambda (x.17)
            (if (= x.17 0) 0 (begin (set! y.18 (+ x.17 -1)) (call L.even?.8 y.18)))))
      (define L.even?.8
        (lambda (x.19)
          (if (= x.19 0) 1 (begin (set! y.20 (+ x.19 -1)) (call L.odd?.7 y.20)))))
      (define L.end-it.9 (lambda (x.21) (+ x.21 1)))
      (begin
        (set! x.22 (call L.even?.8 5))
        (set! y.23 10)
        (if (= x.22 0) (call L.end-it.9 x.22) (call L.end-it.9 y.23)))))

  (check-equal?
    (sequentialize-let
    '(module
          (define L.eq?.2 (lambda (tmp.15 tmp.16) (if (= tmp.15 tmp.16) 14 6)))
        (define L.+.1
          (lambda (tmp.3 tmp.4)
            (if (let ((tmp.24
                      (if (let ((tmp.25 (bitwise-and tmp.4 7))) (= tmp.25 0))
                          14
                          6)))
                  (!= tmp.24 6))
                (if (let ((tmp.26
                          (if (let ((tmp.27 (bitwise-and tmp.3 7))) (= tmp.27 0))
                              14
                              6)))
                      (!= tmp.26 6))
                    (+ tmp.3 tmp.4)
                    574)
                574)))
        (if (let ((tmp.28
                  (let ((tmp.29 (call L.+.1 40 48))) (call L.eq?.2 tmp.29 88))))
              (!= tmp.28 6))
            32
            48)))
    '(module
        (define L.eq?.2 (lambda (tmp.15 tmp.16) (if (= tmp.15 tmp.16) 14 6)))
      (define L.+.1
        (lambda (tmp.3 tmp.4)
          (if (begin
                (set! tmp.24
                      (if (begin (set! tmp.25 (bitwise-and tmp.4 7)) (= tmp.25 0))
                          14
                          6))
                (!= tmp.24 6))
              (if (begin
                    (set! tmp.26
                          (if (begin (set! tmp.27 (bitwise-and tmp.3 7)) (= tmp.27 0))
                              14
                              6))
                    (!= tmp.26 6))
                  (+ tmp.3 tmp.4)
                  574)
              574)))
      (if (begin
            (set! tmp.28
                  (begin (set! tmp.29 (call L.+.1 40 48)) (call L.eq?.2 tmp.29 88)))
            (!= tmp.28 6))
          32
          48)))

  (check-equal?
    (sequentialize-let
    '(module
          (define L.*.4
            (lambda (tmp.4 tmp.5)
              (if (let ((tmp.27
                        (if (let ((tmp.28 (bitwise-and tmp.5 7))) (= tmp.28 0))
                            14
                            6)))
                    (!= tmp.27 6))
                  (if (let ((tmp.29
                            (if (let ((tmp.30 (bitwise-and tmp.4 7))) (= tmp.30 0))
                                14
                                6)))
                        (!= tmp.29 6))
                      (let ((tmp.31 (arithmetic-shift-right tmp.5 3))) (* tmp.4 tmp.31))
                      318)
                  318)))
        (define L.+.3
          (lambda (tmp.6 tmp.7)
            (if (let ((tmp.32
                      (if (let ((tmp.33 (bitwise-and tmp.7 7))) (= tmp.33 0))
                          14
                          6)))
                  (!= tmp.32 6))
                (if (let ((tmp.34
                          (if (let ((tmp.35 (bitwise-and tmp.6 7))) (= tmp.35 0))
                              14
                              6)))
                      (!= tmp.34 6))
                    (+ tmp.6 tmp.7)
                    574)
                574)))
        (define L.eq?.2 (lambda (tmp.18 tmp.19) (if (= tmp.18 tmp.19) 14 6)))
        (define L.fact.1
          (lambda (x.1)
            (if (let ((tmp.36 (call L.eq?.2 x.1 0))) (!= tmp.36 6))
                8
                (let ((z.2 (call L.+.3 x.1 -8)))
                  (let ((y.3 (call L.fact.1 z.2))) (call L.*.4 x.1 y.3))))))
        (call L.fact.1 80)))
    '(module
        (define L.*.4
          (lambda (tmp.4 tmp.5)
            (if (begin
                  (set! tmp.27
                        (if (begin (set! tmp.28 (bitwise-and tmp.5 7)) (= tmp.28 0))
                            14
                            6))
                  (!= tmp.27 6))
                (if (begin
                      (set! tmp.29
                            (if (begin (set! tmp.30 (bitwise-and tmp.4 7)) (= tmp.30 0))
                                14
                                6))
                      (!= tmp.29 6))
                    (begin
                      (set! tmp.31 (arithmetic-shift-right tmp.5 3))
                      (* tmp.4 tmp.31))
                    318)
                318)))
      (define L.+.3
        (lambda (tmp.6 tmp.7)
          (if (begin
                (set! tmp.32
                      (if (begin (set! tmp.33 (bitwise-and tmp.7 7)) (= tmp.33 0))
                          14
                          6))
                (!= tmp.32 6))
              (if (begin
                    (set! tmp.34
                          (if (begin (set! tmp.35 (bitwise-and tmp.6 7)) (= tmp.35 0))
                              14
                              6))
                    (!= tmp.34 6))
                  (+ tmp.6 tmp.7)
                  574)
              574)))
      (define L.eq?.2 (lambda (tmp.18 tmp.19) (if (= tmp.18 tmp.19) 14 6)))
      (define L.fact.1
        (lambda (x.1)
          (if (begin (set! tmp.36 (call L.eq?.2 x.1 0)) (!= tmp.36 6))
              8
              (begin
                (set! z.2 (call L.+.3 x.1 -8))
                (begin (set! y.3 (call L.fact.1 z.2)) (call L.*.4 x.1 y.3))))))
      (call L.fact.1 80)))
)