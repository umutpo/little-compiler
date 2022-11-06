#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide normalize-bind)

;; Compiles Proc-imp-mf-lang-v8 to Proc-imp-cmf-lang-v8,
;; pushing set! under begin so that the right-hand-side of
;; each set! is base value-producing operation.
;;
;; Imp-mf-lang-v8 -> Proc-imp-cmf-lang-v8
(define (normalize-bind p)

  ;; Any -> Boolean
  (define (opand? e)
    (or (int64? e) (aloc? e)))

  ;; imp-mf-lang-v8.Def -> proc-imp-cmf-lang-v8.Def
  (define (normalize-bind-def def)
    (match def
      [`(define ,name (lambda (,params ...) ,tail))
       `(define ,name (lambda ,params ,(normalize-bind-tail tail)))]))

  ;; imp-mf-lang-v8.Pred -> proc-imp-cmf-lang-v8.Pred
  (define (normalize-bind-pred e)
    (match e
      [`(true) `(true)]
      [`(false) `(false)]
      [`(not ,pred) `(not ,(normalize-bind-pred pred))]
      [`(begin ,effects ... ,pred)
       `(begin ,@(map normalize-bind-effect effects) ,(normalize-bind-pred pred))]
      [`(if ,pred ,pred1 ,pred2)
       `(if ,(normalize-bind-pred pred) ,(normalize-bind-pred pred1) ,(normalize-bind-pred pred2))]
      [`(,relop ,opand1 ,opand2) e]))

  ;; imp-mf-lang-v8.Tail -> proc-imp-cmf-lang-v8.Tail
  (define (normalize-bind-tail e)
    (match e
      [`(begin ,effects ... ,tail)
       `(begin ,@(map normalize-bind-effect effects) ,(normalize-bind-tail tail))]
      [`(if ,pred ,tail1 ,tail2)
       `(if ,(normalize-bind-pred pred) ,(normalize-bind-tail tail1) ,(normalize-bind-tail tail2))]
      [`(call ,triv ,opands ...) `(call ,triv ,@opands)]
      [value (normalize-bind-value value)]))

  ;; imp-mf-lang-v8.Effect -> proc-imp-cmf-lang-v8.Effect
  (define (normalize-bind-effect e)
    (match e
      [`(set! ,aloc ,value)
       (push-set (normalize-bind-value value) aloc (void))]
      [`(mset! ,aloc ,opand ,value)
       (push-set (normalize-bind-value value) aloc opand)]
      [`(begin ,effects ...)
       `(begin ,@(map normalize-bind-effect effects))]
      [`(if ,pred ,effect1 ,effect2)
       `(if ,(normalize-bind-pred pred) ,(normalize-bind-effect effect1) ,(normalize-bind-effect effect2))]))

  ;; imp-mf-lang-v8.Value -> proc-imp-cmf-lang-v8.Value
  (define (normalize-bind-value e)
    (match e
      [`(begin ,effects ... ,value)
       `(begin ,@(map normalize-bind-effect effects) ,(normalize-bind-value value))]
      [`(if ,pred ,value1 ,value2)
       `(if ,(normalize-bind-pred pred) ,(normalize-bind-value value1) ,(normalize-bind-value value2))]
      [`(call ,triv ,opands ...) `(call ,triv ,@opands)]
      [`(mref ,aloc ,opand) `(mref ,aloc ,opand)]
      [`(alloc ,opand) `(alloc ,opand)]
      [`(,binop ,opand1 ,opand2) `(,binop ,opand1 ,opand2)]
      [triv triv]))

  ;; imp-mf-lang-v8.Value aloc imp-mf-lang-v8.Opand -> proc-imp-cmf-lang-v8.Value
  (define (push-set e aloc op)
    (match e
      [`(begin ,effects ... ,value)
       `(begin ,@effects ,(push-set value aloc op))]
      [`(if ,pred ,value1 ,value2)
       `(if ,pred ,(push-set value1 aloc op) ,(push-set value2 aloc op))]
      [`(call ,triv ,opands ...)
       (if (opand? op)
           `(mset! ,aloc ,op (call ,triv ,@opands))
           `(set! ,aloc (call ,triv ,@opands)))]
      [`(mref ,aloc^ ,opand)
       (if (opand? op)
           `(mset! ,aloc ,op (mref ,aloc^ ,opand))
           `(set! ,aloc (mref ,aloc^ ,opand)))]
      [`(alloc ,opand)
       (if (opand? op)
           (let ([tmp (fresh)])
           `(begin (set! ,tmp (alloc ,opand))
                   (mset! ,aloc ,op ,tmp)))
           `(set! ,aloc (alloc ,opand)))]
      [`(,binop ,triv1 ,triv2)
       (if (opand? op)
           (let ([tmp (fresh)])
           `(begin (set! ,tmp (,binop ,triv1 ,triv2))
                   (mset! ,aloc ,op ,tmp)))
           `(set! ,aloc ,e))]
      [triv
       (if (opand? op)
           (let ([tmp (fresh)])
           `(begin (set! ,tmp ,e)
                   (mset! ,aloc ,op ,tmp)))
           `(set! ,aloc ,e))]))

  (match p
    [`(module ,defs ... ,tail)
     `(module ,@(map normalize-bind-def defs) ,(normalize-bind-tail tail))]))

(module+ tests
  (check-equal?
  (normalize-bind
    '(module (+ 2 2)))
  '(module (+ 2 2)))

  (check-equal?
  (normalize-bind
    '(module (begin (set! x.1 5) x.1)))
  '(module (begin (set! x.1 5) x.1)))

  (check-equal?
  (normalize-bind
    '(module (begin (set! x.1 (begin (set! y.2 5) y.2)) x.1)))
  '(module (begin (begin (set! y.2 5) (set! x.1 y.2)) x.1)))

  (check-equal?
  (normalize-bind
    '(module (begin
              (set! x.1 (begin
                          (set! y.2 (begin
                                      (set! x.3 5)
                                      (set! y.4 8)
                                      x.3))
                          y.2))
              (+ 4 6))))
  '(module
        (begin
          (begin (begin (set! x.3 5) (set! y.4 8) (set! y.2 x.3)) (set! x.1 y.2))
          (+ 4 6))))

  (check-equal?
  (normalize-bind
    '(module (begin (set! x.1 (begin 5)) x.1)))
  '(module (begin (begin (set! x.1 5)) x.1)))

  (check-equal?
  (normalize-bind
    '(module (begin
              (set! x.1 (begin
                          (set! y.2 (begin 5))
                          y.2))
              (+ 4 6))))
  '(module (begin (begin (begin (set! y.2 5)) (set! x.1 y.2)) (+ 4 6))))

  (check-equal?
  (normalize-bind
    '(module
        (begin
          (if (true)
              (set! x.3
                    (begin
                      (set! y.4
                            (begin
                              (set! z.4 (+ 4 5))
                              z.4))
                      y.4))
              (set! x.3 y.7))
          x.3)))
  '(module
        (begin
          (if (true)
              (begin (begin (set! z.4 (+ 4 5)) (set! y.4 z.4)) (set! x.3 y.4))
              (set! x.3 y.7))
          x.3)))
  (check-equal?
  (normalize-bind
    '(module
        (begin
          (if (true)
              (set! x.3
                    (begin
                      (set! y.4
                            (begin
                              (set! z.4 (+ 4 5))
                              z.4))
                      y.4))
              (set! x.3 y.7))
          x.3)))
  '(module
        (begin
          (if (true)
              (begin (begin (set! z.4 (+ 4 5)) (set! y.4 z.4)) (set! x.3 y.4))
              (set! x.3 y.7))
          x.3)))

  (check-equal?
  (normalize-bind
    '(module
        (begin
          (set! x.7 1)
          (begin
            (set! y.8
                  (begin
                    (set! z.9 3)
                    z.9))
            (begin
              (set! z.10
                    (begin
                      (set! y.11 2)
                      (+ y.11 y.11)))
              (if (begin
                    (set! x.12 6)
                    (> x.12 7))
                  9
                  10))))))
  '(module
        (begin
          (set! x.7 1)
          (begin
            (begin (set! z.9 3) (set! y.8 z.9))
            (begin
              (begin (set! y.11 2) (set! z.10 (+ y.11 y.11)))
              (if (begin (set! x.12 6) (> x.12 7)) 9 10))))))
  (check-equal?
  (normalize-bind
    '(module (begin (set! x.5 (if (true) (begin (set! y.2 14) 12) (begin 15))) x.5)))
  '(module
        (begin
          (if (true) (begin (set! y.2 14) (set! x.5 12)) (begin (set! x.5 15)))
          x.5)))

  (check-equal?
  (normalize-bind '(module (define L.zero.8 (lambda (v0.77 v1.78 v2.79 v3.80) 0)) 0))
  '(module (define L.zero.8 (lambda (v0.77 v1.78 v2.79 v3.80) 0)) 0))

  (check-equal?
  (normalize-bind
    '(module
        (define L.id1.11 (lambda (x.122) x.122))
      (define L.id2.12 (lambda (x.123) x.123))
      (begin (if (true)
                  (set! y.124 L.id1.11)
                  (set! y.124 L.id2.12))
              (call y.124 5))))
  '(module
        (define L.id1.11 (lambda (x.122) x.122))
      (define L.id2.12 (lambda (x.123) x.123))
      (begin
        (if (true) (set! y.124 L.id1.11) (set! y.124 L.id2.12))
        (call y.124 5))))

  (check-equal?
  (normalize-bind
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
  '(module
        (define L.*.4
          (lambda (tmp.4 tmp.5)
            (if (begin
                  (if (begin (set! tmp.28 (bitwise-and tmp.5 7)) (= tmp.28 0))
                      (set! tmp.27 14)
                      (set! tmp.27 6))
                  (!= tmp.27 6))
                (if (begin
                      (if (begin (set! tmp.30 (bitwise-and tmp.4 7)) (= tmp.30 0))
                          (set! tmp.29 14)
                          (set! tmp.29 6))
                      (!= tmp.29 6))
                    (begin
                      (set! tmp.31 (arithmetic-shift-right tmp.5 3))
                      (* tmp.4 tmp.31))
                    318)
                318)))
      (define L.+.3
        (lambda (tmp.6 tmp.7)
          (if (begin
                (if (begin (set! tmp.33 (bitwise-and tmp.7 7)) (= tmp.33 0))
                    (set! tmp.32 14)
                    (set! tmp.32 6))
                (!= tmp.32 6))
              (if (begin
                    (if (begin (set! tmp.35 (bitwise-and tmp.6 7)) (= tmp.35 0))
                        (set! tmp.34 14)
                        (set! tmp.34 6))
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

  (check-equal?
  (normalize-bind
    '(module
        (define L.fact.12
          (lambda (x.94)
            (if (= x.94 0)
                1
                (begin
                  (set! z.95 (+ x.94 -1))
                  (begin (set! y.96 (call L.fact.12 z.95)) (* x.94 y.96))))))
      (call L.fact.12 5)))
  '(module
        (define L.fact.12
          (lambda (x.94)
            (if (= x.94 0)
                1
                (begin
                  (set! z.95 (+ x.94 -1))
                  (begin (set! y.96 (call L.fact.12 z.95)) (* x.94 y.96))))))
      (call L.fact.12 5)))

  (check-equal?
  (normalize-bind
    '(module
        (begin
          (set! tmp.1 (begin (set! tmp.1 (alloc 16)) (+ tmp.1 1)))
          (begin (mset! tmp.1 -1 40) (mset! tmp.1 7 48) tmp.1))))
  '(module
        (begin
          (begin (set! tmp.1 (alloc 16)) (set! tmp.1 (+ tmp.1 1)))
          (begin (mset! tmp.1 -1 40) (mset! tmp.1 7 48) tmp.1))))

  (check-equal?
  (normalize-bind
    '(module
        (begin
          (set! tmp.1
                (begin
                  (set! tmp.2 (begin (set! tmp.2 (alloc 16)) (+ tmp.2 1)))
                  (begin (mset! tmp.2 -1 40) (mset! tmp.2 7 48) tmp.2)))
          (mref tmp.1 -1))))
  '(module
        (begin
          (begin
            (begin (set! tmp.2 (alloc 16)) (set! tmp.2 (+ tmp.2 1)))
            (begin (mset! tmp.2 -1 40) (mset! tmp.2 7 48) (set! tmp.1 tmp.2)))
          (mref tmp.1 -1))))

  (check-equal?
  (normalize-bind
    '(module
        (begin
          (set! tmp.1
                (begin
                  (set! tmp.3 (begin (set! tmp.2 (alloc 32)) (+ tmp.2 3)))
                  (begin (mset! tmp.3 -3 24) tmp.3)))
          (mref tmp.1 53))))
  '(module
        (begin
          (begin
            (begin (set! tmp.2 (alloc 32)) (set! tmp.3 (+ tmp.2 3)))
            (begin (mset! tmp.3 -3 24) (set! tmp.1 tmp.3)))
          (mref tmp.1 53))))

  (check-equal?
  (normalize-bind
    '(module
        (begin
          (set! tmp.1 (begin (set! tmp.1 (alloc 16)) (+ tmp.1 1)))
          (begin
            (mset! tmp.1 -1
                    (begin (set! tmp.2 (alloc 16)) (+ tmp.2 1)))
            (mset! tmp.1 7 48) tmp.1))))
  '(module
        (begin
          (begin (set! tmp.1 (alloc 16)) (set! tmp.1 (+ tmp.1 1)))
          (begin
            (begin
              (set! tmp.2 (alloc 16))
              (begin (set! tmp.1 (+ tmp.2 1)) (mset! tmp.1 -1 tmp.1)))
            (mset! tmp.1 7 48)
            tmp.1))))
)