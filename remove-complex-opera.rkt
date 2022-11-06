#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide remove-complex-opera*)

;; Performs the monadic form transformation,
;; unnesting all non-trivial operators and operands to binops, calls, and relopss,
;; making data flow explicit and and simple to implement imperatively
;;
;; Exprs-bits-lang-v8 -> Values-bits-lang-v8
(define (remove-complex-opera* p)

  ;; Any -> Boolean
  (define (triv? e)
    (or (label? e) (aloc? e) (int64? e)))

  ;; Exprs-bits-lang-v8.Def -> Values-bits-lang-v8.Def
  (define (remove-complex-opera*-def e)
    (match e
      [`(define ,label (lambda (,alocs ...) ,value))
       `(define ,label (lambda (,@alocs) ,(remove-complex-opera*-value value)))]))

  ;; Symbol Exprs-bits-lang-v8.Value Exprs-bits-lang-v8.Value -> Values-bits-lang-v8.Value
  (define (remove-complex-opera*-op op value1 value2)
    (cond
      [(and (triv? value1) (triv? value2))
       `(,op ,value1 ,value2)]
      [(triv? value1)
       (let ([temp (fresh)])
         `(let ((,temp ,(remove-complex-opera*-value value2))) (,op ,value1 ,temp)))]
      [(triv? value2)
       (let ([temp (fresh)])
         `(let ((,temp ,(remove-complex-opera*-value value1))) (,op ,temp ,value2)))]
      [else
       (let ([temp1 (fresh)]
             [temp2 (fresh)])
         `(let ((,temp1 ,(remove-complex-opera*-value value1)))
            (let ((,temp2 ,(remove-complex-opera*-value value2))) (,op ,temp1 ,temp2))))]))

  ;; (listof Exprs-bits-lang-v8.Value) -> Values-bits-lang-v8.Value
  (define (remove-complex-opera*-call values)

    ;; (listof Exprs-bits-lang-v8.Value) (listof aloc) -> Values-bits-lang-v8.Value
    (define (remove-complex-opera*-call--helper values alocs)
      (if (empty? values)
          `(call ,@alocs)
          (cond
            [(triv? (first values))
             (remove-complex-opera*-call--helper (rest values)
                                                 (append alocs (list (first values))))]
            [else
             (let ([temp (fresh)])
               `(let ((,temp ,(remove-complex-opera*-value (first values))))
                  ,(remove-complex-opera*-call--helper (rest values)
                                                       (append alocs (list temp)))))])))

    (remove-complex-opera*-call--helper values '()))

  ;; Exprs-bits-lang-v8.Pred -> Values-bits-lang-v8.Pred
  (define (remove-complex-opera*-pred e)
    (match e
      [`(true) `(true)]
      [`(false) `(false)]
      [`(not ,pred) `(not ,(remove-complex-opera*-pred pred))]
      [`(let ([,alocs ,values] ...) ,pred)
       `(let
            ,(for/list ([aloc alocs]
                        [val values])
               `(,aloc ,(remove-complex-opera*-value val)))
          ,(remove-complex-opera*-pred pred))]
      [`(if ,pred ,pred1 ,pred2)
       `(if ,(remove-complex-opera*-pred pred)
            ,(remove-complex-opera*-pred pred1)
            ,(remove-complex-opera*-pred pred2))]
      [`(begin ,effects ... ,pred)
       `(begin ,@(map remove-complex-opera*-effect effects) ,(remove-complex-opera*-pred pred))]
      [`(,relop ,value1 ,value2)
       (remove-complex-opera*-op relop value1 value2)]))

  ;; Exprs-bits-lang-v8.Effect -> Values-bits-lang-v8.Effect
  (define (remove-complex-opera*-effect e)
    (match e
      [`(mset! ,value1 ,value2 ,value3)
       (if (triv? value2)
           `(mset! ,(remove-complex-opera*-value value1)
                   ,(remove-complex-opera*-value value2)
                   ,(remove-complex-opera*-value value3))
           (let ([temp (fresh)])
             `(let ((,temp ,(remove-complex-opera*-value value2)))
                (mset! ,(remove-complex-opera*-value value1)
                       ,temp
                       ,(remove-complex-opera*-value value3)))))]
      [`(begin ,effects ... ,effect)
       `(begin ,@(map remove-complex-opera*-effect (cons effects effect)))]))

  ;; Exprs-bits-lang-v8.Value -> Values-bits-lang-v8.Value
  (define (remove-complex-opera*-value e)
    (match e
      [`(let ([,alocs ,values] ...) ,value)
       `(let
            ,(for/list ([aloc alocs]
                        [val values])
               `(,aloc ,(remove-complex-opera*-value val)))
          ,(remove-complex-opera*-value value))]
      [`(if ,pred ,value1 ,value2)
       `(if ,(remove-complex-opera*-pred pred)
            ,(remove-complex-opera*-value value1)
            ,(remove-complex-opera*-value value2))]
      [`(call ,value ,values ...)
       (remove-complex-opera*-call (cons value values))]
      [`(mref ,value1 ,value2)
       (if (triv? value2)
           `(mref ,(remove-complex-opera*-value value1) ,(remove-complex-opera*-value value2))
           (let ([temp (fresh)])
             `(let ((,temp ,(remove-complex-opera*-value value2)))
                (mref ,(remove-complex-opera*-value value1) ,temp))))]
      [`(alloc ,value)
       (if (triv? value)
        `(alloc ,(remove-complex-opera*-value value))
        (let ([temp (fresh)])
          `(let ((,temp ,(remove-complex-opera*-value value)))
              (alloc ,temp))))]
      [`(begin ,effects ... ,value)
       `(begin ,@(map remove-complex-opera*-effect effects) ,(remove-complex-opera*-value value))]
      [`(,binop ,value1 ,value2)
       (remove-complex-opera*-op binop value1 value2)]
      [triv triv]))

  (match p
    [`(module ,defs ... ,value)
     `(module ,@(map remove-complex-opera*-def defs) ,(remove-complex-opera*-value value))]))

(module+ tests
  (check-equal?
    (remove-complex-opera*
    '(module 22))
    '(module 22))

  (check-equal?
    (remove-complex-opera*
    '(module
          (define L.eq?.2 (lambda (tmp.15 tmp.16) (if (= tmp.15 tmp.16) 14 6)))
        (define L.+.1
          (lambda (tmp.3 tmp.4)

            (if (!= (if (= (bitwise-and tmp.4 7) 0) 14 6) 6)
                (if (!= (if (= (bitwise-and tmp.3 7) 0) 14 6) 6) (+ tmp.3 tmp.4) 574)
                574)

            ))
        (if (!= (call L.eq?.2 (call L.+.1 40 48) 88) 6) 32 48)))
    '(module
        (define L.eq?.2 (lambda (tmp.15 tmp.16) (if (= tmp.15 tmp.16) 14 6)))
      (define L.+.1
        (lambda (tmp.3 tmp.4)
          (if (let ((tmp.1
                      (if (let ((tmp.2 (bitwise-and tmp.4 7))) (= tmp.2 0)) 14 6)))
                (!= tmp.1 6))
              (if (let ((tmp.3
                          (if (let ((tmp.4 (bitwise-and tmp.3 7))) (= tmp.4 0))
                              14
                              6)))
                    (!= tmp.3 6))
                  (+ tmp.3 tmp.4)
                  574)
              574)
          ))
      (if (let ((tmp.5 (let ((tmp.6 (call L.+.1 40 48))) (call L.eq?.2 tmp.6 88))))
            (!= tmp.5 6))
          32
          48)))

  (check-equal?
    (remove-complex-opera*
    '(module
          (define L.<.2
            (lambda (tmp.9 tmp.10)
              (if (!= (if (= (bitwise-and tmp.10 7) 0) 14 6) 6)
                  (if (!= (if (= (bitwise-and tmp.9 7) 0) 14 6) 6)
                      (if (< tmp.9 tmp.10) 14 6)
                      1086)
                  1086)))
        (define L.swap.1
          (lambda (x.2 y.1)
            (if (!= (call L.<.2 y.1 x.2) 6) x.2 (call L.swap.1 y.1 x.2))))
        (call L.swap.1 8 16)))
    '(module
        (define L.<.2
          (lambda (tmp.9 tmp.10)
            (if (let ((tmp.7
                        (if (let ((tmp.8 (bitwise-and tmp.10 7))) (= tmp.8 0)) 14 6)))
                  (!= tmp.7 6))
                (if (let ((tmp.9
                            (if (let ((tmp.10 (bitwise-and tmp.9 7))) (= tmp.10 0))
                                14
                                6)))
                      (!= tmp.9 6))
                    (if (< tmp.9 tmp.10) 14 6)
                    1086)
                1086)))
      (define L.swap.1
        (lambda (x.2 y.1)
          (if (let ((tmp.11 (call L.<.2 y.1 x.2))) (!= tmp.11 6))
              x.2
              (call L.swap.1 y.1 x.2))))
      (call L.swap.1 8 16)))

  (check-equal?
    (remove-complex-opera*
    '(module
          (define L.*.4
            (lambda (tmp.4 tmp.5)
              (if (!= (if (= (bitwise-and tmp.5 7) 0) 14 6) 6)
                  (if (!= (if (= (bitwise-and tmp.4 7) 0) 14 6) 6)
                      (* tmp.4 (arithmetic-shift-right tmp.5 3))
                      318)
                  318)))
        (define L.+.3
          (lambda (tmp.6 tmp.7)
            (if (!= (if (= (bitwise-and tmp.7 7) 0) 14 6) 6)
                (if (!= (if (= (bitwise-and tmp.6 7) 0) 14 6) 6) (+ tmp.6 tmp.7) 574)
                574)))
        (define L.eq?.2 (lambda (tmp.18 tmp.19) (if (= tmp.18 tmp.19) 14 6)))
        (define L.fact.1
          (lambda (x.1)
            (if (!= (call L.eq?.2 x.1 0) 6)
                8
                (let ((z.2 (call L.+.3 x.1 -8)))
                  (let ((y.3 (call L.fact.1 z.2))) (call L.*.4 x.1 y.3))))))
        (call L.fact.1 80)))
    '(module
        (define L.*.4
          (lambda (tmp.4 tmp.5)
            (if (let ((tmp.12
                        (if (let ((tmp.13 (bitwise-and tmp.5 7))) (= tmp.13 0)) 14 6)))
                  (!= tmp.12 6))
                (if (let ((tmp.14
                            (if (let ((tmp.15 (bitwise-and tmp.4 7))) (= tmp.15 0))
                                14
                                6)))
                      (!= tmp.14 6))
                    (let ((tmp.16 (arithmetic-shift-right tmp.5 3))) (* tmp.4 tmp.16))
                    318)
                318)))
      (define L.+.3
        (lambda (tmp.6 tmp.7)
          (if (let ((tmp.17
                      (if (let ((tmp.18 (bitwise-and tmp.7 7))) (= tmp.18 0)) 14 6)))
                (!= tmp.17 6))
              (if (let ((tmp.19
                          (if (let ((tmp.20 (bitwise-and tmp.6 7))) (= tmp.20 0))
                              14
                              6)))
                    (!= tmp.19 6))
                  (+ tmp.6 tmp.7)
                  574)
              574)))
      (define L.eq?.2 (lambda (tmp.18 tmp.19) (if (= tmp.18 tmp.19) 14 6)))
      (define L.fact.1
        (lambda (x.1)
          (if (let ((tmp.21 (call L.eq?.2 x.1 0))) (!= tmp.21 6))
              8
              (let ((z.2 (call L.+.3 x.1 -8)))
                (let ((y.3 (call L.fact.1 z.2))) (call L.*.4 x.1 y.3))))))
      (call L.fact.1 80)))

  (check-equal?
    (remove-complex-opera*
    '(module
          (let ((tmp.1 (+ (alloc 16) 1)))
            (begin (mset! tmp.1 -1 40) (mset! tmp.1 7 48) tmp.1))))
    '(module
        (let ((tmp.1 (let ((tmp.22 (alloc 16))) (+ tmp.22 1))))
          (begin (mset! tmp.1 -1 40) (mset! tmp.1 7 48) tmp.1))))

  (check-equal?
    (remove-complex-opera*
    '(module
          (if (let ((x.1 (alloc 8)) (y.1 (alloc 16)) (z.1 0))
                (begin
                  (mset! x.1 0 (alloc (let ((t.1 32)) (+ t.1 (+ t.1 8)))))
                  (mset! y.1 z.1 18)
                  (mset! y.1 (+ z.1 8) 40)
                  (= (mref y.1 z.1) (mref y.1 (+ z.1 8)))))
              8
              16)))
    '(module
        (if (let ((x.1 (alloc 8)) (y.1 (alloc 16)) (z.1 0))
              (begin
                (mset!
                  x.1
                  0
                  (let ((tmp.1
                        (let ((t.1 32)) (let ((tmp.2 (+ t.1 8))) (+ t.1 tmp.2)))))
                    (alloc tmp.1)))
                (mset! y.1 z.1 18)
                (let ((tmp.3 (+ z.1 8))) (mset! y.1 tmp.3 40))
                (let ((tmp.4 (mref y.1 z.1)))
                  (let ((tmp.5 (let ((tmp.6 (+ z.1 8))) (mref y.1 tmp.6))))
                    (= tmp.4 tmp.5)))))
            8
            16)))
)