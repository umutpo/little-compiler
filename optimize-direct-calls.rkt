#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide optimize-direct-calls)

;; Inline all direct calls to first-class procedures.
;;
;; just-exprs-lang-v9 -> just-exprs-lang-v9
(define (optimize-direct-calls p)

  ;; just-exprs-lang-v9.Value -> just-exprs-lang-v9.Value
  (define (optimize-direct-call-unsafe-procedure-call value values)
    (match value
      [`(lambda (,alocs ...) ,value)
       `(let ,(for/foldr ([lets '()])
                         ([aloc alocs]
                          [v values])
                (append (list `(,aloc ,(optimize-direct-calls-value v))) lets))
          ,(optimize-direct-calls-value value))]
      [_ `(unsafe-procedure-call ,value ,@values)]))

  ;; just-exprs-lang-v9.Triv -> just-exprs-lang-v9.Triv
  (define (optimize-direct-call-triv triv)
    (match triv
      [`(lambda (,alocs ...) ,value)
       `(lambda ,alocs ,(optimize-direct-calls-value value))]
      [_ triv]))

  ;; just-exprs-lang-v9.Effect -> just-exprs-lang-v9.Effect
  (define (optimize-direct-call-effect e)
    (match e
      [`(begin ,effects ... ,effect)
       `(begin ,@(map optimize-direct-call-effect (cons effects effect)))]
      [`(,primop ,values ...)
       `(,primop ,@(map optimize-direct-calls-value values))]))

  ;; just-exprs-lang-v9.Value -> just-exprs-lang-v9.Value
  (define (optimize-direct-calls-value v)
    (match v
      [`(unsafe-procedure-call ,value ,values ...)
       (optimize-direct-call-unsafe-procedure-call value values)]
      [`(letrec ([,alocs ,lambdas] ...) ,value)
       `(letrec ,(map (lambda (aloc l) `(,aloc ,(optimize-direct-call-triv l))) alocs lambdas)
                ,(optimize-direct-calls-value value))]
      [`(let ([,alocs ,values] ...) ,value)
       `(let ,(map (lambda (aloc v) `(,aloc ,(optimize-direct-calls-value v))) alocs values)
          ,(optimize-direct-calls-value value))]
      [`(if ,value1 ,value2 ,value3)
       `(if ,(optimize-direct-calls-value value1)
            ,(optimize-direct-calls-value value2)
            ,(optimize-direct-calls-value value3))]
      [`(begin ,effects ... ,value)
       `(begin ,@(map optimize-direct-call-effect effects) ,(optimize-direct-calls-value value))]
      [`(,primop ,values ...)
       `(,primop ,@(map optimize-direct-calls-value values))]
      [triv (optimize-direct-call-triv triv)]))

  (match p
    [`(module ,value)
     `(module ,(optimize-direct-calls-value value))]))

(module+ tests
  (check-equal?
    (optimize-direct-calls
      '(module
        (letrec ((|+.1|
                  (lambda (tmp.2 tmp.3)
                    (if (fixnum? tmp.3)
                      (if (fixnum? tmp.2) (unsafe-fx+ tmp.2 tmp.3) (error 2))
                      (error 2)))))
          (unsafe-procedure-call (lambda (x.1 y.2) (unsafe-procedure-call |+.1| x.1 y.2)) 10 15))))
    '(module
      (letrec ((|+.1|
                (lambda (tmp.2 tmp.3)
                  (if (fixnum? tmp.3)
                    (if (fixnum? tmp.2) (unsafe-fx+ tmp.2 tmp.3) (error 2))
                    (error 2)))))
        (let ((x.1 10) (y.2 15)) (unsafe-procedure-call |+.1| x.1 y.2)))))

  (check-equal?
    (optimize-direct-calls
      '(module
        (letrec ((|+.1|
                  (lambda (tmp.2 tmp.3)
                    (if (fixnum? tmp.3)
                      (if (fixnum? tmp.2) 
                          (unsafe-procedure-call (lambda (z.3 t.4) (unsafe-fx+ z.3 t.4)) tmp.2 tmp.3) 
                          (error 2))
                      (error 2)))))
          (unsafe-procedure-call (lambda (x.1 y.2) (unsafe-procedure-call |+.1| x.1 y.2)) 10 15))))
    '(module
      (letrec ((|+.1|
                (lambda (tmp.2 tmp.3)
                  (if (fixnum? tmp.3)
                    (if (fixnum? tmp.2)
                      (let ((z.3 tmp.2) (t.4 tmp.3)) (unsafe-fx+ z.3 t.4))
                      (error 2))
                    (error 2)))))
        (let ((x.1 10) (y.2 15)) (unsafe-procedure-call |+.1| x.1 y.2)))))

  (check-equal?
    (optimize-direct-calls
      '(module
        (letrec ((vector-init-loop.34
                  (lambda (len.35 i.36 vec.37)
                    (if (eq? len.35 i.36)
                      vec.37
                      (begin
                        (unsafe-vector-set! vec.37 i.36 0)
                        (unsafe-procedure-call
                        vector-init-loop.34
                        len.35
                        (unsafe-fx+ i.36 1)
                        vec.37)))))
                (make-init-vector.38
                  (lambda (tmp.39)
                    (let ((tmp.40 (unsafe-make-vector tmp.39)))
                      (unsafe-procedure-call vector-init-loop.34 tmp.39 0 tmp.40))))
                (make-vector.32
                  (lambda (tmp.33)
                    (if (fixnum? tmp.33)
                      (unsafe-procedure-call make-init-vector.38 tmp.33)
                      (error 8)))))
          (let ((x.1 (unsafe-procedure-call make-vector.32 5)))
            (unsafe-procedure-call (lambda (a.2) (unsafe-vector-length a.2)) x.1 b.1)))))
    '(module
      (letrec ((vector-init-loop.34
                (lambda (len.35 i.36 vec.37)
                  (if (eq? len.35 i.36)
                    vec.37
                    (begin
                      (unsafe-vector-set! vec.37 i.36 0)
                      (unsafe-procedure-call
                      vector-init-loop.34
                      len.35
                      (unsafe-fx+ i.36 1)
                      vec.37)))))
              (make-init-vector.38
                (lambda (tmp.39)
                  (let ((tmp.40 (unsafe-make-vector tmp.39)))
                    (unsafe-procedure-call vector-init-loop.34 tmp.39 0 tmp.40))))
              (make-vector.32
                (lambda (tmp.33)
                  (if (fixnum? tmp.33)
                    (unsafe-procedure-call make-init-vector.38 tmp.33)
                    (error 8)))))
        (let ((x.1 (unsafe-procedure-call make-vector.32 5)))
          (let ((a.2 x.1)) (unsafe-vector-length a.2))))))

  (check-equal?
    (optimize-direct-calls
      '(module
        (letrec ((eq?.56 (lambda (tmp.57 tmp.58) (eq? tmp.57 tmp.58)))
                (|+.59|
                  (lambda (tmp.60 tmp.61)
                    (if (fixnum? tmp.61)
                      (if (fixnum? tmp.60) (unsafe-fx+ tmp.60 tmp.61) (error 2))
                      (error 2))))
                (|+.62|
                  (lambda (tmp.63 tmp.64)
                    (if (fixnum? tmp.64)
                      (if (fixnum? tmp.63) (unsafe-fx+ tmp.63 tmp.64) (error 2))
                      (error 2)))))
          (let ((x.1 0) (y.2 0))
            (if (unsafe-procedure-call eq?.56 x.1 y.2)
              (unsafe-procedure-call (lambda (x.1) (unsafe-procedure-call |+.59| x.1 1)) 5)
              (unsafe-procedure-call (lambda (y.2) (unsafe-procedure-call |+.62| y.2 1)) 10))))))
    '(module
      (letrec ((eq?.56 (lambda (tmp.57 tmp.58) (eq? tmp.57 tmp.58)))
              (|+.59|
                (lambda (tmp.60 tmp.61)
                  (if (fixnum? tmp.61)
                    (if (fixnum? tmp.60) (unsafe-fx+ tmp.60 tmp.61) (error 2))
                    (error 2))))
              (|+.62|
                (lambda (tmp.63 tmp.64)
                  (if (fixnum? tmp.64)
                    (if (fixnum? tmp.63) (unsafe-fx+ tmp.63 tmp.64) (error 2))
                    (error 2)))))
        (let ((x.1 0) (y.2 0))
          (if (unsafe-procedure-call eq?.56 x.1 y.2)
            (let ((x.1 5)) (unsafe-procedure-call |+.59| x.1 1))
            (let ((y.2 10)) (unsafe-procedure-call |+.62| y.2 1)))))))
)