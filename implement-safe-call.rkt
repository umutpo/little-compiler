#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide implement-safe-call)

;; Implement call as an unsafe procedure call with dynamic checks.
;; 
;; exprs-unsafe-data-lang-v9 -> exprs-unsafe-lang-v9
(define (implement-safe-call p)

  (define primops '(unsafe-fx* unsafe-fx+ unsafe-fx- eq? unsafe-fx< unsafe-fx<=
                    unsafe-fx> unsafe-fx>= fixnum? boolean? empty? void? ascii-char?
                    error? not pair? vector? procedure? cons unsafe-car unsafe-cdr
                    unsafe-make-vector unsafe-vector-length unsafe-vector-set!
                    unsafe-vector-ref unsafe-procedure-arity))

  ;; exprs-unsafe-data-lang-v9.Triv -> exprs-unsafe-lang-v9.Triv
  (define (implement-safe-call-triv triv)
    (match triv
      [`(lambda (,alocs ...) ,value)
       `(lambda ,alocs ,(implement-safe-call-value value))]
      [_ triv]))

  ;; exprs-unsafe-data-lang-v9.Effect -> exprs-unsafe-lang-v9.Effect
  (define (implement-safe-call-effect e)
    (match e
      [`(begin ,effects ... ,effect)
       `(begin ,@(map implement-safe-call-effect (cons effects effect)))]
      [`(,primop ,values ...)
       `(,primop ,@(map implement-safe-call-value values))]))

  ;; exprs-unsafe-data-lang-v9.Value -> exprs-unsafe-lang-v9.Value
  (define (implement-safe-call-value v)
    (match v
      [`(call ,value ,values ...)
       `(unsafe-procedure-call ,@(map implement-safe-call-value (cons value values)))]
      [`(let ([,alocs ,values] ...) ,val)
       `(let ,(map (lambda (aloc v) `(,aloc ,(implement-safe-call-value v))) alocs values)
          ,(implement-safe-call-value val))]
      [`(if ,value1 ,value2 ,value3)
       `(if ,(implement-safe-call-value value1) 
            ,(implement-safe-call-value value2) 
            ,(implement-safe-call-value value3))]
      [`(begin ,effects ... ,value)
       `(begin ,@(map implement-safe-call-effect effects) ,(implement-safe-call-value value))]
      [`(,primop ,values ...) #:when (memq primop primops)
       `(,primop ,@(map implement-safe-call-value values))]
      [triv (implement-safe-call-triv triv)]))
  
  ;; exprs-unsafe-data-lang-v9.Definition -> exprs-unsafe-lang-v9.Definition
  (define (implement-safe-call-def def)
    (match def
      [`(define ,aloc (lambda (,alocs ...) ,value))
       `(define ,aloc (lambda ,alocs ,(implement-safe-call-value value)))]))

  (match p
    [`(module ,defs ... ,value)
     `(module ,@(map implement-safe-call-def defs) ,(implement-safe-call-value value))]))

(module+ tests
  (check-equal?
    (implement-safe-call
      '(module
        (define |+.1|
          (lambda (tmp.2 tmp.3)
            (if (fixnum? tmp.3)
              (if (fixnum? tmp.2) (unsafe-fx+ tmp.2 tmp.3) (error 2))
              (error 2))))
        (call |+.1| 5 3)))
    '(module
      (define |+.1|
        (lambda (tmp.2 tmp.3)
          (if (fixnum? tmp.3)
            (if (fixnum? tmp.2) (unsafe-fx+ tmp.2 tmp.3) (error 2))
            (error 2))))
      (unsafe-procedure-call |+.1| 5 3)))

  (check-equal?
    (implement-safe-call
      '(module
        (define *.21
          (lambda (tmp.22 tmp.23)
            (if (fixnum? tmp.23)
              (if (fixnum? tmp.22) (unsafe-fx* tmp.22 tmp.23) (error 1))
              (error 1))))
        *.21))
    '(module
      (define *.21
        (lambda (tmp.22 tmp.23)
          (if (fixnum? tmp.23)
            (if (fixnum? tmp.22) (unsafe-fx* tmp.22 tmp.23) (error 1))
            (error 1))))
      *.21))

  (check-equal?
      (implement-safe-call
      '(module
          (define vector-init-loop.34
          (lambda (len.35 i.36 vec.37)
              (if (eq? len.35 i.36)
              vec.37
              (begin
                  (unsafe-vector-set! vec.37 i.36 0)
                  (call vector-init-loop.34 len.35 (unsafe-fx+ i.36 1) vec.37)))))
          (define make-init-vector.38
          (lambda (tmp.39)
              (let ((tmp.40 (unsafe-make-vector tmp.39)))
              (call vector-init-loop.34 tmp.39 0 tmp.40))))
          (define make-vector.32
          (lambda (tmp.33)
              (if (fixnum? tmp.33) (call make-init-vector.38 tmp.33) (error 8))))
          (let ((x.1 (call make-vector.32 5))) x.1)))
    '(module
          (define vector-init-loop.34
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
          (define make-init-vector.38
              (lambda (tmp.39)
              (let ((tmp.40 (unsafe-make-vector tmp.39)))
                  (unsafe-procedure-call vector-init-loop.34 tmp.39 0 tmp.40))))
          (define make-vector.32
              (lambda (tmp.33)
              (if (fixnum? tmp.33)
                  (unsafe-procedure-call make-init-vector.38 tmp.33)
                  (error 8))))
          (let ((x.1 (unsafe-procedure-call make-vector.32 5))) x.1)))

  (check-equal?
    (implement-safe-call
      '(module
          (define unsafe-vector-ref.44
          (lambda (tmp.45 tmp.46)
              (if (unsafe-fx< tmp.46 (unsafe-vector-length tmp.45))
              (if (unsafe-fx>= tmp.46 0)
                  (unsafe-vector-ref tmp.45 tmp.46)
                  (error 11))
              (error 11))))
          (define vector-ref.41
          (lambda (tmp.42 tmp.43)
              (if (fixnum? tmp.43)
              (if (vector? tmp.42)
                  (call unsafe-vector-ref.44 tmp.42 tmp.43)
                  (error 11))
              (error 11))))
          (define vector-init-loop.49
          (lambda (len.50 i.51 vec.52)
              (if (eq? len.50 i.51)
              vec.52
              (begin
                  (unsafe-vector-set! vec.52 i.51 0)
                  (call vector-init-loop.49 len.50 (unsafe-fx+ i.51 1) vec.52)))))
          (define make-init-vector.53
          (lambda (tmp.54)
              (let ((tmp.55 (unsafe-make-vector tmp.54)))
              (call vector-init-loop.49 tmp.54 0 tmp.55))))
          (define make-vector.47
          (lambda (tmp.48)
              (if (fixnum? tmp.48) (call make-init-vector.53 tmp.48) (error 8))))
          (call vector-ref.41 (call make-vector.47 2) 0)))
    '(module
      (define unsafe-vector-ref.44
          (lambda (tmp.45 tmp.46)
          (if (unsafe-fx< tmp.46 (unsafe-vector-length tmp.45))
              (if (unsafe-fx>= tmp.46 0)
              (unsafe-vector-ref tmp.45 tmp.46)
              (error 11))
              (error 11))))
      (define vector-ref.41
          (lambda (tmp.42 tmp.43)
          (if (fixnum? tmp.43)
              (if (vector? tmp.42)
              (unsafe-procedure-call unsafe-vector-ref.44 tmp.42 tmp.43)
              (error 11))
              (error 11))))
      (define vector-init-loop.49
          (lambda (len.50 i.51 vec.52)
          (if (eq? len.50 i.51)
              vec.52
              (begin
              (unsafe-vector-set! vec.52 i.51 0)
              (unsafe-procedure-call
              vector-init-loop.49
              len.50
              (unsafe-fx+ i.51 1)
              vec.52)))))
      (define make-init-vector.53
          (lambda (tmp.54)
          (let ((tmp.55 (unsafe-make-vector tmp.54)))
              (unsafe-procedure-call vector-init-loop.49 tmp.54 0 tmp.55))))
      (define make-vector.47
          (lambda (tmp.48)
          (if (fixnum? tmp.48)
              (unsafe-procedure-call make-init-vector.53 tmp.48)
              (error 8))))
      (unsafe-procedure-call vector-ref.41 (unsafe-procedure-call make-vector.47 2) 0)))

  (check-equal?
    (implement-safe-call
      '(module
          (define eq?.56 (lambda (tmp.57 tmp.58) (eq? tmp.57 tmp.58)))
          (define |+.59|
          (lambda (tmp.60 tmp.61)
              (if (fixnum? tmp.61)
              (if (fixnum? tmp.60) (unsafe-fx+ tmp.60 tmp.61) (error 2))
              (error 2))))
          (define |+.62|
          (lambda (tmp.63 tmp.64)
              (if (fixnum? tmp.64)
              (if (fixnum? tmp.63) (unsafe-fx+ tmp.63 tmp.64) (error 2))
              (error 2))))
          (let ((x.1 0) (y.2 0))
          (if (call eq?.56 x.1 y.2)
              (lambda (x.1) (call |+.59| x.1 1))
              (lambda (y.2) (call |+.62| y.2 1))))))
    '(module
      (define eq?.56 (lambda (tmp.57 tmp.58) (eq? tmp.57 tmp.58)))
      (define |+.59|
          (lambda (tmp.60 tmp.61)
          (if (fixnum? tmp.61)
              (if (fixnum? tmp.60) (unsafe-fx+ tmp.60 tmp.61) (error 2))
              (error 2))))
      (define |+.62|
          (lambda (tmp.63 tmp.64)
          (if (fixnum? tmp.64)
              (if (fixnum? tmp.63) (unsafe-fx+ tmp.63 tmp.64) (error 2))
              (error 2))))
      (let ((x.1 0) (y.2 0))
          (if (unsafe-procedure-call eq?.56 x.1 y.2)
          (lambda (x.1) (unsafe-procedure-call |+.59| x.1 1))
          (lambda (y.2) (unsafe-procedure-call |+.62| y.2 1))))))
)