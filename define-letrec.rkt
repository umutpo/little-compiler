#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide define->letrec)

;; Transform all top-level bindings into local bindings.
;;
;; exprs-unsafe-lang-v9 -> just-exprs-lang-v9
(define (define->letrec p)
  
  ;; exprs-unsafe-lang-v9.Definition -> just-exprs-lang-v9.Value
  (define (define->letrec-def def)
    (match def
      [`(define ,aloc (lambda (,alocs ...) ,value))
       `(,aloc (lambda ,alocs ,value))]))

  (match p
    [`(module ,defs ... ,value)
     (let ([new-let-defs (map define->letrec-def defs)])
      (if (empty? new-let-defs)
          `(module ,value)
          `(module (letrec ,new-let-defs ,value))))]))

(module+ tests
  (check-equal?
    (define->letrec
      '(module
        (define |+.1|
          (lambda (tmp.2 tmp.3)
            (if (fixnum? tmp.3)
              (if (fixnum? tmp.2) (unsafe-fx+ tmp.2 tmp.3) (error 2))
              (error 2))))
        (unsafe-procedure-call |+.1| 5 3)))
    '(module
      (letrec ((|+.1|
                (lambda (tmp.2 tmp.3)
                  (if (fixnum? tmp.3)
                    (if (fixnum? tmp.2) (unsafe-fx+ tmp.2 tmp.3) (error 2))
                    (error 2)))))
        (unsafe-procedure-call |+.1| 5 3))))

  (check-equal?
    (define->letrec
      '(module
        (define *.21
          (lambda (tmp.22 tmp.23)
            (if (fixnum? tmp.23)
              (if (fixnum? tmp.22) (unsafe-fx* tmp.22 tmp.23) (error 1))
              (error 1))))
        *.21))
    '(module
      (letrec ((*.21
                (lambda (tmp.22 tmp.23)
                  (if (fixnum? tmp.23)
                    (if (fixnum? tmp.22) (unsafe-fx* tmp.22 tmp.23) (error 1))
                    (error 1)))))
        *.21)))
    
  (check-equal?
    (define->letrec
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
        (let ((x.1 (unsafe-procedure-call make-vector.32 5))) x.1))))

  (check-equal?
    (define->letrec
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
    '(module
      (letrec ((unsafe-vector-ref.44
                (lambda (tmp.45 tmp.46)
                  (if (unsafe-fx< tmp.46 (unsafe-vector-length tmp.45))
                    (if (unsafe-fx>= tmp.46 0)
                      (unsafe-vector-ref tmp.45 tmp.46)
                      (error 11))
                    (error 11))))
              (vector-ref.41
                (lambda (tmp.42 tmp.43)
                  (if (fixnum? tmp.43)
                    (if (vector? tmp.42)
                      (unsafe-procedure-call unsafe-vector-ref.44 tmp.42 tmp.43)
                      (error 11))
                    (error 11))))
              (vector-init-loop.49
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
              (make-init-vector.53
                (lambda (tmp.54)
                  (let ((tmp.55 (unsafe-make-vector tmp.54)))
                    (unsafe-procedure-call vector-init-loop.49 tmp.54 0 tmp.55))))
              (make-vector.47
                (lambda (tmp.48)
                  (if (fixnum? tmp.48)
                    (unsafe-procedure-call make-init-vector.53 tmp.48)
                    (error 8)))))
        (unsafe-procedure-call
        vector-ref.41
        (unsafe-procedure-call make-vector.47 2)
        0))))

  (check-equal?
    (define->letrec
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
            (lambda (x.1) (unsafe-procedure-call |+.59| x.1 1))
            (lambda (y.2) (unsafe-procedure-call |+.62| y.2 1)))))))
)