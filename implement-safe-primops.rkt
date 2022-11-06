#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide implement-safe-primops)

;; Implements safe primitive operations by inserting procedure definitions for
;; each primitive operation which perform dynamic tag checking, to ensure type safety.
;;
;; Error Codes:
;; 1 -> Error in * operation parameter data types
;; 2 -> Error in + operation parameter data types
;; 3 -> Error in - operation parameter data types
;; 4 -> Error in < operation parameter data types
;; 5 -> Error in <= operation parameter data types
;; 6 -> Error in > operation parameter data types
;; 7 -> Error in <= operation parameter data types
;; 8 -> Error in eq? operation parameter data types
;; 9 -> Error in make-vector operation parameter data types
;; 10 -> Error in vector-length operation parameter data types
;; 11 -> Error in vector-set! operation parameter data types
;; 12 -> Error in vector-ref operation parameter data types
;; 13 -> Error in car operation parameter data types
;; 14 -> Error in cdr operation parameter data types
;;
;; exprs-unique-lang-v9 -> exprs-unsafe-data-lang-v9
(define (implement-safe-primops p)
  (define added-defs '())

  (define prim-f-specs
    `((* unsafe-fx* (fixnum? fixnum?))
      (+ unsafe-fx+ (fixnum? fixnum?))
      (- unsafe-fx- (fixnum? fixnum?))
      (< unsafe-fx< (fixnum? fixnum?))
      (<= unsafe-fx<= (fixnum? fixnum?))
      (> unsafe-fx> (fixnum? fixnum?))
      (>= unsafe-fx>= (fixnum? fixnum?))

      (make-vector make-init-vector (fixnum?))
      (vector-length unsafe-vector-length (vector?))
      (vector-set! unsafe-vector-set! (vector? fixnum? any?))
      (vector-ref unsafe-vector-ref (vector? fixnum?))

      (car unsafe-car (pair?))
      (cdr unsafe-cdr (pair?))
      (procedure-arity unsafe-procedure-arity (procedure?))

      ,@(map (lambda (x) `(,x ,x (any?)))
             '(fixnum? boolean? empty? void? ascii-char? error? pair?
                       vector? not procedure?))
      ,@(map (lambda (x) `(,x ,x (any? any?)))
             '(cons eq?))))

  (define prim-fs (map (lambda (p) (car p)) prim-f-specs))

  ;; exprs-unique-lang-v7.Triv -> Boolean
  (define (lambda? triv)
    (match triv
      [`(lambda (,alocs ...) ,value) #t]
      [_ #f]))

  ;; exprs-unique-lang-v7.Triv -> exprs-unsafe-data-lang-v9.Triv
  (define (implement-safe-primops-lambda triv)
    (match triv
      [`(lambda (,alocs ...) ,value) `(lambda ,alocs ,(implement-safe-primops-value value))]))

  ;; exprs-unique-lang-v9.Primop -> Natural
  (define (get-error-code called)
    (+ (- (length prim-fs) (length (member called prim-fs))) 1))

  ;; exprs-unsafe-data-lang-v9.Prim-op (listof aloc) -> exprs-unsafe-data-lang-v9.Value
  (define (implement-safe-primops-typed--make-init-vector primop new-params)
    (let* ([vector-init-loop-label (fresh `tmp)]
           [vector-init-loop-len (fresh `len)]
           [vector-init-loop-index (fresh `i)]
           [vector-init-loop-vector (fresh `vec)]
           [vector-init-loop-def `(define ,vector-init-loop-label
                                    (lambda (,vector-init-loop-len ,vector-init-loop-index ,vector-init-loop-vector)
                                      (if (eq? ,vector-init-loop-len ,vector-init-loop-index)
                                          ,vector-init-loop-vector
                                          (begin
                                            (unsafe-vector-set! ,vector-init-loop-vector ,vector-init-loop-index 0)
                                            (call ,vector-init-loop-label ,vector-init-loop-len (unsafe-fx+ ,vector-init-loop-index 1) ,vector-init-loop-vector)))))]
           [make-init-vector-label (fresh `tmp)]
           [make-init-vector-tmp1 (fresh `tmp)]
           [make-init-vector-tmp2 (fresh `tmp)]
           [make-init-vector-def `(define ,make-init-vector-label
                                    (lambda (,make-init-vector-tmp1)
                                      (let ((,make-init-vector-tmp2 (unsafe-make-vector ,make-init-vector-tmp1)))
                                        (call ,vector-init-loop-label ,make-init-vector-tmp1 0 ,make-init-vector-tmp2))))])
      (set! added-defs (append added-defs (list vector-init-loop-def)))
      (set! added-defs (append added-defs (list make-init-vector-def)))
      `(call ,make-init-vector-label ,@new-params)))

  ;; exprs-unsafe-data-lang-v9.Prim-op (listof aloc) -> exprs-unsafe-data-lang-v9.Value
  (define (implement-safe-primops-typed--unsafe-vector-set primop new-params)
    (let* ([unsafe-vector-set-label (fresh `tmp)]
           [unsafe-vector-set-tmp1 (fresh `tmp)]
           [unsafe-vector-set-tmp2 (fresh `tmp)]
           [unsafe-vector-set-tmp3 (fresh `tmp)]
           [unsafe-vector-set-def `(define ,unsafe-vector-set-label
                                     (lambda (,unsafe-vector-set-tmp1 ,unsafe-vector-set-tmp2 ,unsafe-vector-set-tmp3)
                                       (if (unsafe-fx< ,unsafe-vector-set-tmp2 (unsafe-vector-length ,unsafe-vector-set-tmp1))
                                           (if (unsafe-fx>= ,unsafe-vector-set-tmp2 0)
                                               (begin (unsafe-vector-set! ,unsafe-vector-set-tmp1 ,unsafe-vector-set-tmp2 ,unsafe-vector-set-tmp3) (void))
                                               (error 10))
                                           (error 10))))])
      (set! added-defs (append added-defs (list unsafe-vector-set-def)))
      `(call ,unsafe-vector-set-label ,@new-params)))

  ;; exprs-unsafe-data-lang-v9.Prim-op (listof aloc) -> exprs-unsafe-data-lang-v9.Value
  (define (implement-safe-primops-typed--unsafe-vector-ref primop new-params)
    (let* ([unsafe-vector-ref-label (fresh `tmp)]
           [unsafe-vector-ref-tmp1 (fresh `tmp)]
           [unsafe-vector-ref-tmp2 (fresh `tmp)]
           [unsafe-vector-ref-def `(define ,unsafe-vector-ref-label
                                     (lambda (,unsafe-vector-ref-tmp1 ,unsafe-vector-ref-tmp2)
                                       (if (unsafe-fx< ,unsafe-vector-ref-tmp2 (unsafe-vector-length ,unsafe-vector-ref-tmp1))
                                           (if (unsafe-fx>= ,unsafe-vector-ref-tmp2 0)
                                               (unsafe-vector-ref ,unsafe-vector-ref-tmp1 ,unsafe-vector-ref-tmp2)
                                               (error 11))
                                           (error 11))))])
      (set! added-defs (append added-defs (list unsafe-vector-ref-def)))
      `(call ,unsafe-vector-ref-label ,@new-params)))

  ;; exprs-unsafe-data-lang-v9.Prim-op (listof aloc) -> exprs-unsafe-data-lang-v9.Value
  (define (implement-safe-primops-typed--call prim-op new-params)
    (match prim-op
      [`make-init-vector (implement-safe-primops-typed--make-init-vector prim-op new-params)]
      [`unsafe-vector-set! (implement-safe-primops-typed--unsafe-vector-set prim-op new-params)]
      [`unsafe-vector-ref (implement-safe-primops-typed--unsafe-vector-ref prim-op new-params)]
      [_ `(,prim-op ,@new-params)]))

  ;; (listof Parameter-types) (listof aloc) exprs-unique-lang-v9.Value Natural
  ;;                                                            -> exprs-unsafe-data-lang-v9.Value
  (define (implement-safe-primops-typed--ifs params param-names primop-value error-code)
    (cond
      [(empty? params) primop-value]
      [(equal? (first params) `any?) (implement-safe-primops-typed--ifs (rest params) (rest param-names) primop-value error-code)]
      [else
       `(if (,(first params) ,(first param-names))
            ,(implement-safe-primops-typed--ifs (rest params) (rest param-names) primop-value error-code)
            (error ,error-code))]))

  ;; exprs-unique-lang-v9.Prim-f exprs-unsafe-data-lang-v9.Prim-op (listof Parameter-types)
  ;;                                                            -> exprs-unsafe-data-lang-v9.Label
  (define (implement-safe-primops-typed prim-f prim-op params)
    (let* ([new-label (fresh 'tmp)]
           [new-params (map (lambda (p) (fresh 'tmp)) params)]
           [error-code (get-error-code prim-f)]
           [new-def `(define ,new-label
                       (lambda (,@new-params)
                         ,(implement-safe-primops-typed--ifs (reverse params)
                                                             (reverse new-params)
                                                             (implement-safe-primops-typed--call prim-op new-params)
                                                             error-code)))])
      (set! added-defs (append added-defs (list new-def)))
      new-label))

  ;; exprs-unique-lang-v9.Prim-f exprs-unsafe-data-lang-v9.Prim-op (listof Parameter-types)
  ;;                                                            -> exprs-unsafe-data-lang-v9.Label
  (define (implement-safe-primops-any prim-f prim-op params)
    (let* ([new-label (fresh 'tmp)]
           [new-params (map (lambda (p) (fresh 'tmp)) params)]
           [new-def `(define ,new-label
                       (lambda (,@new-params)
                         ,(implement-safe-primops-typed--call prim-op new-params)))])
      (set! added-defs (append added-defs (list new-def)))
      new-label))

  ;; `(exprs-unique-lang-v9.Prim-f exprs-unsafe-data-lang-v9.Prim-op (listof Parameter-types))
  ;;                                                            -> exprs-unsafe-data-lang-v9.Label
  (define (implement-safe-primops-prim-f prim-f-spec)
    (match prim-f-spec
      [`(,prim-f ,prim-op ,params)
       (if (equal? 'any? (first params))
           (implement-safe-primops-any prim-f prim-op params)
           (implement-safe-primops-typed prim-f prim-op params))]))

  ;; exprs-unique-lang-v9.Triv -> exprs-unsafe-data-lang-v9.Triv
  (define (implement-safe-primops-triv triv)
    (cond
      [(memq triv prim-fs)
       (implement-safe-primops-prim-f (findf (lambda (p) (equal? (car p) triv)) prim-f-specs))]
      [(lambda? triv) (implement-safe-primops-lambda triv)]
      [else triv]))

  ;; exprs-unique-lang-v9.Value -> exprs-unsafe-data-lang-v9.Value
  (define (implement-safe-primops-value value)
    (match value
      [`(call ,v ,vs ...)
       `(call ,(implement-safe-primops-value v) ,@(map implement-safe-primops-value vs))]
      [`(let ([,alocs ,vs] ...) ,val)
       `(let ,(map (lambda (aloc v) `(,aloc ,(implement-safe-primops-value v))) alocs vs)
          ,(implement-safe-primops-value val))]
      [`(if ,v1 ,v2 ,v3)
       `(if ,(implement-safe-primops-value v1)
            ,(implement-safe-primops-value v2)
            ,(implement-safe-primops-value v3))]
      [triv (implement-safe-primops-triv triv)]))

  ;; exprs-unique-lang-v9.Definition -> exprs-unsafe-data-lang-v9.Definition
  (define (implement-safe-primops-def def)
    (match def
      [`(define ,label (lambda (,params ...) ,value))
       `(define ,label (lambda ,params ,(implement-safe-primops-value value)))]))

  (match p
    [`(module ,defs ... ,value)
     (let ([module-value (implement-safe-primops-value value)]
           [new-defs (map implement-safe-primops-def defs)])
       `(module ,@(append added-defs new-defs)
          ,module-value))]))

(module+ tests
  (check-equal?
    (implement-safe-primops
    '(module (call + 5 3)))
    '(module
      (define tmp.1
        (lambda (tmp.2 tmp.3)
          (if (fixnum? tmp.3)
            (if (fixnum? tmp.2) (unsafe-fx+ tmp.2 tmp.3) (error 2))
            (error 2))))
      (call tmp.1 5 3)))

  (check-equal?
    (implement-safe-primops
      '(module
          (define mul.1
            (lambda (x.1 y.2)
              (call * x.1 y.2)))
        (let ([t.3 5]
              [k.4 10])
          (call mul.1 t.3 k.4))))
    '(module
      (define tmp.4
        (lambda (tmp.5 tmp.6)
          (if (fixnum? tmp.6)
            (if (fixnum? tmp.5) (unsafe-fx* tmp.5 tmp.6) (error 1))
            (error 1))))
      (define mul.1 (lambda (x.1 y.2) (call tmp.4 x.1 y.2)))
      (let ((t.3 5) (k.4 10)) (call mul.1 t.3 k.4))))

  (check-equal?
    (implement-safe-primops
      '(module
            (define greater.1
              (lambda (x.1 y.2)
                (if (call < x.1 y.2)
                    #t
                    #f)))
          (let ([t.3 5]
                [k.4 10])
            (if (call greater.1 t.3 k.4)
                (call + t.3 k.4)
                (call - k.4 t.3)))))
    '(module
      (define tmp.7
        (lambda (tmp.8 tmp.9)
          (if (fixnum? tmp.9)
            (if (fixnum? tmp.8) (unsafe-fx+ tmp.8 tmp.9) (error 2))
            (error 2))))
      (define tmp.10
        (lambda (tmp.11 tmp.12)
          (if (fixnum? tmp.12)
            (if (fixnum? tmp.11) (unsafe-fx- tmp.11 tmp.12) (error 3))
            (error 3))))
      (define tmp.13
        (lambda (tmp.14 tmp.15)
          (if (fixnum? tmp.15)
            (if (fixnum? tmp.14) (unsafe-fx< tmp.14 tmp.15) (error 4))
            (error 4))))
      (define greater.1 (lambda (x.1 y.2) (if (call tmp.13 x.1 y.2) #t #f)))
      (let ((t.3 5) (k.4 10))
        (if (call greater.1 t.3 k.4) (call tmp.7 t.3 k.4) (call tmp.10 k.4 t.3)))))

  (check-equal?
    (implement-safe-primops
      '(module
            (let ([t.3 5]
                  [k.4 #t])
              (if (call error? (call + t.3 k.4))
                  (void)
                  t.3))))
    '(module
      (define tmp.16 (lambda (tmp.17) (error? tmp.17)))
      (define tmp.18
        (lambda (tmp.19 tmp.20)
          (if (fixnum? tmp.20)
            (if (fixnum? tmp.19) (unsafe-fx+ tmp.19 tmp.20) (error 2))
            (error 2))))
      (let ((t.3 5) (k.4 #t))
        (if (call tmp.16 (call tmp.18 t.3 k.4)) (void) t.3))))

  (check-equal?
    (implement-safe-primops
      '(module *))
    '(module
      (define tmp.21
        (lambda (tmp.22 tmp.23)
          (if (fixnum? tmp.23)
            (if (fixnum? tmp.22) (unsafe-fx* tmp.22 tmp.23) (error 1))
            (error 1))))
      tmp.21))

  (check-equal?
    (implement-safe-primops
      '(module
          (define add.1
            (lambda (x.1 y.2 z.3)
              (call + x.1 y.2 z.3)))
        (let ([t.3 5]
              [k.4 10]
              [m.5 15])
        (call add.1 t.3 k.4 m.5))))
    '(module
      (define tmp.24
        (lambda (tmp.25 tmp.26)
          (if (fixnum? tmp.26)
            (if (fixnum? tmp.25) (unsafe-fx+ tmp.25 tmp.26) (error 2))
            (error 2))))
      (define add.1 (lambda (x.1 y.2 z.3) (call tmp.24 x.1 y.2 z.3)))
      (let ((t.3 5) (k.4 10) (m.5 15)) (call add.1 t.3 k.4 m.5))))

  (check-equal?
    (implement-safe-primops
      '(module 
          (let ([x.1 (call cons 5 10)])
            (call car x.1))))
    '(module
      (define tmp.27 (lambda (tmp.28 tmp.29) (cons tmp.28 tmp.29)))
      (define tmp.30
        (lambda (tmp.31) (if (pair? tmp.31) (unsafe-car tmp.31) (error 12))))
      (let ((x.1 (call tmp.27 5 10))) (call tmp.30 x.1))))

  (check-equal?
    (implement-safe-primops
      '(module 
          (let ([x.1 (call make-vector 5)])
            x.1)))
    '(module
      (define tmp.34
        (lambda (len.35 i.36 vec.37)
          (if (eq? len.35 i.36)
            vec.37
            (begin
              (unsafe-vector-set! vec.37 i.36 0)
              (call tmp.34 len.35 (unsafe-fx+ i.36 1) vec.37)))))
      (define tmp.38
        (lambda (tmp.39)
          (let ((tmp.40 (unsafe-make-vector tmp.39)))
            (call tmp.34 tmp.39 0 tmp.40))))
      (define tmp.32
        (lambda (tmp.33)
          (if (fixnum? tmp.33) (call tmp.38 tmp.33) (error 8))))
      (let ((x.1 (call tmp.32 5))) x.1)))

  (check-equal?
    (implement-safe-primops
      '(module (call vector-ref (call make-vector 2) 0)))
    '(module
      (define tmp.44
        (lambda (tmp.45 tmp.46)
          (if (unsafe-fx< tmp.46 (unsafe-vector-length tmp.45))
            (if (unsafe-fx>= tmp.46 0)
              (unsafe-vector-ref tmp.45 tmp.46)
              (error 11))
            (error 11))))
      (define tmp.41
        (lambda (tmp.42 tmp.43)
          (if (fixnum? tmp.43)
            (if (vector? tmp.42)
              (call tmp.44 tmp.42 tmp.43)
              (error 11))
            (error 11))))
      (define tmp.49
        (lambda (len.50 i.51 vec.52)
          (if (eq? len.50 i.51)
            vec.52
            (begin
              (unsafe-vector-set! vec.52 i.51 0)
              (call tmp.49 len.50 (unsafe-fx+ i.51 1) vec.52)))))
      (define tmp.53
        (lambda (tmp.54)
          (let ((tmp.55 (unsafe-make-vector tmp.54)))
            (call tmp.49 tmp.54 0 tmp.55))))
      (define tmp.47
        (lambda (tmp.48)
          (if (fixnum? tmp.48) (call tmp.53 tmp.48) (error 8))))
      (call tmp.41 (call tmp.47 2) 0)))

  (check-equal?
    (implement-safe-primops
      '(module (let ([x.1 0]
                    [y.2 0])
                (if (call eq? x.1 y.2)
                    (lambda (x.1) (call + x.1 1))
                    (lambda (y.2) (call + y.2 1))))))
    '(module
      (define tmp.56 (lambda (tmp.57 tmp.58) (eq? tmp.57 tmp.58)))
      (define tmp.59
        (lambda (tmp.60 tmp.61)
          (if (fixnum? tmp.61)
            (if (fixnum? tmp.60) (unsafe-fx+ tmp.60 tmp.61) (error 2))
            (error 2))))
      (define tmp.62
        (lambda (tmp.63 tmp.64)
          (if (fixnum? tmp.64)
            (if (fixnum? tmp.63) (unsafe-fx+ tmp.63 tmp.64) (error 2))
            (error 2))))
      (let ((x.1 0) (y.2 0))
        (if (call tmp.56 x.1 y.2)
          (lambda (x.1) (call tmp.59 x.1 1))
          (lambda (y.2) (call tmp.62 y.2 1))))))
)