#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide hoist-lambdas)

;; Exercise 10
;; Hoists code to the top-level definitions
;; closure-lang-v9 -> hoisted-lang-v9
(define (hoist-lambdas p)
  (define new-defines '())

  ;; Any -> Boolean
  (define (primop? e)
     (memq e '(unsafe-fx* unsafe-fx+ unsafe-fx- eq? unsafe-fx< unsafe-fx<= unsafe-fx> unsafe-fx>=
                          fixnum? boolean? empty? void? ascii-char? error? not pair? vector? procedure? cons unsafe-car
                          unsafe-cdr unsafe-make-vector unsafe-vector-length unsafe-vector-set! unsafe-vector-ref unsafe-procedure-arity)))

  ;; closure-lang-v9.Effect -> hoisted-lang-v9.Effect
  (define (hoist-lambdas-effect e)
    (match e
      [`(begin ,effects ...) `(begin ,@(hoist-lambdas--loe effects))]
      [`(,primop ,values ...) `(,primop ,@(hoist-lambdas--lov values))]))

  ;; (listof closure-lang-v9.Effect) -> (listof hoisted-lang-v9.Effect)
  (define (hoist-lambdas--loe loe)
    (map hoist-lambdas-effect loe))

  ;; (listof closure-lang-v9.Value) -> (listof hoisted-lang-v9.Value)
  (define (hoist-lambdas--lov lov)
    (map hoist-lambdas-value lov))

  ;; Label (listof aloc) hoisted-lang-v9.Value
  (define (add-define! label args body)
    (set! new-defines (cons `(define ,label (lambda ,args ,body)) new-defines)))

  ;; closure-lang-v9.Value -> hoisted-lang-v9.Value
  (define (hoist-lambdas-value v)
    (match v
      [`(letrec ([,labels (lambda (,args ...) ,body-values)] ...) ,value)
       (let ([body-values (hoist-lambdas--lov body-values)])
         (for-each add-define! labels args body-values)
         (hoist-lambdas-value value))]
      [`(cletrec ([,alocs (make-closure ,labels ,lens ,values ...)] ...) ,value)
       `(cletrec ,(for/list ([aloc alocs]
                             [label labels]
                             [len lens]
                             [val values])
                    `(,aloc (make-closure ,label ,len ,@(hoist-lambdas--lov val))))
                 ,(hoist-lambdas-value value))]
      [`(closure-ref ,value_c ,value_i)
       `(closure-ref ,(hoist-lambdas-value value_c) ,(hoist-lambdas-value value_i))]
      [`(closure-call ,value_c ,values ...)
       `(closure-call ,(hoist-lambdas-value value_c) ,@(hoist-lambdas--lov values))]
      [`(call ,value ,values ...)
       `(call ,(hoist-lambdas-value value) ,@(hoist-lambdas--lov values))]
      [`(let ([,alocs ,values] ...) ,value)
       `(let ,(for/list ([aloc alocs]
                         [val values])
                `[,aloc ,(hoist-lambdas-value val)])
          ,(hoist-lambdas-value value))]
      [`(if ,value_p ,value_1 ,value_2)
       `(if ,(hoist-lambdas-value value_p) ,(hoist-lambdas-value value_1) ,(hoist-lambdas-value value_2))]
      [`(begin ,effects ... ,value)
       `(begin ,@(hoist-lambdas--loe effects) ,(hoist-lambdas-value value))]
      [`(,primop ,values ...)
       #:when (primop? primop)
       `(,primop ,@(hoist-lambdas--lov values))]
      [triv triv]))

  (match p
    [`(module ,value)
     (let ([value (hoist-lambdas-value value)])
       `(module ,@new-defines ,value))]))


;; Tests

(module+ tests
  (check-equal?
   (hoist-lambdas
    '(module
         (letrec ((L.x.1.7
                   (lambda (c.4)
                     (let ((x.1 (closure-ref c.4 0))) (call L.x.1.7 x.1)))))
           (cletrec
            ((x.1 (make-closure L.x.1.7 0 x.1)) (y.1 (make-closure L.x.1.9 0 y.1)))
            x.1)))
    )
   '(module
        (define L.x.1.7
          (lambda (c.4) (let ((x.1 (closure-ref c.4 0))) (call L.x.1.7 x.1))))
      (cletrec
       ((x.1 (make-closure L.x.1.7 0 x.1)) (y.1 (make-closure L.x.1.9 0 y.1)))
       x.1)))

  (check-equal?
   (hoist-lambdas
    '(module
         (letrec ((L.x.1.7
                   (lambda (c.4)
                     (let ((x.1 (closure-ref c.4 0))) (call L.x.1.7 x.1)))))
           (cletrec
            ((x.1 (make-closure L.x.1.7 0 x.1)) (y.1 (make-closure L.x.1.9 0 y.1)))
            x.1))))
   '(module
        (define L.x.1.7
          (lambda (c.4) (let ((x.1 (closure-ref c.4 0))) (call L.x.1.7 x.1))))
      (cletrec
       ((x.1 (make-closure L.x.1.7 0 x.1)) (y.1 (make-closure L.x.1.9 0 y.1)))
       x.1)))

  (check-equal?
   (hoist-lambdas
    '(module
         (letrec ((L.cdr.361.90
                   (lambda (c.572 tmp.362)
                     (let () (if (pair? tmp.362) (unsafe-cdr tmp.362) (error 13)))))
                  (L.cons.363.91
                   (lambda (c.573 tmp.364 tmp.365) (let () (cons tmp.364 tmp.365)))))
           (cletrec
            ((cdr.361 (make-closure L.cdr.361.90 1))
             (cons.363 (make-closure L.cons.363.91 2)))
            (closure-call
             cdr.361
             cdr.361
             (closure-call cons.363 cons.363 7 empty))))))
   '(module
        (define L.cons.363.91
          (lambda (c.573 tmp.364 tmp.365) (let () (cons tmp.364 tmp.365))))
      (define L.cdr.361.90
        (lambda (c.572 tmp.362)
          (let () (if (pair? tmp.362) (unsafe-cdr tmp.362) (error 13)))))
      (cletrec
       ((cdr.361 (make-closure L.cdr.361.90 1))
        (cons.363 (make-closure L.cons.363.91 2)))
       (closure-call cdr.361 cdr.361 (closure-call cons.363 cons.363 7 empty))))))