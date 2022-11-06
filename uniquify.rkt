#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide uniquify)

;; Resolves all lexical identifiers into unique abstract locations.
;;
;; Exprs-lang-v9 -> Exprs-unique-lang-v9
(define (uniquify p)

  ;; Any -> Boolean
  (define (prim-f? e)
    (memq e '(* + - < <= > >= eq?
                fixnum? boolean? empty? void? ascii-char? error? not
                pair? cons car cdr
                vector? make-vector vector-length vector-set! vector-ref
                procedure? procedure-arity)))

  ;; (listof Exprs-lang-v9.definition) -> (dictof name -> aloc)
  (define (collect-def-names defs)
    (define env (make-hash))
    (for ([def defs])
      (match def
        [`(define ,name ,lambda) (dict-set! env name (fresh name))]))
    env)

  ;; (listof Exprs-lang-v9.definition) -> (listof Exprs-unique-lang-v9.definition) (dictof name -> aloc)
  (define (uniquify-defs defs)
    (let* ([env (collect-def-names defs)]
           [fresh-defs (map (lambda (def) (uniquify-def def env)) defs)])
      (values fresh-defs env)))

  ;; Exprs-lang-v9.definition (dictof name -> aloc) -> Exprs-unique-lang-v9.definition
  (define (uniquify-def def env)
    (define (uniquify-def-fresh params env)
      (for/fold ([fresh-params '()]
                 [def-env (dict-copy env)])
                ([param params])
        (let ([fresh-param (fresh param)])
          (dict-set! def-env param fresh-param)
          (values (append fresh-params (list fresh-param)) def-env))))

    (match def
      [`(define ,name (lambda (,params ...) ,value))
       (let-values ([(fresh-params def-env) (uniquify-def-fresh params env)])
         `(define ,(dict-ref env name) (lambda (,@fresh-params) ,(uniquify-value value def-env))))]))

  ;; Exprs-lang-v9.Value (dictof name -> aloc) -> Exprs-unique-lang-v9.Value
  (define (uniquify-value value env)
    (match value
      [`(let ([,ids ,values] ...) ,value)
       (let-values ([(fresh-let fresh-env) (fresh-locations ids values env)])
         `(let ,fresh-let ,(uniquify-value value fresh-env)))]
      [`(if ,value ,value1 ,value2)
       `(if ,(uniquify-value value env) ,(uniquify-value value1 env) ,(uniquify-value value2 env))]
      [`(call ,value ,values ...)
       `(call ,(uniquify-value value env) ,@(map (λ (v) (uniquify-value v env)) values))]
      [triv (uniquify-triv triv env)]))

  ;; (listof symbol) (listof Exprs-lang-v9.Value) (dictof name -> aloc) -> ((listof (list symbol Exprs-unique-lang-v9.Value)) (dictof name -> aloc))
  (define (fresh-locations ids vals env)
    (define fresh-let empty)
    (let ([current_env (dict-copy env)])
      (for ([id ids]
            [val vals])
        (let* ([fresh-id (fresh id)]
               [fresh-val (uniquify-value val current_env)])
          (dict-set! env id fresh-id)
          (set! fresh-let `(,@fresh-let (,fresh-id ,fresh-val)))))
      (values fresh-let env)))

  ;; Exprs-lang-v9.Triv (dictof name -> aloc) -> Exprs-unique-lang-v9.Triv
  (define (uniquify-triv e env)
    (match e
      ['empty e]
      [#t e]
      [#f e]
      [`(void) e]
      [`(error ,uint8) e]
      [`(lambda (,params ...) ,value)
       (let ([lambda-env (dict-copy env)])
         (for ([param params])
           (dict-set! lambda-env param (fresh param)))
         `(lambda
              ,(map (λ (param) (dict-ref lambda-env param)) params)
            ,(uniquify-value value lambda-env)))]
      [fixnum #:when (int61? fixnum) e]
      [ascii-char-literal
       #:when (ascii-char-literal? ascii-char-literal)
       e]
      [x (if (prim-f? x) x (dict-ref env x))]))

  (match p
    [`(module ,defs ... ,value)
     (let-values ([(uniquified-defs env) (uniquify-defs defs)])
       `(module ,@uniquified-defs ,(uniquify-value value env)))]))

(module+ tests
  (check-equal?
   (uniquify
    '(module empty))
   '(module empty))

  (check-equal?
   (uniquify
    '(module 1))
   '(module 1))

  (check-equal?
   (uniquify
    '(module #t))
   '(module #t))

  (check-equal?
   (uniquify
    '(module #f))
   '(module #f))

  (check-equal?
   (uniquify
    '(module (void)))
   '(module (void)))

  (check-equal?
   (uniquify
    '(module (error 1)))
   '(module (error 1)))

  (check-equal?
   (uniquify
    '(module (if (call eq? (call + 5 6) 11) 4 6)))
   '(module (if (call eq? (call + 5 6) 11) 4 6)))

  (check-equal?
   (uniquify
    '(module
         (define swap
           (lambda (x y)
             (if (call < y x)
                 x
                 (call swap y x))))
       (call swap 1 2)))
   '(module
        (define swap.1
          (lambda (x.2 y.3) (if (call < y.3 x.2) x.2 (call swap.1 y.3 x.2))))
      (call swap.1 1 2)))

  (check-equal?
   (uniquify
    '(module
         (define fact
           (lambda (x)
             (if (call eq? x 0)
                 1
                 (let ((z (call + x -1)))
                   (let ((y (call fact z))) (call * x y))))))
       (call fact 10)))
   '(module
        (define fact.4
          (lambda (x.5)
            (if (call eq? x.5 0)
                1
                (let ((z.6 (call + x.5 -1)))
                  (let ((y.7 (call fact.4 z.6))) (call * x.5 y.7))))))
      (call fact.4 10)))

  (check-equal?
   (uniquify
    '(module
         (define identity
           (lambda (x)
             (if (call eq? x 0)
                 0
                 (let ((y (call - x 1)))
                   (let ((x (call identity y)))
                     (call + 1 x))))))
       (define fact
         (lambda (x)
           (let ((x (call identity x))
                 (y (call identity 0)))
             (if (call eq? x y)
                 (let ((z (call identity 1))) z)
                 (let ((n (call identity 1)))
                   (let ((z (call - x n)))
                     (let ((y (call fact z)))
                       (call * x y))))))))
       (call fact 5)))
   '(module
        (define identity.8
          (lambda (x.10)
            (if (call eq? x.10 0)
                0
                (let ((y.11 (call - x.10 1)))
                  (let ((x.12 (call identity.8 y.11))) (call + 1 x.12))))))
      (define fact.9
        (lambda (x.13)
          (let ((x.14 (call identity.8 x.13)) (y.15 (call identity.8 0)))
            (if (call eq? x.14 y.15)
                (let ((z.16 (call identity.8 1))) z.16)
                (let ((n.17 (call identity.8 1)))
                  (let ((z.18 (call - x.14 n.17)))
                    (let ((y.19 (call fact.9 z.18))) (call * x.14 y.19))))))))
      (call fact.9 5)))

  (check-equal?
   (uniquify
    '(module (call + (call + 5 6) (call * 4 5))))
   '(module (call + (call + 5 6) (call * 4 5))))

  (check-equal?
   (uniquify
    '(module (let ([x (call make-vector 5)])
               (if (call eq? (call vector-ref x 2) 0)
                   (call vector-set! x 2 1)
                   (call vector-set! x 2 -1)))))
   '(module
        (let ((x.20 (call make-vector 5)))
          (if (call eq? (call vector-ref x.20 2) 0)
              (call vector-set! x.20 2 1)
              (call vector-set! x.20 2 -1)))))

  (check-equal?
   (uniquify
    '(module
         (define map
           (lambda (f ls)
             (if (call eq? empty ls)
                 empty
                 (call
                  cons
                  (call f (call car ls))
                  (call map f (call cdr ls))))))
       (call map
             (lambda (x) (call + 1 x))
             (call cons 1 (call cons 2 (call cons 3 empty))))))
   '(module
        (define map.21
          (lambda (f.22 ls.23)
            (if (call eq? empty ls.23)
                empty
                (call
                 cons
                 (call f.22 (call car ls.23))
                 (call map.21 f.22 (call cdr ls.23))))))
      (call
       map.21
       (lambda (x.24) (call + 1 x.24))
       (call cons 1 (call cons 2 (call cons 3 empty)))))
   )
  )
