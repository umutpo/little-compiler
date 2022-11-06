#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide dox-lambdas)

;; Explicitly binds all procedures to abstract locations
;;
;; Just-exprs-lang-v9 -> Lam-opticon-lang-v9
(define (dox-lambdas p)

  ;; Any -> Boolean
  (define (primop? e)
    (memq e '(unsafe-fx* unsafe-fx+ unsafe-fx- eq? unsafe-fx< unsafe-fx<= unsafe-fx> unsafe-fx>=
                         fixnum? boolean? empty? void? ascii-char? error? not pair? vector? procedure? cons unsafe-car
                         unsafe-cdr unsafe-make-vector unsafe-vector-length unsafe-vector-set! unsafe-vector-ref unsafe-procedure-arity)))

  ;; (aloc (lambda (listof aloc) Just-exprs-lang-v9.Value)) -> (aloc (lambda (listof aloc) Lam-opticon-lang-v9.Value))
  (define (dox-lambdas-letrec e)
    (match e
      [`(,aloc (lambda (,lam-alocs ...) ,lam-value))
       `(,aloc (lambda ,lam-alocs ,(dox-lambdas-value lam-value)))]))

  ;; Just-exprs-lang-v9.Value -> Lam-opticon-lang-v9.Value
  (define (dox-lambdas-value e)
    (match e
      [`(unsafe-procedure-call ,value ,values ...)
       `(unsafe-procedure-call ,(dox-lambdas-value value) ,@(map dox-lambdas-value values))]
      [`(letrec ,proc-bindings ,value)
       `(letrec ,(map dox-lambdas-letrec proc-bindings) ,(dox-lambdas-value value))]
      [`(let ([,alocs ,values] ...) ,value)
       `(let
            ,(for/list ([aloc alocs]
                        [val values])
               `(,aloc ,(dox-lambdas-value val)))
          ,(dox-lambdas-value value))]
      [`(if ,value ,value1 ,value2)
       `(if ,(dox-lambdas-value value)
            ,(dox-lambdas-value value1)
            ,(dox-lambdas-value value2))]
      [`(begin ,effects ... ,value)
       `(begin ,@(map dox-lambdas-effect effects) ,(dox-lambdas-value value))]
      [`(,primop ,values ...)
       #:when (primop? primop)
       `(,primop ,@(map dox-lambdas-value values))]
      [triv (dox-lambdas-triv triv)]))

  ;; Just-exprs-lang-v9.Effect -> Lam-opticon-lang-v9.Effect
  (define (dox-lambdas-effect e)
    (match e
      [`(begin ,effects ...)
       `(begin ,@(map dox-lambdas-effect effects))]
      [`(,primop ,values ...)
       `(,primop ,@(map dox-lambdas-value values))]))

  ;; Just-exprs-lang-v9.Triv -> Lam-opticon-lang-v9.Triv
  (define (dox-lambdas-triv e)
    (match e
      ['empty e]
      [#t e]
      [#f e]
      [`(void) e]
      [`(error ,uint8) e]
      [`(lambda (,params ...) ,value)
       (let ([tmp (fresh `lam)])
         `(letrec ([,tmp (lambda ,params ,(dox-lambdas-value value))]) ,tmp))]
      [fixnum #:when (int61? fixnum) e]
      [ascii-char-literal
       #:when (ascii-char-literal? ascii-char-literal)
       e]
      [x e]))

  (match p
    [`(module ,value)
     `(module ,(dox-lambdas-value value))]))

(module+ tests
  (check-equal?
   (dox-lambdas
    '(module
         (letrec ((|+.64|
                   (lambda (tmp.24 tmp.25)
                     (if (fixnum? tmp.25)
                         (if (fixnum? tmp.24) (unsafe-fx+ tmp.24 tmp.25) (error 2))
                         (error 2))))
                  (cons.63 (lambda (tmp.55 tmp.56) (cons tmp.55 tmp.56)))
                  (cdr.62
                   (lambda (tmp.44)
                     (if (pair? tmp.44) (unsafe-cdr tmp.44) (error 13))))
                  (car.61
                   (lambda (tmp.43)
                     (if (pair? tmp.43) (unsafe-car tmp.43) (error 12))))
                  (eq?.60 (lambda (tmp.57 tmp.58) (eq? tmp.57 tmp.58)))
                  (map.4
                   (lambda (f.6 ls.5)
                     (if (unsafe-procedure-call eq?.60 empty ls.5)
                         empty
                         (unsafe-procedure-call
                          cons.63
                          (if (procedure? f.6)
                              (if (eq? (unsafe-procedure-arity f.6) 1)
                                  (unsafe-procedure-call
                                   f.6
                                   (unsafe-procedure-call car.61 ls.5))
                                  (error 42))
                              (error 43))
                          (unsafe-procedure-call
                           map.4
                           f.6
                           (unsafe-procedure-call cdr.62 ls.5)))))))
           (unsafe-procedure-call
            map.4
            (lambda (x.7) (unsafe-procedure-call |+.64| 1 x.7))
            (unsafe-procedure-call
             cons.63
             1
             (unsafe-procedure-call
              cons.63
              2
              (unsafe-procedure-call cons.63 3 empty)))))))
   '(module
        (letrec ((|+.64|
                  (lambda (tmp.24 tmp.25)
                    (if (fixnum? tmp.25)
                        (if (fixnum? tmp.24) (unsafe-fx+ tmp.24 tmp.25) (error 2))
                        (error 2))))
                 (cons.63 (lambda (tmp.55 tmp.56) (cons tmp.55 tmp.56)))
                 (cdr.62
                  (lambda (tmp.44)
                    (if (pair? tmp.44) (unsafe-cdr tmp.44) (error 13))))
                 (car.61
                  (lambda (tmp.43)
                    (if (pair? tmp.43) (unsafe-car tmp.43) (error 12))))
                 (eq?.60 (lambda (tmp.57 tmp.58) (eq? tmp.57 tmp.58)))
                 (map.4
                  (lambda (f.6 ls.5)
                    (if (unsafe-procedure-call eq?.60 empty ls.5)
                        empty
                        (unsafe-procedure-call
                         cons.63
                         (if (procedure? f.6)
                             (if (eq? (unsafe-procedure-arity f.6) 1)
                                 (unsafe-procedure-call
                                  f.6
                                  (unsafe-procedure-call car.61 ls.5))
                                 (error 42))
                             (error 43))
                         (unsafe-procedure-call
                          map.4
                          f.6
                          (unsafe-procedure-call cdr.62 ls.5)))))))
          (unsafe-procedure-call
           map.4
           (letrec ((lam.1 (lambda (x.7) (unsafe-procedure-call |+.64| 1 x.7))))
             lam.1)
           (unsafe-procedure-call
            cons.63
            1
            (unsafe-procedure-call
             cons.63
             2
             (unsafe-procedure-call cons.63 3 empty)))))))
  )
