#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide uncover-free)

;; Explicitly annotate procedures with their free variable sets.
;;
;; Lam-opticon-lang-v9 -> Lam-free-lang-v9
(define (uncover-free p)

  ;; Any -> Boolean
  (define (primop? e)
    (memq e '(unsafe-fx* unsafe-fx+ unsafe-fx- eq? unsafe-fx< unsafe-fx<= unsafe-fx> unsafe-fx>=
                         fixnum? boolean? empty? void? ascii-char? error? not pair? vector? procedure? cons unsafe-car
                         unsafe-cdr unsafe-make-vector unsafe-vector-length unsafe-vector-set! unsafe-vector-ref unsafe-procedure-arity)))

  ;; (aloc (lambda (listof alocs) Lam-opticon-lang-v9.Value) (listof aloc)
  ;; -> (aloc (lambda (listof alocs) (listof alocs) Lam-free-lang-v9.Value) (listof aloc)
  (define (uncover-free-letrec e bound)
    (match e
      [`(,aloc (lambda (,lam-alocs ...) ,lam-value))
       (let-values ([(new-lam-value free) (uncover-free-value lam-value (set-add bound aloc))])
         (values
          `(,aloc (lambda ((free ,(set-subtract free lam-alocs))) ,lam-alocs ,new-lam-value))
          (set-subtract free lam-alocs)))]))

  ;; (function (listof Source Value or Effect) (listof aloc) -> (listof Target Value or Effect)
  ;; (listof Source Value or Effect)
  ;; (listof aloc)
  ;; ->
  ;; (listof Target Value or Effect) (listof aloc)
  (define (uncover-free-list f l bound)
    (define l-free '())
    (define new-l '())
    (for ([e l])
      (let-values ([(new-e e-free) (f e bound)])
        (set! l-free (set-union l-free e-free))
        (set! new-l `(,@new-l ,new-e))))
    (values new-l l-free))

  ;; Lam-opticon-lang-v9.Value (listof aloc) -> Lam-free-lang-v9.Value (listof aloc)
  (define (uncover-free-value e bound)
    (match e
      [`(unsafe-procedure-call ,value ,values^ ...)
       (let-values ([(new-value value-free) (uncover-free-value value bound)]
                    [(new-values^ values^-free) (uncover-free-list uncover-free-value values^ bound)])
         (values
          `(unsafe-procedure-call ,new-value ,@new-values^)
          (set-union value-free values^-free)))]
      [`(letrec ,proc-bindings ,value)
       (let*-values ([(new-binds binds-free) (uncover-free-list uncover-free-letrec proc-bindings bound)]
                     [(new-value value-free) (uncover-free-value value bound)])
         (values
          `(letrec (,@new-binds) ,new-value)
          (set-intersect (set-union binds-free value-free) bound)))]
      [`(let ([,alocs ,values^] ...) ,value)
       (define free '())
       (define binds '())
       (for ([aloc alocs]
             [val values^])
         (let-values ([(new-val val-free) (uncover-free-value val (set-add bound aloc))])
           (set! free (set-union free val-free))
           (set! binds `(,@binds (,aloc ,new-val)))))
       (let-values ([(new-value value-free) (uncover-free-value value bound)])
         (set! free (set-union free value-free))
         (values `(let ,binds ,new-value) (set-subtract free alocs)))]
      [`(if ,value ,value1 ,value2)
       (let-values ([(new-value value-free) (uncover-free-value value bound)]
                    [(new-value1 value1-free) (uncover-free-value value1 bound)]
                    [(new-value2 value2-free) (uncover-free-value value2 bound)])
         (values
          `(if ,new-value ,new-value1 ,new-value2)
          (set-union value-free (set-union value1-free value2-free))))]
      [`(begin ,effects ... ,value)
       (let-values ([(new-effects effects-free) (uncover-free-list uncover-free-effect effects bound)]
                    [(new-value value-free) (uncover-free-value value bound)])
         (values
          `(begin ,@new-effects ,new-value)
          (set-union value-free effects-free)))]
      [`(,primop ,values^ ...)
       #:when (primop? primop)
       (let-values ([(new-values^ values^-free) (uncover-free-list uncover-free-value values^ bound)])
         (values
          `(,primop ,@new-values^)
          values^-free))]
      [triv
       (if (aloc? triv)
           (values triv (list triv))
           (values triv (list)))]))

  ;; Lam-opticon-lang-v9.Effect (listof aloc) -> Lam-free-lang-v9.Effect (listof aloc)
  (define (uncover-free-effect e bound)
    (define free '())
    (match e
      [`(begin ,effects ...)
       (let-values ([(new-effects effects-free) (uncover-free-list uncover-free-effect effects bound)])
         (values
          `(begin ,@new-effects)
          effects-free))]
      [`(,primop ,values^ ...)
       (let-values ([(new-values^ values^-free) (uncover-free-list uncover-free-value values^ bound)])
         (values
          `(,primop ,@new-values^)
          values^-free))]))

  (match p
    [`(module ,value)
     (let-values ([(new-value _) (uncover-free-value value '())])
       `(module ,new-value))]))

(module+ tests
  
 (check-equal?
  (uncover-free
   '(module
        (letrec ([x.1 (lambda () (unsafe-procedure-call x.1))])
          x.1)))
  '(module
       (letrec ((x.1 (lambda
                         ((free (x.1)))
                       ()
                       (unsafe-procedure-call x.1))))
         x.1)))

 (check-equal?
  (uncover-free
   '(module
        (letrec ([f.1 (lambda ()
                        (letrec ([x.1 (lambda () (unsafe-procedure-call x.1))])
                          x.1))])
          f.1)))
  '(module
       (letrec ((f.1
                 (lambda ((free ()))
                   ()
                   (letrec ((x.1
                             (lambda ((free (x.1)))
                               ()
                               (unsafe-procedure-call x.1))))
                     x.1))))
         f.1)))

 (check-equal?
  (uncover-free
   '(module
        (letrec ([f.1 (lambda ()
                        (letrec ([x.1 (lambda () f.1)])
                          x.1))])
          f.1)))
  '(module
       (letrec ((f.1
                 (lambda ((free (f.1)))
                   ()
                   (letrec ((x.1 (lambda ((free (f.1))) () f.1))) x.1))))
         f.1)))

 (check-equal?
  (uncover-free
   '(module
        (letrec ([f.1 (lambda ()
                        (letrec ([x.1
                                  (lambda
                                      ()
                                    (unsafe-fx+ (unsafe-procedure-call x.1)
                                                (unsafe-procedure-call f.1)))])
                          x.1))])
          f.1)))
  '(module
       (letrec ((f.1
                 (lambda ((free (f.1)))
                   ()
                   (letrec ((x.1
                             (lambda ((free (x.1 f.1)))
                               ()
                               (unsafe-fx+
                                (unsafe-procedure-call x.1)
                                (unsafe-procedure-call f.1)))))
                     x.1))))
         f.1)))

 (check-equal?
  (uncover-free
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
  '(module
       (letrec ((|+.64|
                 (lambda ((free ()))
                   (tmp.24 tmp.25)
                   (if (fixnum? tmp.25)
                       (if (fixnum? tmp.24) (unsafe-fx+ tmp.24 tmp.25) (error 2))
                       (error 2))))
                (cons.63 (lambda ((free ())) (tmp.55 tmp.56) (cons tmp.55 tmp.56)))
                (cdr.62
                 (lambda ((free ()))
                   (tmp.44)
                   (if (pair? tmp.44) (unsafe-cdr tmp.44) (error 13))))
                (car.61
                 (lambda ((free ()))
                   (tmp.43)
                   (if (pair? tmp.43) (unsafe-car tmp.43) (error 12))))
                (eq?.60 (lambda ((free ())) (tmp.57 tmp.58) (eq? tmp.57 tmp.58)))
                (map.4
                 (lambda ((free (eq?.60 cons.63 map.4 cdr.62 car.61)))
                   (f.6 ls.5)
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
          (letrec ((lam.1
                    (lambda ((free (|+.64|)))
                      (x.7)
                      (unsafe-procedure-call |+.64| 1 x.7))))
            lam.1)
          (unsafe-procedure-call
           cons.63
           1
           (unsafe-procedure-call
            cons.63
            2
            (unsafe-procedure-call cons.63 3 empty)))))))
  )
