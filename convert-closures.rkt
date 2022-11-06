#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide convert-closures)

;; Performs closure conversion, converting all procedures into explicit closures.
;;
;; Lam-free-lang-v9 -> Closure-lang-v9
(define (convert-closures p)

  ;; Any -> Boolean
  (define (primop? e)
    (memq e '(unsafe-fx* unsafe-fx+ unsafe-fx- eq? unsafe-fx< unsafe-fx<= unsafe-fx> unsafe-fx>=
                         fixnum? boolean? empty? void? ascii-char? error? not pair? vector? procedure? cons unsafe-car
                         unsafe-cdr unsafe-make-vector unsafe-vector-length unsafe-vector-set! unsafe-vector-ref unsafe-procedure-arity)))

  ;; label (listof aloc) Lam-free-lang-v9.Value (listof aloc)
  ;; -> (label (lambda (listof aloc) Closure-lang-v9.Value))
  (define (convert-closures-letrec-lambda lam-label lam-alocs lam-value free)
    (let ([c (fresh `c)]
          [new-lam-value (convert-closures-value lam-value)])
      `(,lam-label
        (lambda (,c ,@lam-alocs)
          (let ,(create-closure-ref c free)
            ,new-lam-value)))))

  ;; aloc label (listof alocs) (listof alocs) -> (aloc Closure-lang-v9.Value)
  (define (convert-closures-letrec-cletrec aloc label lam-alocs free)
    `(,aloc (make-closure ,label ,(length lam-alocs) ,@free)))

  ;; aloc label (listof alocs) (listof alocs) Lam-free-lang-v9.Value
  ;; -> Closure-lang-v9.Value Closure-lang-v9.Value
  (define (convert-closures-letrec-f aloc lam-label lam-alocs free lam-value)
    (values
     (convert-closures-letrec-lambda lam-label lam-alocs lam-value free)
     (convert-closures-letrec-cletrec aloc lam-label lam-alocs free)))

  ;; (listof (aloc (lambda (listof aloc) Lam-free-lang-v9.Value)))
  ;; -> (listof alocs) (listof labels) (listof (listof alocs))
  ;;    (listof (listof alocs)) (listof Lam-free-lang-v9.Value) 
  (define (collect-letrec-info proc-bindings)
    (define aloc-l '())
    (define label-l '())
    (define lam-alocs-l '())
    (define free-l '())
    (define lam-value-l '())
    (for ([proc proc-bindings])
      (match proc
        [`(,aloc (lambda ,info (,lam-alocs ...) ,lam-value))
         (set! aloc-l `(,@aloc-l ,aloc))
         (set! label-l `(,@label-l ,(fresh-label aloc)))
         (set! lam-alocs-l `(,@lam-alocs-l ,lam-alocs))
         (set! free-l `(,@free-l ,(info-ref info `free)))
         (set! lam-value-l `(,@lam-value-l ,lam-value))]))
    (values aloc-l label-l lam-alocs-l free-l lam-value-l))

  ;; (listof (aloc (lambda (listof aloc) Lam-free-lang-v9.Value))) Lam-free-lang-v9.Value
  ;; -> Closure-lang-v9.Value
  (define (convert-closures-letrec proc-bindings value)
    (let*-values ([(alocs labels lam-alocs-l free-l lam-values) (collect-letrec-info proc-bindings)]
                  [(letrec-binds letrec-closures) (map2 convert-closures-letrec-f
                                                        alocs
                                                        labels
                                                        lam-alocs-l
                                                        free-l
                                                        lam-values)])
      `(letrec ,letrec-binds (cletrec ,letrec-closures ,(convert-closures-value value)))))

  ;; aloc (listof aloc) -> Closure-lang-v9.Value
  (define (create-closure-ref c free)
    (for/list ([x free]
               [i (length free)])
      `(,x (closure-ref ,c ,i))))

  ;; Lam-free-lang-v9.Value -> Closure-lang-v9.Value
  (define (convert-closures-value e)
    (match e
      [`(unsafe-procedure-call ,value ,values ...)
       (if (aloc? value)
           `(closure-call ,value ,value ,@(map convert-closures-value values))
           (let ([tmp (fresh)]
                 [new-value (convert-closures-value value)])
             `(let ((,tmp ,new-value))
                (closure-call ,tmp ,tmp ,@(map convert-closures-value values)))))]
      [`(letrec ,proc-bindings ,value)
       (convert-closures-letrec proc-bindings value)]
      [`(let ([,alocs ,values] ...) ,value)
       `(let ,(map (λ (aloc val) `(,aloc ,(convert-closures-value val))) alocs values)
          ,(convert-closures-value value))]
      [`(if ,value ,value1 ,value2)
       `(if ,(convert-closures-value value)
            ,(convert-closures-value value1)
            ,(convert-closures-value value2))]
      [`(begin ,effects ... ,value)
       `(begin ,@(map convert-closures-effect effects) ,(convert-closures-value value))]
      [`(,primop ,values ...)
       #:when (primop? primop)
       `(,primop ,@(map convert-closures-value values))]
      [triv e]))

  ;; Lam-free-lang-v9.Effect -> Closure-lang-v9.Effect
  (define (convert-closures-effect e)
    (match e
      [`(begin ,effects ...)
       `(begin ,@(map convert-closures-effect effects))]
      [`(,primop ,values ...)
       `(,primop ,@(map convert-closures-value values))]))

  (match p
    [`(module ,value)
     `(module ,(convert-closures-value value))]))

(module+ tests
  (check-equal?
   (convert-closures
    '(module
         (letrec ((x.1 (lambda
                           ((free (x.1)))
                         ()
                         (unsafe-procedure-call x.1))))
           x.1)))
   '(module
        (letrec ((L.x.1.1
                  (lambda (c.1)
                    (let ((x.1 (closure-ref c.1 0)))
                      (closure-call x.1 x.1)))))
          (cletrec ((x.1 (make-closure L.x.1.1 0 x.1))) x.1))))

  (check-equal?
   (convert-closures
    '(module
         (letrec ((x.1 (lambda
                           ((free (x.1)))
                         ()
                         (unsafe-procedure-call x.1)))
                  (y.1 (lambda
                           ((free (y.1)))
                         ()
                         (unsafe-procedure-call y.1))))
           x.1)))
   '(module
        (letrec ((L.x.1.2
                  (lambda (c.2)
                    (let ((x.1 (closure-ref c.2 0))) (closure-call x.1 x.1))))
                 (L.y.1.3
                  (lambda (c.3)
                    (let ((y.1 (closure-ref c.3 0))) (closure-call y.1 y.1)))))
          (cletrec
           ((x.1 (make-closure L.x.1.2 0 x.1)) (y.1 (make-closure L.y.1.3 0 y.1)))
           x.1))))

  (check-equal?
   (convert-closures
    '(module
         (letrec ((x.1 (lambda
                           ((free (x.1)))
                         ()
                         (unsafe-procedure-call x.1 x.1))))
           x.1)))
   '(module
        (letrec ((L.x.1.4
                  (lambda (c.4)
                    (let ((x.1 (closure-ref c.4 0)))
                      (closure-call x.1 x.1 x.1)))))
          (cletrec ((x.1 (make-closure L.x.1.4 0 x.1))) x.1))))

  (check-equal?
   (convert-closures
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
   '(module
        (letrec ((L.f.1.5
                  (lambda (c.5)
                    (let ()
                      (letrec ((L.x.1.6
                                (lambda (c.6)
                                  (let ((x.1 (closure-ref c.6 0)))
                                    (closure-call x.1 x.1)))))
                        (cletrec ((x.1 (make-closure L.x.1.6 0 x.1))) x.1))))))
          (cletrec ((f.1 (make-closure L.f.1.5 0))) f.1))))

  (check-equal?
   (convert-closures
    '(module
         (letrec ((f.1
                   (lambda ((free (f.1)))
                     ()
                     (letrec ((x.1 (lambda ((free (f.1))) () f.1))) x.1))))
           f.1)))
   '(module
        (letrec ((L.f.1.7
                  (lambda (c.7)
                    (let ((f.1 (closure-ref c.7 0)))
                      (letrec ((L.x.1.8
                                (lambda (c.8)
                                  (let ((f.1 (closure-ref c.8 0))) f.1))))
                        (cletrec ((x.1 (make-closure L.x.1.8 0 f.1))) x.1))))))
          (cletrec ((f.1 (make-closure L.f.1.7 0 f.1))) f.1))))

  (check-equal?
   (convert-closures
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
   '(module
        (letrec ((L.f.1.9
                  (lambda (c.9)
                    (let ((f.1 (closure-ref c.9 0)))
                      (letrec ((L.x.1.10
                                (lambda (c.10)
                                  (let ((x.1 (closure-ref c.10 0))
                                        (f.1 (closure-ref c.10 1)))
                                    (unsafe-fx+
                                     (closure-call x.1 x.1)
                                     (closure-call f.1 f.1))))))
                        (cletrec ((x.1 (make-closure L.x.1.10 0 x.1 f.1))) x.1))))))
          (cletrec ((f.1 (make-closure L.f.1.9 0 f.1))) f.1))))

  (check-equal?
   (convert-closures
    '(module
         (letrec ((f.1
                   (lambda ((free (f.1)))
                     ()
                     (letrec ((y.1
                               (lambda ((free (x.1 f.1)))
                                 ()
                                 (unsafe-fx+
                                  (unsafe-procedure-call x.1)
                                  (unsafe-procedure-call f.1)))))
                       x.1))))
           f.1)))
   '(module
        (letrec ((L.f.1.11
                  (lambda (c.11)
                    (let ((f.1 (closure-ref c.11 0)))
                      (letrec ((L.y.1.12
                                (lambda (c.12)
                                  (let ((x.1 (closure-ref c.12 0))
                                        (f.1 (closure-ref c.12 1)))
                                    (unsafe-fx+
                                     (closure-call x.1 x.1)
                                     (closure-call f.1 f.1))))))
                        (cletrec ((y.1 (make-closure L.y.1.12 0 x.1 f.1))) x.1))))))
          (cletrec ((f.1 (make-closure L.f.1.11 0 f.1))) f.1))))

  (check-equal?
   (convert-closures
    '(module
         (letrec ((f.1
                   (lambda ((free (f.1)))
                     ()
                     (letrec ((y.1
                               (lambda ((free (x.1 f.1)))
                                 ()
                                 (unsafe-fx+
                                  (unsafe-procedure-call
                                   (letrec ((x.1
                                             (lambda ((free (x.1 f.1)))
                                               ()
                                               (unsafe-fx+
                                                (unsafe-procedure-call x.1)
                                                (unsafe-procedure-call f.1)))))
                                     y.1))
                                  (unsafe-procedure-call x.1)))))
                       f.1))))
           f.1)))
   '(module
        (letrec ((L.f.1.13
                  (lambda (c.13)
                    (let ((f.1 (closure-ref c.13 0)))
                      (letrec ((L.y.1.14
                                (lambda (c.14)
                                  (let ((x.1 (closure-ref c.14 0))
                                        (f.1 (closure-ref c.14 1)))
                                    (unsafe-fx+
                                     (let ((tmp.15
                                            (letrec ((L.x.1.15
                                                      (lambda (c.16)
                                                        (let ((x.1
                                                               (closure-ref c.16 0))
                                                              (f.1
                                                               (closure-ref c.16 1)))
                                                          (unsafe-fx+
                                                           (closure-call x.1 x.1)
                                                           (closure-call
                                                            f.1
                                                            f.1))))))
                                              (cletrec
                                               ((x.1
                                                 (make-closure L.x.1.15 0 x.1 f.1)))
                                               y.1))))
                                       (closure-call tmp.15 tmp.15))
                                     (closure-call x.1 x.1))))))
                        (cletrec ((y.1 (make-closure L.y.1.14 0 x.1 f.1))) f.1))))))
          (cletrec ((f.1 (make-closure L.f.1.13 0 f.1))) f.1))))

  (check-equal?
   (convert-closures
    '(module
         (letrec ((f.1
                   (lambda ((free (f.1)))
                     ()
                     (letrec ((y.1
                               (lambda ((free (x.1 f.1)))
                                 ()
                                 (unsafe-fx+
                                  (unsafe-procedure-call
                                   (letrec ((x.1
                                             (lambda ((free (x.1 f.1)))
                                               ()
                                               (unsafe-fx+
                                                (unsafe-procedure-call x.1)
                                                (unsafe-procedure-call f.1)))))
                                     y.1)
                                   (letrec ((x.1
                                             (lambda ((free (x.1 f.1)))
                                               ()
                                               (unsafe-fx+
                                                (unsafe-procedure-call x.1)
                                                (unsafe-procedure-call f.1)))))
                                     y.1))
                                  (unsafe-procedure-call x.1)))))
                       f.1))))
           f.1)))
   '(module
        (letrec ((L.f.1.16
                  (lambda (c.17)
                    (let ((f.1 (closure-ref c.17 0)))
                      (letrec ((L.y.1.17
                                (lambda (c.18)
                                  (let ((x.1 (closure-ref c.18 0))
                                        (f.1 (closure-ref c.18 1)))
                                    (unsafe-fx+
                                     (let ((tmp.19
                                            (letrec ((L.x.1.18
                                                      (lambda (c.20)
                                                        (let ((x.1
                                                               (closure-ref c.20 0))
                                                              (f.1
                                                               (closure-ref c.20 1)))
                                                          (unsafe-fx+
                                                           (closure-call x.1 x.1)
                                                           (closure-call
                                                            f.1
                                                            f.1))))))
                                              (cletrec
                                               ((x.1
                                                 (make-closure L.x.1.18 0 x.1 f.1)))
                                               y.1))))
                                       (closure-call
                                        tmp.19
                                        tmp.19
                                        (letrec ((L.x.1.19
                                                  (lambda (c.21)
                                                    (let ((x.1 (closure-ref c.21 0))
                                                          (f.1 (closure-ref c.21 1)))
                                                      (unsafe-fx+
                                                       (closure-call x.1 x.1)
                                                       (closure-call f.1 f.1))))))
                                          (cletrec
                                           ((x.1 (make-closure L.x.1.19 0 x.1 f.1)))
                                           y.1))))
                                     (closure-call x.1 x.1))))))
                        (cletrec ((y.1 (make-closure L.y.1.17 0 x.1 f.1))) f.1))))))
          (cletrec ((f.1 (make-closure L.f.1.16 0 f.1))) f.1))))

  (check-equal?
   (convert-closures
    '(module
         (letrec ((f.1
                   (lambda ((free (f.1)))
                     ()
                     (letrec ((y.1
                               (lambda ((free (x.1 f.1)))
                                 ()
                                 (unsafe-fx+
                                  (unsafe-procedure-call
                                   (letrec ((x.1
                                             (lambda ((free (x.1 f.1)))
                                               ()
                                               (unsafe-fx+
                                                (unsafe-procedure-call x.1)
                                                (unsafe-procedure-call f.1)))))
                                     y.1)
                                   (letrec ((x.1
                                             (lambda ((free (x.1 f.1)))
                                               ()
                                               (unsafe-fx+
                                                (unsafe-procedure-call x.1)
                                                (unsafe-procedure-call f.1)))))
                                     y.1)
                                   (letrec ((x.1
                                             (lambda ((free (x.1 f.1)))
                                               ()
                                               (unsafe-fx+
                                                (unsafe-procedure-call x.1)
                                                (unsafe-procedure-call f.1)))))
                                     y.1))
                                  (unsafe-procedure-call x.1)))))
                       f.1))))
           f.1)))
   '(module
        (letrec ((L.f.1.20
                  (lambda (c.22)
                    (let ((f.1 (closure-ref c.22 0)))
                      (letrec ((L.y.1.21
                                (lambda (c.23)
                                  (let ((x.1 (closure-ref c.23 0))
                                        (f.1 (closure-ref c.23 1)))
                                    (unsafe-fx+
                                     (let ((tmp.24
                                            (letrec ((L.x.1.22
                                                      (lambda (c.25)
                                                        (let ((x.1
                                                               (closure-ref c.25 0))
                                                              (f.1
                                                               (closure-ref c.25 1)))
                                                          (unsafe-fx+
                                                           (closure-call x.1 x.1)
                                                           (closure-call
                                                            f.1
                                                            f.1))))))
                                              (cletrec
                                               ((x.1
                                                 (make-closure L.x.1.22 0 x.1 f.1)))
                                               y.1))))
                                       (closure-call
                                        tmp.24
                                        tmp.24
                                        (letrec ((L.x.1.23
                                                  (lambda (c.26)
                                                    (let ((x.1 (closure-ref c.26 0))
                                                          (f.1 (closure-ref c.26 1)))
                                                      (unsafe-fx+
                                                       (closure-call x.1 x.1)
                                                       (closure-call f.1 f.1))))))
                                          (cletrec
                                           ((x.1 (make-closure L.x.1.23 0 x.1 f.1)))
                                           y.1))
                                        (letrec ((L.x.1.24
                                                  (lambda (c.27)
                                                    (let ((x.1 (closure-ref c.27 0))
                                                          (f.1 (closure-ref c.27 1)))
                                                      (unsafe-fx+
                                                       (closure-call x.1 x.1)
                                                       (closure-call f.1 f.1))))))
                                          (cletrec
                                           ((x.1 (make-closure L.x.1.24 0 x.1 f.1)))
                                           y.1))))
                                     (closure-call x.1 x.1))))))
                        (cletrec ((y.1 (make-closure L.y.1.21 0 x.1 f.1))) f.1))))))
          (cletrec ((f.1 (make-closure L.f.1.20 0 f.1))) f.1))))

  (check-equal?
   (convert-closures
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
   '(module
        (letrec ((L.+.64.25
                  (lambda (c.28 tmp.24 tmp.25)
                    (let ()
                      (if (fixnum? tmp.25)
                          (if (fixnum? tmp.24) (unsafe-fx+ tmp.24 tmp.25) (error 2))
                          (error 2)))))
                 (L.cons.63.26
                  (lambda (c.29 tmp.55 tmp.56) (let () (cons tmp.55 tmp.56))))
                 (L.cdr.62.27
                  (lambda (c.30 tmp.44)
                    (let () (if (pair? tmp.44) (unsafe-cdr tmp.44) (error 13)))))
                 (L.car.61.28
                  (lambda (c.31 tmp.43)
                    (let () (if (pair? tmp.43) (unsafe-car tmp.43) (error 12)))))
                 (L.eq?.60.29
                  (lambda (c.32 tmp.57 tmp.58) (let () (eq? tmp.57 tmp.58))))
                 (L.map.4.30
                  (lambda (c.33 f.6 ls.5)
                    (let ((eq?.60 (closure-ref c.33 0))
                          (cons.63 (closure-ref c.33 1))
                          (map.4 (closure-ref c.33 2))
                          (cdr.62 (closure-ref c.33 3))
                          (car.61 (closure-ref c.33 4)))
                      (if (closure-call eq?.60 eq?.60 empty ls.5)
                          empty
                          (closure-call
                           cons.63
                           cons.63
                           (if (procedure? f.6)
                               (if (eq? (unsafe-procedure-arity f.6) 1)
                                   (closure-call f.6 f.6 (closure-call car.61 car.61 ls.5))
                                   (error 42))
                               (error 43))
                           (closure-call
                            map.4
                            map.4
                            f.6
                            (closure-call cdr.62 cdr.62 ls.5))))))))
          (cletrec
           ((|+.64| (make-closure L.+.64.25 2))
            (cons.63 (make-closure L.cons.63.26 2))
            (cdr.62 (make-closure L.cdr.62.27 1))
            (car.61 (make-closure L.car.61.28 1))
            (eq?.60 (make-closure L.eq?.60.29 2))
            (map.4 (make-closure L.map.4.30 2 eq?.60 cons.63 map.4 cdr.62 car.61)))
           (closure-call
            map.4
            map.4
            (letrec ((L.lam.1.31
                      (lambda (c.34 x.7)
                        (let ((|+.64| (closure-ref c.34 0)))
                          (closure-call |+.64| |+.64| 1 x.7)))))
              (cletrec ((lam.1 (make-closure L.lam.1.31 1 |+.64|))) lam.1))
            (closure-call
             cons.63
             cons.63
             1
             (closure-call
              cons.63
              cons.63
              2
              (closure-call cons.63 cons.63 3 empty))))))))

  (check-equal?
   (convert-closures
    '(module
         (let ((z.1
                (letrec ((x.1 (lambda
                                  ((free (x.1)))
                                ()
                                (unsafe-procedure-call x.1)))
                         (y.1 (lambda
                                  ((free (y.1)))
                                ()
                                (unsafe-procedure-call y.1))))
                  x.1)))
           z.1)))
   '(module
        (let ((z.1
               (letrec ((L.x.1.32
                         (lambda (c.35)
                           (let ((x.1 (closure-ref c.35 0))) (closure-call x.1 x.1))))
                        (L.y.1.33
                         (lambda (c.36)
                           (let ((y.1 (closure-ref c.36 0)))
                             (closure-call y.1 y.1)))))
                 (cletrec
                  ((x.1 (make-closure L.x.1.32 0 x.1))
                   (y.1 (make-closure L.y.1.33 0 y.1)))
                  x.1))))
          z.1)))
  )
