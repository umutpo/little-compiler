#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide implement-closures)

(define (my-flatten lst)
  (foldr append '() lst))

;; Implement closures in terms of the procedure data structure.
;;
;; hoisted-lang-v9 -> proc-exposed-lang-v9
(define (implement-closures p)

  ;; Any -> Boolean
  (define (primop? e)
     (memq e '(unsafe-fx* unsafe-fx+ unsafe-fx- eq? unsafe-fx< unsafe-fx<= unsafe-fx> unsafe-fx>=
                          fixnum? boolean? empty? void? ascii-char? error? not pair? vector? procedure? cons unsafe-car
                          unsafe-cdr unsafe-make-vector unsafe-vector-length unsafe-vector-set! unsafe-vector-ref unsafe-procedure-arity)))

  ;; (listof hoisted-lang-v9.Value) -> (listof proc-exposed-lang-v9.Value)
  (define (implement-closures--lov lov)
    (map implement-closures-value lov))

  ;; hoisted-lang-v9.Effect -> proc-exposed-lang-v9.Effect
  (define (implement-closures-effect e)
    (match e
      [`(begin ,effects ...) `(begin ,@(implement-closures--loe effects))]
      [`(,primop ,values ...) `(,primop ,@(implement-closures--lov values))]))
  
  ;; (listof hoisted-lang-v9.Effect) -> (listof proc-exposed-lang-v9.Effect)
  (define (implement-closures--loe loe)
    (map implement-closures-effect loe))

  ;; (listof aloc) (listof label) (listof int) (listof int)
  ;;                -> (listof `(aloc (make-procedure label int int)))
  (define (get-make-procedures alocs labels arities lens)
    (for/list ([aloc alocs]
               [label labels]
               [arity arities]
               [len lens])
      `(,aloc (make-procedure ,label ,arity ,len))))

  ;; (listof aloc) (listof (listof hoisted-lang-v9.Value))
  ;;                  -> (listof (unsafe-procedure-set! aloc int hoisted-lang-v9.Value))
  (define (get-procedure-sets alocs vals)

    ;; aloc (listof hoisted-lang-v9.Value)
    ;;             -> (listof (unsafe-procedure-set! aloc int hoisted-lang-v9.Value))
    (define (get-procedure-sets aloc vals)
      (for/list ([i (build-list (length vals) values)])
        `(unsafe-procedure-set! ,aloc ,i ,(implement-closures-value (list-ref vals i)))))

    (my-flatten (for/list ([aloc alocs]
                           [val vals])
                  (get-procedure-sets aloc val))))

  ;; hoisted-lang-v9.Value -> proc-exposed-lang-v9.Value
  (define (implement-closures-value v)
    (match v
      [`(cletrec ([,alocs (make-closure ,labels ,arities ,values ...)] ...) ,value)
        (let ([make-procs (get-make-procedures alocs labels arities (map length values))]
              [proc-sets (get-procedure-sets alocs values)]
              [val (implement-closures-value value)])
          `(let ,make-procs
              ,(if (> (length proc-sets) 0)
                `(begin ,@proc-sets ,val)
                val)))]
      [`(closure-ref ,value_c ,value_i)
       `(unsafe-procedure-ref ,(implement-closures-value value_c) ,(implement-closures-value value_i))]
      [`(closure-call ,value_c ,values ...)
       `(call (unsafe-procedure-label ,(implement-closures-value value_c)) ,@(implement-closures--lov values))]
      [`(call ,value ,values ...)
       `(call ,(implement-closures-value value) ,@(implement-closures--lov values))]
      [`(let ([,alocs ,values] ...) ,value)
       `(let ,(for/list ([aloc alocs]
                         [val values])
                `[,aloc ,(implement-closures-value val)])
          ,(implement-closures-value value))]
      [`(if ,value_p ,value_1 ,value_2)
       `(if ,(implement-closures-value value_p) ,(implement-closures-value value_1) ,(implement-closures-value value_2))]
      [`(begin ,effects ... ,value)
       `(begin ,@(implement-closures--loe effects) ,(implement-closures-value value))]
      [`(,primop ,values ...)
       #:when (primop? primop)
       `(,primop ,@(implement-closures--lov values))]
      [triv triv]))

  ;; hoisted-lang-v9.Def -> proc-exposed-lang-v9.Def
  (define (implement-closures-def def)
    (match def
      [`(define ,label (lambda (,params ...) ,value))
       `(define ,label (lambda ,params ,(implement-closures-value value)))]))

  (match p
    [`(module ,defs ... ,value)
     `(module ,@(map implement-closures-def defs)
        ,(implement-closures-value value))]))

(module+ tests
  (check-equal?
   (implement-closures
    '(module
         (define L.x.1.7
           (lambda (c.4) (let ((x.1 (closure-ref c.4 0))) (call L.x.1.7 x.1))))
       (cletrec
        ((x.1 (make-closure L.x.1.7 0 x.1)) (y.1 (make-closure L.x.1.9 0 y.1)))
        x.1)))
   '(module
        (define L.x.1.7
          (lambda (c.4)
            (let ((x.1 (unsafe-procedure-ref c.4 0))) (call L.x.1.7 x.1))))
      (let ((x.1 (make-procedure L.x.1.7 0 1)) (y.1 (make-procedure L.x.1.9 0 1)))
        (begin
          (unsafe-procedure-set! x.1 0 x.1)
          (unsafe-procedure-set! y.1 0 y.1)
          x.1))))

  (check-equal?
   (implement-closures
    '(module
         (define L.*.231.36
           (lambda (c.518 tmp.232 tmp.233)
             (let ()
               (if (fixnum? tmp.233)
                   (if (fixnum? tmp.232) (unsafe-fx* tmp.232 tmp.233) (error 1))
                   (error 1)))))
       (define L.+.228.35
         (lambda (c.517 tmp.229 tmp.230)
           (let ()
             (if (fixnum? tmp.230)
                 (if (fixnum? tmp.229) (unsafe-fx+ tmp.229 tmp.230) (error 2))
                 (error 2)))))
       (define L.+.225.34
         (lambda (c.516 tmp.226 tmp.227)
           (let ()
             (if (fixnum? tmp.227)
                 (if (fixnum? tmp.226) (unsafe-fx+ tmp.226 tmp.227) (error 2))
                 (error 2)))))
       (cletrec
        ((|+.225| (make-closure L.+.225.34 2))
         (|+.228| (make-closure L.+.228.35 2))
         (*.231 (make-closure L.*.231.36 2)))
        (closure-call
         |+.225|
         |+.225|
         (closure-call |+.228| |+.228| 5 6)
         (closure-call *.231 *.231 4 5))))
    )
   '(module
        (define L.*.231.36
          (lambda (c.518 tmp.232 tmp.233)
            (let ()
              (if (fixnum? tmp.233)
                  (if (fixnum? tmp.232) (unsafe-fx* tmp.232 tmp.233) (error 1))
                  (error 1)))))
      (define L.+.228.35
        (lambda (c.517 tmp.229 tmp.230)
          (let ()
            (if (fixnum? tmp.230)
                (if (fixnum? tmp.229) (unsafe-fx+ tmp.229 tmp.230) (error 2))
                (error 2)))))
      (define L.+.225.34
        (lambda (c.516 tmp.226 tmp.227)
          (let ()
            (if (fixnum? tmp.227)
                (if (fixnum? tmp.226) (unsafe-fx+ tmp.226 tmp.227) (error 2))
                (error 2)))))
      (let ((|+.225| (make-procedure L.+.225.34 2 0))
            (|+.228| (make-procedure L.+.228.35 2 0))
            (*.231 (make-procedure L.*.231.36 2 0)))
        (call
         (unsafe-procedure-label |+.225|)
         |+.225|
         (call (unsafe-procedure-label |+.228|) |+.228| 5 6)
         (call (unsafe-procedure-label *.231) *.231 4 5)))))
)