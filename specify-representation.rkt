#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide specify-representation)

;; Compiles immediate data and primitive operations into their implementations as ptrs
;; and primitive bitwise operations on ptrs.
;;
;; proc-exposed-lang-v9 -> exprs-bits-lang-v8
(define (specify-representation p)

  ;; any -> Boolean
  (define (primop? p)
    (and (member p '(unsafe-fx* unsafe-fx+ unsafe-fx- eq? unsafe-fx< unsafe-fx<= unsafe-fx> unsafe-fx>=
                                fixnum? boolean? empty? void? ascii-char? error? not pair? vector? procedure? cons
                                unsafe-car unsafe-cdr unsafe-make-vector unsafe-vector-length unsafe-vector-set!
                                unsafe-vector-ref make-procedure unsafe-procedure-arity unsafe-procedure-label
                                unsafe-procedure-ref unsafe-procedure-set!))
         #t))

  ;; Triv -> Triv
  (define (specify-representation-triv e)
    (match e
      ['#t (current-true-ptr)]
      ['#f (current-false-ptr)]
      ['empty (current-empty-ptr)]
      [fixnum #:when (int61? fixnum)
              (bitwise-ior (arithmetic-shift fixnum (current-fixnum-shift)) (current-fixnum-tag))]
      [`(void) (current-void-ptr)]
      [`(error ,num) (bitwise-ior (arithmetic-shift num (current-error-shift)) (current-error-tag))]
      [label #:when (label? label) label]
      [aloc #:when (aloc? aloc) aloc]
      [char #:when (ascii-char-literal? char)
            (bitwise-ior (arithmetic-shift (char->integer char) (current-ascii-char-shift)) (current-ascii-char-tag))]))

  (define (spec-unop val mask tag)
    `(if (= (bitwise-and ,val ,mask) ,tag)
         ,(current-true-ptr)
         ,(current-false-ptr)))

  ;; Primop Value -> Value
  (define (specify-representation-primop primop values)
    (match primop
      ['unsafe-fx*
       `(* ,(specify-representation-value (first values))
           (arithmetic-shift-right ,(specify-representation-value (second values))
                                   ,(current-fixnum-shift)))]
      ['unsafe-fx+ `(+ ,(specify-representation-value (first values)) ,(specify-representation-value (second values)))]
      ['unsafe-fx- `(-  ,(specify-representation-value (first values)) ,(specify-representation-value (second values)))]
      ['eq? `(if (= ,(specify-representation-value (first values)) ,(specify-representation-value (second values))) ,(current-true-ptr) ,(current-false-ptr))]
      ['unsafe-fx< `(if (< ,(specify-representation-value (first values)) ,(specify-representation-value (second values))) ,(current-true-ptr) ,(current-false-ptr))]
      ['unsafe-fx<= `(if (<= ,(specify-representation-value (first values)) ,(specify-representation-value (second values))) ,(current-true-ptr) ,(current-false-ptr))]
      ['unsafe-fx> `(if (> ,(specify-representation-value (first values)) ,(specify-representation-value (second values))) ,(current-true-ptr) ,(current-false-ptr))]
      ['unsafe-fx>= `(if (>= ,(specify-representation-value (first values)) ,(specify-representation-value (second values))) ,(current-true-ptr) ,(current-false-ptr))]
      ['fixnum? (spec-unop (specify-representation-value (first values)) (current-fixnum-mask) (current-fixnum-tag))]
      ['boolean? (spec-unop (specify-representation-value (first values)) (current-boolean-mask) (current-boolean-tag))]
      ['empty? (spec-unop (specify-representation-value (first values)) (current-empty-mask) (current-empty-tag))]
      ['void? (spec-unop (specify-representation-value (first values)) (current-void-mask) (current-void-tag))]
      ['ascii-char? (spec-unop (specify-representation-value (first values)) (current-ascii-char-mask) (current-ascii-char-tag))]
      ['error? (spec-unop (specify-representation-value (first values)) (current-ascii-char-mask) (current-ascii-char-tag))]
      ['not
       `(if (!= ,(specify-representation-value (first values)) ,(current-false-ptr))
            ,(current-false-ptr)
            ,(current-true-ptr))]
      ['pair? (spec-unop (specify-representation-value (first values)) (current-pair-mask) (current-pair-tag))]
      ['vector? (spec-unop (specify-representation-value (first values)) (current-vector-mask) (current-vector-tag))]
      ['procedure? (spec-unop (specify-representation-value (first values)) (current-procedure-mask) (current-procedure-tag))]
      ['cons
       (let ([tmp-var (fresh 'tmp)]
             [car (specify-representation-value (first values))]
             [cdr (specify-representation-value (second values))])
         `(let ((,tmp-var (+ (alloc ,(current-pair-size)) ,(current-pair-tag))))
            (begin (mset! ,tmp-var ,(car-offset) ,car) (mset! ,tmp-var ,(cdr-offset) ,cdr) ,tmp-var)))]
      ['unsafe-car `(mref ,(specify-representation-value (first values)) ,(car-offset))]
      ['unsafe-cdr `(mref ,(specify-representation-value (first values)) ,(cdr-offset))]
      ['unsafe-make-vector
       (let ([tmp-var (fresh 'tmp)]
             [length (specify-representation-value (first values))])
         `(let ((,tmp-var (+ (alloc (* (+ 1 (arithmetic-shift-right ,length ,(current-fixnum-shift))) ,(current-word-size-bytes))) ,(current-vector-tag))))
            (begin (mset! ,tmp-var ,(- (current-vector-length-displacement) (current-vector-tag)) ,length) ,tmp-var)))]
      ['unsafe-vector-length
       `(mref ,(specify-representation-value (first values)) ,(- (current-vector-length-displacement) (current-vector-tag)))]
      ['unsafe-vector-set!
       (let ([vec (specify-representation-value (first values))]
             [index (specify-representation-value (second values))]
             [val (specify-representation-value (third values))])
         `(mset! ,vec (+ (* (arithmetic-shift-right ,index ,(current-fixnum-shift)) ,(current-word-size-bytes)) ,(- (current-vector-base-displacement) (current-vector-tag))) ,val))]
      ['unsafe-vector-ref
       (let ([vec (specify-representation-value (first values))]
             [index (specify-representation-value (second values))])
         `(mref ,vec (+ (* (arithmetic-shift-right ,index ,(current-fixnum-shift)) ,(current-word-size-bytes)) ,(- (current-vector-base-displacement) (current-vector-tag)))))]
      ['make-procedure
       (let ([tmp-var (fresh 'tmp)]
             [label (specify-representation-value (first values))]
             [arity (specify-representation-value (second values))]
             [length (specify-representation-value (third values))])
         `(let ((,tmp-var (+ (alloc (* (+ 2 (arithmetic-shift-right ,length ,(current-fixnum-shift))) ,(current-word-size-bytes))) ,(current-procedure-tag))))
            (begin (mset! ,tmp-var ,(- (current-procedure-label-displacement) (current-procedure-tag)) ,label)
                   (mset! ,tmp-var ,(- (current-procedure-arity-displacement) (current-procedure-tag)) ,arity)
                   ,tmp-var)))]
      ['unsafe-procedure-arity
       (let ([proc (specify-representation-value (first values))])
         `(mref ,proc ,(- (current-procedure-arity-displacement) (current-procedure-tag))))]
      ['unsafe-procedure-label
       (let ([proc (specify-representation-value (first values))])
         `(mref ,proc ,(- (current-procedure-label-displacement) (current-procedure-tag))))]
      ['unsafe-procedure-ref
       (let ([proc (specify-representation-value (first values))]
             [index (specify-representation-value (second values))])
         `(mref
           ,proc
           (+ (* (arithmetic-shift-right ,index ,(current-fixnum-shift))
                 ,(current-word-size-bytes))
              ,(- (current-procedure-environment-displacement) (current-procedure-tag)))))]
      ['unsafe-procedure-set!
       (let ([proc (specify-representation-value (first values))]
             [index (specify-representation-value (second values))]
             [val (specify-representation-value (third values))])
         `(mset!
           ,proc
           (+ (* (arithmetic-shift-right ,index ,(current-fixnum-shift))
                 ,(current-word-size-bytes))
              ,(- (current-procedure-environment-displacement) (current-procedure-tag)))
           ,val))]))

  ;; Effect -> Effect
  (define (specify-representation-effect e)
    (match e
      [`(begin ,effects ...)
        `(begin ,@(map specify-representation-effect effects))]
      [`(,primop ,vs ...)
        #:when (primop? primop)
        (specify-representation-primop primop vs)]))

  ;; Value -> Value
  (define (specify-representation-value e)
    (match e
      [`(call ,v ,vs ...)
       `(call ,(specify-representation-value v) ,@(map specify-representation-value vs))]
      [`(let ([,alocs ,vs] ...) ,val)
       `(let ,(map (lambda (aloc v) `(,aloc ,(specify-representation-value v))) alocs vs)
          ,(specify-representation-value val))]
      [`(if ,vp ,vc ,va)
       `(if (!= ,(specify-representation-value vp) ,(current-false-ptr))
            ,(specify-representation-value vc)
            ,(specify-representation-value va))]
      [`(,primop ,vs ...)
       #:when (primop? primop)
       (specify-representation-primop primop vs)]
      [`(begin ,effects ... ,value)
        `(begin ,@(map specify-representation-effect effects) ,(specify-representation-value value))]
      [triv (specify-representation-triv triv)]))

  ;; Def -> Def
  (define (specify-representation-def e)
    (match e
      [`(define ,label (lambda (,params ...) ,value))
       `(define ,label (lambda ,params ,(specify-representation-value value)))]))

  (match p
    [`(module ,defs ... ,value)
     `(module ,@(map specify-representation-def defs)
        ,(specify-representation-value value))]))

(module+ tests
  (check-equal?
   (specify-representation
    '(module
         (define L.+.1
           (lambda (tmp.1 tmp.2)
             (if (fixnum? tmp.2)
                 (if (fixnum? tmp.1) (unsafe-fx+ tmp.1 tmp.2) (error 2))
                 (error 2))))
       (call L.+.1 5 3)))
   '(module
        (define L.+.1
          (lambda (tmp.1 tmp.2)
            (if (!= (if (= (bitwise-and tmp.2 7) 0) 14 6) 6)
                (if (!= (if (= (bitwise-and tmp.1 7) 0) 14 6) 6) (+ tmp.1 tmp.2) 574)
                574)))
      (call L.+.1 40 24)))

  (check-equal?
   (specify-representation
    '(module
         (define L.+.1
           (lambda (tmp.1 tmp.2)
             (if (not tmp.2)
                 (if (fixnum? tmp.1) (unsafe-fx+ #t tmp.2) (error 2))
                 (error 2))))
       (call L.+.1 (not 5) 3)))

   '(module
        (define L.+.1
          (lambda (tmp.1 tmp.2)
            (if (!= (if (!= tmp.2 6) 6 14) 6)
                (if (!= (if (= (bitwise-and tmp.1 7) 0) 14 6) 6) (+ 14 tmp.2) 574)
                574)))
      (call L.+.1 (if (!= 40 6) 6 14) 24)))

  (check-equal?
   (specify-representation
    '(module
         (define L.+.1
           (lambda (tmp.1 tmp.2)
             (if (fixnum? tmp.2)
                 (if (fixnum? tmp.1) (eq? tmp.1 tmp.2) (error 2))
                 (error 2))))
       (call L.+.1 (not 5) 3)))
   '(module
        (define L.+.1
          (lambda (tmp.1 tmp.2)
            (if (!= (if (= (bitwise-and tmp.2 7) 0) 14 6) 6)
                (if (!= (if (= (bitwise-and tmp.1 7) 0) 14 6) 6)
                    (if (= tmp.1 tmp.2) 14 6)
                    574)
                574)))
      (call L.+.1 (if (!= 40 6) 6 14) 24)))

  (check-equal?
   (specify-representation
    '(module
         (define L.eq?.35
           (lambda (tmp.139 tmp.140)
             (if (fixnum? tmp.140)
                 (if (fixnum? tmp.139)
                     (eq? tmp.139 tmp.140)
                     (error 5)) (error 5))))
       (define L.+.36
         (lambda (tmp.141 tmp.142)
           (if (fixnum? tmp.142)
               (if (fixnum? tmp.141)
                   (unsafe-fx+ tmp.141 tmp.142)
                   (error 2)) (error 2))))
       (if (call L.eq?.35 (call L.+.36 5 6) 11) 4 6)))
   '(module  (define L.eq?.35
               (lambda (tmp.139 tmp.140)
                 (if (!= (if (= (bitwise-and tmp.140 7) 0) 14 6) 6)
                     (if (!= (if (= (bitwise-and tmp.139 7) 0) 14 6) 6)
                         (if (= tmp.139 tmp.140) 14 6)
                         1342)
                     1342)))
      (define L.+.36
        (lambda (tmp.141 tmp.142)
          (if (!= (if (= (bitwise-and tmp.142 7) 0) 14 6) 6)
              (if (!= (if (= (bitwise-and tmp.141 7) 0) 14 6) 6)
                  (+ tmp.141 tmp.142)
                  574)
              574)))
      (if (!= (call L.eq?.35 (call L.+.36 40 48) 88) 6) 32 48)))

  (check-equal?
   (specify-representation
    '(module
         (define L.eq?.29
           (lambda (tmp.127 tmp.128)
             (if (fixnum? tmp.128)
                 (if (fixnum? tmp.127)
                     (eq? tmp.127 tmp.128)
                     (error 5)) (error 5))))
       (define L.eq?.30
         (lambda (tmp.129 tmp.130)
           (if (fixnum? tmp.130)
               (if (fixnum? tmp.129)
                   (eq? tmp.129 tmp.130)
                   (error 5)) (error 5))))
       (define L.+.31
         (lambda (tmp.131 tmp.132)
           (if (fixnum? tmp.132)
               (if (fixnum? tmp.131)
                   (unsafe-fx+ tmp.131 tmp.132)
                   (error 2)) (error 2))))
       (define L.+.32
         (lambda (tmp.133 tmp.134)
           (if (fixnum? tmp.134)
               (if (fixnum? tmp.133)
                   (unsafe-fx+ tmp.133 tmp.134)
                   (error 2)) (error 2))))
       (define L.fib_loop.22
         (lambda (n.110 acc1.111 acc2.112)
           (if (call L.eq?.29 n.110 0)
               acc1.111
               (if (call L.eq?.30 n.110 1)
                   acc2.112
                   (let ((new-n.113 (call L.+.31 n.110 -1)))
                     (let ((new-acc2.114 (call L.+.32 acc1.111 acc2.112)))
                       (call L.fib_loop.22 new-n.113 acc2.112 new-acc2.114)))))))
       (call L.fib_loop.22 5 0 1)))
   '(module
        (define L.eq?.29
          (lambda (tmp.127 tmp.128)
            (if (!= (if (= (bitwise-and tmp.128 7) 0) 14 6) 6)
                (if (!= (if (= (bitwise-and tmp.127 7) 0) 14 6) 6)
                    (if (= tmp.127 tmp.128) 14 6)
                    1342)
                1342)))
      (define L.eq?.30
        (lambda (tmp.129 tmp.130)
          (if (!= (if (= (bitwise-and tmp.130 7) 0) 14 6) 6)
              (if (!= (if (= (bitwise-and tmp.129 7) 0) 14 6) 6)
                  (if (= tmp.129 tmp.130) 14 6)
                  1342)
              1342)))
      (define L.+.31
        (lambda (tmp.131 tmp.132)
          (if (!= (if (= (bitwise-and tmp.132 7) 0) 14 6) 6)
              (if (!= (if (= (bitwise-and tmp.131 7) 0) 14 6) 6)
                  (+ tmp.131 tmp.132)
                  574)
              574)))
      (define L.+.32
        (lambda (tmp.133 tmp.134)
          (if (!= (if (= (bitwise-and tmp.134 7) 0) 14 6) 6)
              (if (!= (if (= (bitwise-and tmp.133 7) 0) 14 6) 6)
                  (+ tmp.133 tmp.134)
                  574)
              574)))
      (define L.fib_loop.22
        (lambda (n.110 acc1.111 acc2.112)
          (if (!= (call L.eq?.29 n.110 0) 6)
              acc1.111
              (if (!= (call L.eq?.30 n.110 8) 6)
                  acc2.112
                  (let ((new-n.113 (call L.+.31 n.110 -8)))
                    (let ((new-acc2.114 (call L.+.32 acc1.111 acc2.112)))
                      (call L.fib_loop.22 new-n.113 acc2.112 new-acc2.114)))))))
      (call L.fib_loop.22 40 0 8)))

  (check-equal?
   (specify-representation
    '(module (cons 5 6)))
   '(module
        (let ((tmp.1 (+ (alloc 16) 1)))
          (begin (mset! tmp.1 -1 40) (mset! tmp.1 7 48) tmp.1))))

  (check-equal?
   (specify-representation
    '(module (unsafe-car (cons 5 6))))
   '(module
        (mref
         (let ((tmp.2 (+ (alloc 16) 1)))
           (begin (mset! tmp.2 -1 40) (mset! tmp.2 7 48) tmp.2))
         -1)))

  (check-equal?
   (specify-representation '(module (unsafe-vector-ref (unsafe-make-vector 3) 6)))
   '(module
        (mref
         (let ((tmp.3 (+ (alloc (* (+ 1 (arithmetic-shift-right 24 3)) 8)) 3)))
           (begin (mset! tmp.3 -3 24) tmp.3))
         (+ (* (arithmetic-shift-right 48 3) 8) 5))))

  (check-equal?
   (specify-representation
    '(module
         (define L.vector-init-loop.90
           (lambda (len.231 i.232 vec.233)
             (if (eq? len.231 i.232)
                 vec.233
                 (begin (unsafe-vector-set! vec.233 i.232 0)
                        (call L.vector-init-loop.90 len.231 (unsafe-fx+ i.232 1) vec.233)))))
       (define L.make-init-vector.91
         (lambda (tmp.234)
           (let ((tmp.235
                  (unsafe-make-vector
                   tmp.234)))
             (call L.vector-init-loop.90 tmp.234 0 tmp.235))))
       (define L.tmp.89
         (lambda (tmp.230)
           (if (fixnum? tmp.230) (call L.make-init-vector.91 tmp.230) (error 8))))
       (call L.tmp.89 0)))
   '(module
        (define L.vector-init-loop.90
          (lambda (len.231 i.232 vec.233)
            (if (!= (if (= len.231 i.232) 14 6) 6)
                vec.233
                (begin
                  (mset! vec.233 (+ (* (arithmetic-shift-right i.232 3) 8) 5) 0)
                  (call L.vector-init-loop.90 len.231 (+ i.232 8) vec.233)))))
      (define L.make-init-vector.91
        (lambda (tmp.234)
          (let ((tmp.235
                 (let ((tmp.4
                        (+
                         (alloc (* (+ 1 (arithmetic-shift-right tmp.234 3)) 8))
                         3)))
                   (begin (mset! tmp.4 -3 tmp.234) tmp.4))))
            (call L.vector-init-loop.90 tmp.234 0 tmp.235))))
      (define L.tmp.89
        (lambda (tmp.230)
          (if (!= (if (= (bitwise-and tmp.230 7) 0) 14 6) 6)
              (call L.make-init-vector.91 tmp.230)
              2110)))
      (call L.tmp.89 0)))

  (check-equal?
   (specify-representation
    '(module
         (define L.vector-init-loop.90
           (lambda (len.231 i.232 vec.233)
             (if (eq? len.231 i.232)
                 vec.233
                 (begin
                   (unsafe-vector-set! vec.233 i.232 0)
                   (call L.vector-init-loop.90 len.231 (unsafe-fx+ i.232 1) vec.233)))))
       (define L.make-init-vector.91
         (lambda (tmp.234)
           (let ((tmp.235 (unsafe-make-vector tmp.234)))
             (call L.vector-init-loop.90 tmp.234 0 tmp.235))))
       (define L.tmp.89
         (lambda (tmp.230)
           (if (fixnum? tmp.230) (call L.make-init-vector.91 tmp.230) (error 8))))
       (call L.tmp.89 0)))
   '(module
        (define L.vector-init-loop.90
          (lambda (len.231 i.232 vec.233)
            (if (!= (if (= len.231 i.232) 14 6) 6)
                vec.233
                (begin
                  (mset! vec.233 (+ (* (arithmetic-shift-right i.232 3) 8) 5) 0)
                  (call L.vector-init-loop.90 len.231 (+ i.232 8) vec.233)))))
      (define L.make-init-vector.91
        (lambda (tmp.234)
          (let ((tmp.235
                 (let ((tmp.5
                        (+
                         (alloc (* (+ 1 (arithmetic-shift-right tmp.234 3)) 8))
                         3)))
                   (begin (mset! tmp.5 -3 tmp.234) tmp.5))))
            (call L.vector-init-loop.90 tmp.234 0 tmp.235))))
      (define L.tmp.89
        (lambda (tmp.230)
          (if (!= (if (= (bitwise-and tmp.230 7) 0) 14 6) 6)
              (call L.make-init-vector.91 tmp.230)
              2110)))
      (call L.tmp.89 0)))


  (check-equal?
   (specify-representation
    '(module
         (define L.x.1.7
           (lambda (c.4)
             (let ((x.1 (unsafe-procedure-ref c.4 0))) (call L.x.1.7 x.1))))
       (let ((x.1 (make-procedure L.x.1.7 0 1)) (y.1 (make-procedure L.x.1.9 0 1)))
         (begin
           (unsafe-procedure-set! x.1 0 x.1)
           (unsafe-procedure-set! y.1 0 y.1)
           x.1))))
     '(module
   (define L.x.1.7
     (lambda (c.4)
       (let ((x.1 (mref c.4 (+ (* (arithmetic-shift-right 0 3) 8) 14))))
         (call L.x.1.7 x.1))))
   (let ((x.1
          (let ((tmp.6 (+ (alloc (* (+ 2 (arithmetic-shift-right 8 3)) 8)) 2)))
            (begin (mset! tmp.6 -2 L.x.1.7) (mset! tmp.6 6 0) tmp.6)))
         (y.1
          (let ((tmp.7 (+ (alloc (* (+ 2 (arithmetic-shift-right 8 3)) 8)) 2)))
            (begin (mset! tmp.7 -2 L.x.1.9) (mset! tmp.7 6 0) tmp.7))))
     (begin
       (mset! x.1 (+ (* (arithmetic-shift-right 0 3) 8) 14) x.1)
       (mset! y.1 (+ (* (arithmetic-shift-right 0 3) 8) 14) y.1)
       x.1))))
    
  (check-equal?
   (specify-representation
    '(module
         (define L.id.149.14 (lambda (c.496 x.150) (let () x.150)))
       (let ((id.149 (make-procedure L.id.149.14 1 0)))
         (begin
           (let ((x.151 (call (unsafe-procedure-label id.149) id.149 5)))
             (call (unsafe-procedure-label id.149) id.149 x.151))))))
   '(module
        (define L.id.149.14 (lambda (c.496 x.150) (let () x.150)))
      (let ((id.149
             (let ((tmp.8 (+ (alloc (* (+ 2 (arithmetic-shift-right 0 3)) 8)) 2)))
               (begin (mset! tmp.8 -2 L.id.149.14) (mset! tmp.8 6 8) tmp.8))))
        (begin
          (let ((x.151 (call (mref id.149 -2) id.149 40)))
            (call (mref id.149 -2) id.149 x.151)))))))