#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide optimize-predicates)

;; Optimize nested-asm-lang-v5 programs by analyzing and simplifying predicates.
;;
;; nested-asm-lang-v8 -> nested-asm-lang-v8
(define (optimize-predicates p)

  ;; An abstract-integer is one of:
  ;; - integer?
  ;; - 'unknown

  ;; Env is map of loc to abstract-integer

  ;; (Source Def) -> (Target Def)
  (define (optimize-predicates-def e)
    (match e
      [`(define ,label ,tail) `(define ,label ,(optimize-predicates-tail '() tail))]))

  ;; Env (Source Tail) -> (Target Tail)
  (define (optimize-predicates-tail env e)
    ;; Env nested-asm-lang-v5.Pred nested-asm-lang-v5.Tail nested-asm-lang-v5.Tail -> nested-asm-lang-v5.Tail
    (define (choose-pred-tail env e tail1 tail2)
      (let-values ([(env pred) (optimize-predicates-pred env e)])
        (match pred
          [`(true) (optimize-predicates-tail env tail1)]
          [`(false) (optimize-predicates-tail env tail2)]
          [else `(if ,pred
                     ,(optimize-predicates-tail env tail1)
                     ,(optimize-predicates-tail env tail2))])))

    (match e
      [`(halt ,opand) e]
      [`(jump ,trg) e]
      [`(begin ,effects ... ,tail)
       (let-values ([(env effects) (optimize-predicates-effect--loe env effects)])
         `(begin ,@effects ,(optimize-predicates-tail env tail)))]
      [`(if ,pred ,tail1 ,tail2)
       (choose-pred-tail env pred tail1 tail2)]))

  ;; Env (Source Effect) -> values (Env AND (Target Effect))
  (define (optimize-predicates-effect env e)
    ;; Env (Source Pred) (Source Effect) (Source Effect)
    ;;                    -> values (Env AND (Source Effect))
    (define (choose-pred-effect env e effect1 effect2)
      (let-values ([(env pred) (optimize-predicates-pred env e)])
        (match pred
          [`(true) (optimize-predicates-effect env effect1)]
          [`(false) (optimize-predicates-effect env effect2)]
          [else
           (let-values ([(env1 effect1^) (optimize-predicates-effect env effect1)]
                        [(env2 effect2^) (optimize-predicates-effect env effect2)])
             (values
              (clear-locs env (set-union (collect-locs-effect '() effect1)
                                         (collect-locs-effect '() effect2)))
              `(if ,pred ,effect1^ ,effect2^)))])))

    (match e
      [`(set! ,loc_1 (mref ,loc_2 ,index)) (values env e)]
      [`(set! ,loc (,binop ,loc ,opand))
       (values
        (dict-set env loc ((abstract-interp-binop binop)
                           (optimize-predicates-triv env loc)
                           (optimize-predicates-triv env opand)))
        e)]
      [`(set! ,loc ,triv)
       (values (dict-set env loc (optimize-predicates-triv env triv)) e)]
      [`(mset! ,loc ,index ,triv) (values env e)]
      [`(begin ,effect^ ,effects ...)
       (let-values ([(env effects) (optimize-predicates-effect--loe env (cons effect^ effects))])
         (values env `(begin ,@effects)))]
      [`(if ,pred ,effect1 ,effect2)
       (choose-pred-effect env pred effect1 effect2)]
      [`(return-point ,label ,tail)
       (values env `(return-point ,label ,(optimize-predicates-tail env tail)))]))

  ;; Env (listof (Source Effect)) -> values (Env AND (listof (Target Effect)))
  (define (optimize-predicates-effect--loe env loe)
    (let-values ([(env effects)
                  (for/fold ([env env]
                             [effect-ls '()])
                            ([effect loe])
                    (let-values ([(new-env effect) (optimize-predicates-effect env effect)])
                      (values new-env (cons effect effect-ls))))])
      (values env (reverse effects))))

  ;; Env (Source Pred) -> values (Env AND (Target Pred))
  (define (optimize-predicates-pred env pred)
    ;; Env (Source Pred) (Source Pred) (Source Pred)
    ;;                    -> values (Env AND (Source Pred))
    (define (choose-pred-pred env e pred1 pred2)
      (let-values ([(env pred) (optimize-predicates-pred env e)])
        (match pred
          [`(true) (optimize-predicates-pred env pred1)]
          [`(false) (optimize-predicates-pred env pred2)]
          [else
           (let-values ([(env1 pred1^) (optimize-predicates-pred env pred1)]
                        [(env2 pred2^) (optimize-predicates-pred env pred2)])
             (values (clear-locs env (set-union (collect-locs-pred '() pred1)
                                                (collect-locs-pred '() pred2)))
                     `(if ,pred ,pred1^ ,pred2^)))])))

    (match pred
      [`(true) (values env pred)]
      [`(false) (values env pred)]
      [`(not ,pred)
       (let-values ([(env pred) (optimize-predicates-pred env pred)])
         (match pred
           [`(true) (values env `(false))]
           [`(false) (values env `(true))]
           [else (values env `(not ,pred))]))]
      [`(begin ,effects ... ,pred)
       (let*-values ([(env effects) (optimize-predicates-effect--loe env effects)]
                     [(env pred) (optimize-predicates-pred env pred)])
         (values env `(begin ,@effects ,pred)))]
      [`(if ,pred ,pred1 ,pred2)
       (choose-pred-pred env pred pred1 pred2)]
      [`(,relop ,loc ,opand)
       (values
        env
        (let ([abstract-pred ((abstract-interp-relop relop)
                              (optimize-predicates-triv env loc)
                              (optimize-predicates-triv env opand))])
          (cond
            [(eq? abstract-pred 'unknown) pred]
            [abstract-pred '(true)]
            [else '(false)])))]))

  ;; Env Triv -> abstract-integer
  (define (optimize-predicates-triv env triv)
    (match triv
      [(? label?) triv]
      [(? symbol?) (dict-ref env triv 'unknown)]
      [(? integer?) triv]))

  (define (collect-locs-tail acc e)
    (match e
      [`(jump ,trg) (set-add acc trg)]
      [`(begin ,effects ... ,tail) (collect-locs-tail (collect-locs-effect--loe acc effects) tail)]
      [`(if ,pred ,tail1 ,tail2) (collect-locs-tail (collect-locs-tail (collect-locs-pred pred) tail1) tail2)]))

  ;; (setof loc) (Source Effect) -> (setof loc)
  (define (collect-locs-effect acc e)
    (match e
      [`(set! ,loc_1 (mref ,loc_2 ,index)) (set-union acc `(,loc_1 ,loc_2 ,index))]
      [`(set! ,loc (,binop ,loc ,triv)) (set-add acc loc)]
      [`(set! ,loc ,triv) (set-add acc loc)]
      [`(mset! ,loc ,index ,triv) (set-union acc '(,loc ,index ,triv))]
      [`(begin ,effect^ ,effects ...) (collect-locs-effect--loe acc (cons effect^ effects))]
      [`(if ,pred ,effect1 ,effect2)
       (collect-locs-pred (collect-locs-effect--loe acc (list effect1 effect2)) pred)]
      [`(return-point ,label ,tail) (collect-locs-tail acc tail)]))

  ;; (setof loc) (Source Pred) -> (setof loc)
  (define (collect-locs-pred acc e)
    (match e
      [`(not ,pred) (collect-locs-pred acc pred)]
      [`(begin ,effects ... ,pred)
       (collect-locs-pred (collect-locs-effect--loe acc effects) pred)]
      [`(if ,pred ,pred1 ,pred2)
       (collect-locs-pred (collect-locs-pred (collect-locs-pred pred) pred1) pred2)]
      [else acc]))

  ;; (setof loc) (listof (Source Effect)) -> (setof loc)
  (define (collect-locs-effect--loe acc loe)
    (for/fold ([acc acc])
              ([effect loe])
      (collect-locs-effect acc effect)))

  ;; Env (listof loc) -> Env
  (define (clear-locs env locs)
    (for/fold ([env env])
              ([loc locs])
      (dict-set env loc 'unknown)))

  ;; An abstract-pred? is one of:
  ;; - #t
  ;; - #f
  ;; - 'unknown

  ;; relop -> (abstract-integer abstract-integer -> abstract-pred)
  (define (abstract-interp-relop relop)
    (define funs (hash '< < '<= <= '= = '>= >= '> > '!= (lambda (v1 v2) (not (= v1 v2)))))
    (lambda (x1 x2)
      (cond
        [(and (integer? x1) (integer? x2))
         ((dict-ref funs relop) x1 x2)]
        [else 'unknown])))

  ;; binop -> (abstract-integer? abstract-integer? -> abstract-integer?)
  (define (abstract-interp-binop binop)
    (match binop
      ['+
       (lambda (x1 x2)
         (cond
           [(and (integer? x1) (integer? x2))
            (+ x1 x2)]
           [(eq? x1 0)
            x2]
           [(eq? x2 0)
            x1]
           [else 'unknown]))]
      ['-
       (lambda (x1 x2)
         (cond
           [(and (integer? x1) (integer? x2))
            (- x1 x2)]
           [(eq? x1 0)
            x2]
           [(eq? x2 0)
            x1]
           [else 'unknown]))]
      ['*
       (lambda (x1 x2)
         (cond
           [(and (integer? x1) (integer? x2))
            (* x1 x2)]
           [(eq? x1 0)
            0]
           [(eq? x2 0)
            0]
           [(eq? x1 1)
            x2]
           [(eq? x2 1)
            x1]
           [else 'unknown]))]
      ['bitwise-and
       (lambda (x1 x2)
         `(bitwise-and ,x1 ,x2))]
      ['bitwise-ior
       (lambda (x1 x2)
         `(bitwise-ior ,x1 ,x2))]
      ['bitwise-xor
       (lambda (x1 x2)
         `(bitwise-xor ,x1 ,x2))]
      ['arithmetic-shift-right
       (lambda (x1 x2)
         `(arithmetic-shift-right ,x1 ,x2))]))

  (match p
    [`(module ,defs ... ,tail)
     `(module ,@(map optimize-predicates-def defs) ,(optimize-predicates-tail '() tail))]))

(module+ tests
  (check-equal?
  (optimize-predicates
    '(module (begin (set! r8 69)
                    (set! r9 420)
                    (if (true)
                        (set! r8 5)
                        (set! r9 7))
                    (halt r8))))
  '(module (begin (set! r8 69) (set! r9 420) (set! r8 5) (halt r8))))

  (check-equal?
  (optimize-predicates
    '(module (begin (set! r8 0)
                    (set! r9 0)
                    (if (not (if (true) (> r8 5) (< r9 6)))
                        (set! r12 15)
                        (set! r12 90))
                    (halt r12))))
  '(module
        (begin
          (set! r8 0)
          (set! r9 0)
          (set! r12 15)
          (halt r12))))

  (check-equal?
  (optimize-predicates
    '(module
        (begin
          (set! rbx 1)
          (set! rcx 2)
          (if (< rbx rcx)
              (begin (set! rdx 4) (halt rdx))
              (begin (set! rdx 8) (halt rdx))))))

  '(module
        (begin
          (set! rbx 1)
          (set! rcx 2)
          (begin
            (set! rdx 4)
            (halt rdx)))))


  (check-equal?
  (optimize-predicates
    '(module (begin (set! r8 7)
                    (set! r12 42)
                    (set! r8 (+ r8 r12))
                    (set! r8 (* r8 r12))
                    (if (> r8 2)
                        (set! r12 69)
                        (set! r12 69))
                    (set! r8 (+ r8 r12))
                    (halt r8))))
  '(module
        (begin
          (set! r8 7)
          (set! r12 42)
          (set! r8 (+ r8 r12))
          (set! r8 (* r8 r12))
          (set! r12 69)
          (set! r8 (+ r8 r12))
          (halt r8))))
)