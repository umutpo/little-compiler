#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide conflict-analysis)

(define (my-flatten lst)
  (foldr append '() lst))

;; Decorates a program with its conflict graph.
;;
;; Asm-pred-lang-v8/undead -> Asm-pred-lang-v8/conflicts
(define (conflict-analysis p)

  ;; Any -> Boolean
  (define (loc? e)
    (or (register? e) (fvar? e) (aloc? e)))

  ;; asm-pred-lang-v8/undead.Info (Set aloc -> (listof aloc)) -> (values list (Set (listof aloc)) (Set aloc -> (listof aloc)))
  (define (conflict-analysis-info-setup e)
    (let ([locals (info-ref e `locals)]
          [undead-out (info-ref e `undead-out)])
      (values locals undead-out (new-graph locals))))

  ;; (Set (listof aloc)) asm-pred-lang-v8/undead.Pred (Set aloc -> (listof aloc)) -> (Set aloc -> (listof aloc))
  (define (conflict-analysis-pred ust pred conflicts)
    (match (cons ust pred)
      [(cons ust `(true)) conflicts]
      [(cons ust `(false)) conflicts]
      [(cons ust `(not ,pred)) (conflict-analysis-pred ust pred conflicts)]
      [(cons `(,usts ... ,ust_pred) `(begin ,effects ... ,pred))
       (conflict-analysis-pred ust_pred pred (conflict-analysis--loe effects usts conflicts))]
      [(cons `(,ust-pred ,ust-pred1 ,ust-pred2) `(if ,pred ,pred1 ,pred2))
       (let* ([pred-conflict (conflict-analysis-pred ust-pred pred conflicts)]
              [pred1-conflict (conflict-analysis-pred ust-pred1 pred1 pred-conflict)])
         (conflict-analysis-pred ust-pred2 pred2 pred1-conflict))]
      [(cons ust `(,relop ,loc ,triv))
       (set! ust (set-remove ust loc))
       (when (loc? triv)
         (set! ust (set-remove ust triv)))
       (add-edges conflicts loc ust)]))

  ;; (listof Effect) (listof (Set (listof aloc))) (Set aloc -> (listof aloc)) -> (Set aloc -> (listof aloc))
  (define (conflict-analysis--loe effects usts conflicts)
    (for/fold ([effect-conflicts conflicts])
              ([eff effects]
               [ust usts])
      (conflict-analysis-effect ust eff effect-conflicts)))

  ;; (Set (listof aloc)) asm-pred-lang-v8/undead.Effect (Set aloc -> (listof aloc)) -> (Set aloc -> (listof aloc))
  (define (conflict-analysis-effect ust effect conflicts)
    (match (cons ust effect)
      [(cons `(,usts ...) `(begin ,effects ...))
       (conflict-analysis--loe effects usts conflicts)]
      [(cons `(,ust-pred ,ust-effect1 ,ust-effect2) `(if ,pred ,effect1 ,effect2))
       (let* ([pred-conflict (conflict-analysis-pred ust-pred pred conflicts)]
              [effect1-conflict (conflict-analysis-effect ust-effect1 effect1 pred-conflict)])
         (conflict-analysis-effect ust-effect2 effect2 effect1-conflict))]
      [(cons ust `(mset! ,loc ,index ,triv))
       (set! ust (set-remove ust loc))
       (when (loc? index)
         (set! ust (set-remove ust index)))
       (when (loc? triv)
         (set! ust (set-remove ust triv)))
       (add-edges conflicts loc ust)]
      [(cons ust `(set! ,loc1 (mref ,loc2 ,index)))
       (set! ust (set-remove ust loc1))
       (add-edges conflicts loc1 ust)]
      [(cons ust `(set! ,loc (,binop ,loc ,opand)))
       (set! ust (set-remove ust loc))
       (add-edges conflicts loc ust)]
      [(cons ust `(set! ,loc ,triv))
       (set! ust (set-remove ust loc))
       (add-edges conflicts loc ust)]
      [(cons ust `(return-point ,label ,tail))
       (conflict-analysis-tail (my-flatten (set-rest ust)) tail conflicts)]))

  ;; (Set (listof aloc)) asm-pred-lang-v8/undead.Tail (Set aloc -> (listof aloc)) -> (Set aloc -> (listof aloc))
  (define (conflict-analysis-tail ust tail conflicts)
    (match (cons ust tail)
      [(cons ust `(jump ,trg ,locs ...)) conflicts]
      [(cons `(,usts ... ,ust_tail) `(begin ,effects ... ,tail))
       (conflict-analysis-tail ust_tail tail (conflict-analysis--loe effects usts conflicts))]
      [(cons `(,ust-pred ,ust-tail1 ,ust-tail2) `(if ,pred ,tail1 ,tail2))
       (let* ([pred-conflicts (conflict-analysis-pred ust-pred pred conflicts)]
              [tail1-conflicts (conflict-analysis-tail ust-tail1 tail1 pred-conflicts)])
         (conflict-analysis-tail ust-tail2 tail2 tail1-conflicts))]))

  ;; asm-pred-lang-v8/undead.Definition -> asm-pred-lang-v8/conflicts.Definition
  (define (conflict-analysis-definition def)
    (match def
      [`(define ,label ,info ,tail)
       (let*-values ([(locals ust conflicts) (conflict-analysis-info-setup info)]
                     [(new-info) (info-set info 'conflicts (conflict-analysis-tail ust tail conflicts))])
         `(define ,label ,new-info ,tail))]))

  (match p
    [`(module ,info ,defs ... ,tail)
     (let*-values ([(locals ust conflicts) (conflict-analysis-info-setup info)]
                   [(tail-conflicts) (conflict-analysis-tail ust tail conflicts)])
       `(module ,(info-set info 'conflicts tail-conflicts)
          ,@(map conflict-analysis-definition defs)
          ,tail))]))

(module+ tests
  (check-equal?
    (conflict-analysis
    '(module
          ((locals (x.1 y.2))
          (call-undead ())
          (new-frames ())
          (undead-out
            ((x.1 r15) (y.2 x.1 r15) ((y.2 x.1 r15) ((r15) ()) ((r15) ())))))
        (begin
          (set! x.1 3)
          (set! y.2 x.1)
          (if (> y.2 x.1)
              (begin (set! rax x.1) (jump r15))
              (begin (set! rax y.2) (jump r15))))))
    '(module
        ((locals (x.1 y.2))
          (call-undead ())
          (new-frames ())
          (undead-out ((x.1 r15) (y.2 x.1 r15) ((y.2 x.1 r15) ((r15) ()) ((r15) ()))))
          (conflicts ((y.2 (r15)) (x.1 (r15)) (r15 (rax y.2 x.1)) (rax (r15)))))
      (begin
        (set! x.1 3)
        (set! y.2 x.1)
        (if (> y.2 x.1)
            (begin (set! rax x.1) (jump r15))
            (begin (set! rax y.2) (jump r15))))))

  (check-equal?
    (conflict-analysis
    '(module
          ((locals ()) (new-frames ()) (call-undead ()) (undead-out ((r15) ())))
        (begin (set! rax 1) (jump r15))))
    '(module
        ((locals ())
          (new-frames ())
          (call-undead ())
          (undead-out ((r15) ()))
          (conflicts ((rax (r15)) (r15 (rax)))))
      (begin (set! rax 1) (jump r15))))

  (check-equal?
    (conflict-analysis
    '(module
          ((locals (x.1))
          (new-frames ())
          (call-undead ())
          (undead-out ((x.1 r15) (r15) ())))
        (begin (set! x.1 42) (set! rax x.1) (jump r15))))
    '(module
        ((locals (x.1))
          (new-frames ())
          (call-undead ())
          (undead-out ((x.1 r15) (r15) ()))
          (conflicts ((x.1 (r15)) (r15 (rax x.1)) (rax (r15)))))
      (begin (set! x.1 42) (set! rax x.1) (jump r15))))

  (check-equal?
    (conflict-analysis
    '(module
          ((locals (x.1 y.2))
          (new-frames ())
          (call-undead ())
          (undead-out ((x.1 r15) (y.2 x.1 r15) (x.1 r15) (r15) ())))
        (begin
          (set! x.1 1)
          (set! y.2 2)
          (set! x.1 (+ x.1 y.2))
          (set! rax x.1)
          (jump r15))))
    '(module
        ((locals (x.1 y.2))
          (new-frames ())
          (call-undead ())
          (undead-out ((x.1 r15) (y.2 x.1 r15) (x.1 r15) (r15) ()))
          (conflicts
          ((y.2 (r15 x.1)) (x.1 (y.2 r15)) (r15 (rax y.2 x.1)) (rax (r15)))))
      (begin
        (set! x.1 1)
        (set! y.2 2)
        (set! x.1 (+ x.1 y.2))
        (set! rax x.1)
        (jump r15))))

  (check-equal?
    (conflict-analysis
    '(module
          ((locals (x.1 y.2))
          (new-frames ())
          (call-undead ())
          (undead-out
            ((x.1 r15) (y.2 x.1 r15) ((y.2 x.1 r15) ((r15) ()) ((r15) ())))))
        (begin
          (set! x.1 3)
          (set! y.2 x.1)
          (if (> y.2 x.1)
              (begin (set! rax x.1) (jump r15))
              (begin (set! rax y.2) (jump r15))))))
    '(module
        ((locals (x.1 y.2))
          (new-frames ())
          (call-undead ())
          (undead-out ((x.1 r15) (y.2 x.1 r15) ((y.2 x.1 r15) ((r15) ()) ((r15) ()))))
          (conflicts ((y.2 (r15)) (x.1 (r15)) (r15 (rax y.2 x.1)) (rax (r15)))))
      (begin
        (set! x.1 3)
        (set! y.2 x.1)
        (if (> y.2 x.1)
            (begin (set! rax x.1) (jump r15))
            (begin (set! rax y.2) (jump r15))))))

  (check-equal?
    (conflict-analysis
    '(module
          ((locals (x.1 y.1))
          (new-frames ())
          (call-undead ())
          (undead-out ((x.1) (y.1 x.1) (y.1 x.1))))
        (define L.halt.1
          ((locals (a.1 b.1))
          (new-frames ())
          (undead-out ((a.1 r15) (r15) ()))
          (call-undead ()))
          (begin (set! a.1 (+ a.1 b.1)) (set! rax a.1) (jump r15)))
        (begin (set! x.1 5) (set! y.1 6) (jump L.halt.1 x.1 y.1))))
    '(module
        ((locals (x.1 y.1))
          (new-frames ())
          (call-undead ())
          (undead-out ((x.1) (y.1 x.1) (y.1 x.1)))
          (conflicts ((y.1 (x.1)) (x.1 (y.1)))))
      (define L.halt.1
        ((locals (a.1 b.1))
          (new-frames ())
          (undead-out ((a.1 r15) (r15) ()))
          (call-undead ())
          (conflicts ((b.1 ()) (a.1 (r15)) (r15 (rax a.1)) (rax (r15)))))
        (begin (set! a.1 (+ a.1 b.1)) (set! rax a.1) (jump r15)))
      (begin (set! x.1 5) (set! y.1 6) (jump L.halt.1 x.1 y.1))))

  (check-equal?
    (conflict-analysis
    '(module
          ((new-frames ())
          (locals (tmp.1 tmp-ra.2))
          (call-undead ())
          (undead-out
            ((r12 tmp-ra.2 rbp)
            ((r12 tmp.1 tmp-ra.2 rbp) (tmp.1 tmp-ra.2 rbp))
            (tmp-ra.2 rbp tmp.1)
            (rbp tmp-ra.2 tmp.1)
            (tmp.1 tmp-ra.2 rbp)
            (tmp-ra.2 rax rbp)
            (rax rbp))))
        (begin
          (set! tmp-ra.2 r15)
          (begin (set! tmp.1 r12) (set! r12 (+ r12 16)))
          (set! tmp.1 (+ tmp.1 1))
          (mset! tmp.1 -1 40)
          (mset! tmp.1 7 48)
          (set! rax tmp.1)
          (jump tmp-ra.2 rbp rax)))
    )
    '(module
        ((new-frames ())
          (locals (tmp.1 tmp-ra.2))
          (call-undead ())
          (undead-out
          ((r12 tmp-ra.2 rbp)
            ((r12 tmp.1 tmp-ra.2 rbp) (tmp.1 tmp-ra.2 rbp))
            (tmp-ra.2 rbp tmp.1)
            (rbp tmp-ra.2 tmp.1)
            (tmp.1 tmp-ra.2 rbp)
            (tmp-ra.2 rax rbp)
            (rax rbp)))
          (conflicts
          ((tmp-ra.2 (rax tmp.1 rbp r12))
            (tmp.1 (r12 rbp tmp-ra.2))
            (r12 (rbp tmp.1 tmp-ra.2))
            (rbp (rax r12 tmp.1 tmp-ra.2))
            (rax (rbp tmp-ra.2)))))
      (begin
        (set! tmp-ra.2 r15)
        (begin (set! tmp.1 r12) (set! r12 (+ r12 16)))
        (set! tmp.1 (+ tmp.1 1))
        (mset! tmp.1 -1 40)
        (mset! tmp.1 7 48)
        (set! rax tmp.1)
        (jump tmp-ra.2 rbp rax))))

  (check-equal?
    (conflict-analysis
    '(module
          ((new-frames ())
          (locals (tmp.1 tmp.2 tmp-ra.3))
          (call-undead ())
          (undead-out
            ((r12 tmp-ra.3 rbp)
            ((r12 tmp.2 tmp-ra.3 rbp) (tmp.2 tmp-ra.3 rbp))
            (tmp-ra.3 rbp tmp.2)
            (rbp tmp-ra.3 tmp.2)
            (tmp.2 tmp-ra.3 rbp)
            (tmp.1 tmp-ra.3 rbp)
            (tmp-ra.3 rax rbp)
            (rax rbp))))
        (begin
          (set! tmp-ra.3 r15)
          (begin (set! tmp.2 r12) (set! r12 (+ r12 16)))
          (set! tmp.2 (+ tmp.2 1))
          (mset! tmp.2 -1 40)
          (mset! tmp.2 7 48)
          (set! tmp.1 tmp.2)
          (set! rax (mref tmp.1 -1))
          (jump tmp-ra.3 rbp rax))))
    '(module
        ((new-frames ())
          (locals (tmp.1 tmp.2 tmp-ra.3))
          (call-undead ())
          (undead-out
          ((r12 tmp-ra.3 rbp)
            ((r12 tmp.2 tmp-ra.3 rbp) (tmp.2 tmp-ra.3 rbp))
            (tmp-ra.3 rbp tmp.2)
            (rbp tmp-ra.3 tmp.2)
            (tmp.2 tmp-ra.3 rbp)
            (tmp.1 tmp-ra.3 rbp)
            (tmp-ra.3 rax rbp)
            (rax rbp)))
          (conflicts
          ((tmp-ra.3 (rax tmp.1 tmp.2 rbp r12))
            (tmp.2 (r12 rbp tmp-ra.3))
            (tmp.1 (rbp tmp-ra.3))
            (r12 (rbp tmp.2 tmp-ra.3))
            (rbp (rax tmp.1 r12 tmp.2 tmp-ra.3))
            (rax (rbp tmp-ra.3)))))
      (begin
        (set! tmp-ra.3 r15)
        (begin (set! tmp.2 r12) (set! r12 (+ r12 16)))
        (set! tmp.2 (+ tmp.2 1))
        (mset! tmp.2 -1 40)
        (mset! tmp.2 7 48)
        (set! tmp.1 tmp.2)
        (set! rax (mref tmp.1 -1))
        (jump tmp-ra.3 rbp rax))))

  (check-equal?
    (conflict-analysis
    '(module
          ((new-frames ())
          (locals (tmp.1 tmp.3 tmp.2 tmp-ra.3))
          (call-undead ())
          (undead-out
            ((r12 rbp tmp-ra.3)
            ((r12 tmp.2 rbp tmp-ra.3) (tmp.2 rbp tmp-ra.3))
            (tmp.3 rbp tmp-ra.3)
            (rbp tmp-ra.3 tmp.3)
            (tmp.3 tmp-ra.3 rbp)
            (tmp.1 tmp-ra.3 rbp)
            (tmp-ra.3 rax rbp)
            (rax rbp))))
        (begin
          (set! tmp-ra.3 r15)
          (begin (set! tmp.2 r12) (set! r12 (+ r12 32)))
          (set! tmp.3 tmp.2)
          (set! tmp.3 (+ tmp.3 3))
          (mset! tmp.3 -3 24)
          (set! tmp.1 tmp.3)
          (set! rax (mref tmp.1 53))
          (jump tmp-ra.3 rbp rax))))
    '(module
        ((new-frames ())
          (locals (tmp.1 tmp.3 tmp.2 tmp-ra.3))
          (call-undead ())
          (undead-out
          ((r12 rbp tmp-ra.3)
            ((r12 tmp.2 rbp tmp-ra.3) (tmp.2 rbp tmp-ra.3))
            (tmp.3 rbp tmp-ra.3)
            (rbp tmp-ra.3 tmp.3)
            (tmp.3 tmp-ra.3 rbp)
            (tmp.1 tmp-ra.3 rbp)
            (tmp-ra.3 rax rbp)
            (rax rbp)))
          (conflicts
          ((tmp-ra.3 (rax tmp.1 tmp.3 tmp.2 rbp r12))
            (tmp.2 (r12 tmp-ra.3 rbp))
            (tmp.3 (tmp-ra.3 rbp))
            (tmp.1 (rbp tmp-ra.3))
            (r12 (rbp tmp.2 tmp-ra.3))
            (rbp (rax tmp.1 tmp.3 r12 tmp.2 tmp-ra.3))
            (rax (rbp tmp-ra.3)))))
      (begin
        (set! tmp-ra.3 r15)
        (begin (set! tmp.2 r12) (set! r12 (+ r12 32)))
        (set! tmp.3 tmp.2)
        (set! tmp.3 (+ tmp.3 3))
        (mset! tmp.3 -3 24)
        (set! tmp.1 tmp.3)
        (set! rax (mref tmp.1 53))
        (jump tmp-ra.3 rbp rax))))
)