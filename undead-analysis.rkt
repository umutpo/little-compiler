#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide undead-analysis)

(define (my-flatten lst)
  (foldr append '() lst))

;; Performs undead analysis, compiling Asm-pred-lang v6/locals to Asm-pred-lang v6/undead
;; by decorating programs with their undead-set trees.
;;
;; Asm-pred-lang-v6/locals -> Asm-pred-lang-v6/undead
(define (undead-analysis p)

  ;; Any -> Boolean
  (define (loc? e)
    (or (aloc? e) (register? e) (fvar? e)))

  ;; asm-pred-lang-v5/locals.Pred (Set (listof aloc)) -> (values (Set (listof aloc)) (list (Set (listof aloc))))
  (define (undead-analysis-pred e undead-out call-undead-box)
    (match e
      [`(true) (values undead-out (list undead-out) call-undead-box)]
      [`(false) (values undead-out (list undead-out) call-undead-box)]
      [`(not ,pred)
       (let-values ([(undead-in ust call-undead-box-pred) (undead-analysis-pred pred undead-out call-undead-box)])
         (values undead-in `(,@ust) call-undead-box-pred))]
      [`(begin ,effects ... ,pred)
       (let-values ([(undead-in ust call-undead-box-pred) (undead-analysis-pred pred undead-out call-undead-box)])
         (let ([ust-effs (list)]
               [call-undead-box call-undead-box-pred])
           (for ([eff (reverse effects)])
             (let-values ([(undead-out ust-eff call-undead-box-eff) (undead-analysis-effect eff undead-in call-undead-box)])
               (set! ust-effs (append ust-eff ust-effs))
               (set! undead-in undead-out)))
           (values undead-in (list (append ust-effs ust)) call-undead-box)))]
      [`(if ,pred ,pred1 ,pred2)
       (let*-values ([(undead-in-1 ust1 call-undead-box-1) (undead-analysis-pred pred1 undead-out call-undead-box)]
                     [(undead-in-2 ust2 call-undead-box-2) (undead-analysis-pred pred2 undead-out call-undead-box)]
                     [(undead-in-pred ust-pred call-undead-box-pred) (undead-analysis-pred pred (set-union undead-in-1 undead-in-2) call-undead-box-2)])
         (values undead-in-pred (list `(,@ust-pred ,@ust1 ,@ust2)) call-undead-box-pred))]
      [`(,relop ,loc ,opand)
       (let ([undead-in undead-out])
         (set! undead-out (set-add undead-out loc))
         (when (loc? opand) (set! undead-out (set-add undead-out opand)))
         (values undead-out (list undead-in) call-undead-box))]))

  ;; asm-pred-lang-v5/locals.Tail -> (values (Set (listof aloc)) (list (Set (listof aloc))))
  (define (undead-analysis-tail e call-undead-box)
    (match e
      [`(jump ,trg ,locs ...)
       (if (loc? trg)
           (values `(,@(reverse locs) ,trg) (list (reverse locs)) call-undead-box)
           (values (reverse locs) (list (reverse locs)) call-undead-box))]
      [`(begin ,effects ... ,tail)
       (let-values ([(undead-in ust call-undead-box-tail) (undead-analysis-tail tail call-undead-box)])
         (let ([ust-effs (list)]
               [call-undead-box call-undead-box-tail])
           (for ([eff (reverse effects)])
             (let-values ([(undead-out ust-eff call-undead-box-eff) (undead-analysis-effect eff undead-in call-undead-box)])
               (set! ust-effs (append ust-eff ust-effs))
               (set! undead-in undead-out)
               (set-box! call-undead-box (unbox call-undead-box-eff))))
           (values undead-in (list (append ust-effs ust)) call-undead-box)))]
      [`(if ,pred ,tail1 ,tail2)
       (let*-values ([(undead-in-1 ust1 call-undead-box-1) (undead-analysis-tail tail1 call-undead-box)]
                     [(undead-in-2 ust2 call-undead-box-2) (undead-analysis-tail tail2 call-undead-box)])
         (let-values ([(undead-in-pred ust-pred call-undead-box-pred) (undead-analysis-pred pred (set-union undead-in-1 undead-in-2) call-undead-box-2)])
           (values undead-in-pred (list `(,@ust-pred ,@ust1 ,@ust2)) call-undead-box-pred)))]))

  ;; asm-pred-lang-v5/locals.Effect (Set (listof aloc)) -> (values (Set (listof aloc)) (list (Set (listof aloc))))
  (define (undead-analysis-effect e undead-out call-undead-box)
    (match e
      [`(set! ,loc1 (mref ,loc2 ,index))
       (let* ([undead-in undead-out]
              [undead-out (set-remove undead-in loc1)])
         (set! undead-out (set-add undead-out loc2))
         (when (loc? index) (set! undead-out (set-add undead-out index)))
         (values undead-out (list undead-in) call-undead-box))]
      [`(set! ,loc (,binop ,loc ,opand))
       (let* ([undead-in undead-out]
              [undead-out (set-remove undead-in loc)])
         (set! undead-out (set-add undead-out loc))
         (when (loc? opand) (set! undead-out (set-add undead-out opand)))
         (values undead-out (list undead-in) call-undead-box))]
      [`(begin ,effects ...)
       (let ([ust-effs (list)])
         (for ([eff (reverse effects)])
           (let-values ([(new-undead-out ust-eff call-undead-box-eff) (undead-analysis-effect eff undead-out call-undead-box)])
             (set! ust-effs (append ust-eff ust-effs))
             (set! undead-out new-undead-out)
             (set-box! call-undead-box (unbox call-undead-box-eff))))
         (values undead-out (list ust-effs) call-undead-box))]
      [`(if ,pred ,effect1 ,effect2)
       (let*-values ([(undead-in-1 ust1 call-undead-box-1) (undead-analysis-effect effect1 undead-out call-undead-box)]
                     [(undead-in-2 ust2 call-undead-box-2) (undead-analysis-effect effect2 undead-out call-undead-box)]
                     [(undead-in-pred ust-pred call-undead-box-pred) (undead-analysis-pred pred (set-union undead-in-1 undead-in-2) call-undead-box-2)])
         (values undead-in-pred (list `(,@ust-pred ,@ust1 ,@ust2)) call-undead-box-pred))]
      [`(set! ,loc ,triv)
       (let* ([undead-in undead-out]
              [undead-out (set-remove undead-in loc)])
         (when (loc? triv) (set! undead-out (set-add undead-out triv)))
         (values undead-out (list undead-in) call-undead-box))]
      [`(mset! ,loc ,index ,triv)
       (let* ([undead-in undead-out]
              [undead-out (set-remove undead-in loc)])
         (set! undead-out (set-add undead-out loc))
         (when (loc? index) (set! undead-out (set-add undead-out index)))
         (when (loc? triv) (set! undead-out (set-add undead-out triv)))
         (values undead-out (list undead-in) call-undead-box))]
      [`(return-point ,label ,tail)
       (let*-values ([(undead-in ust call-undead-box-tail) (undead-analysis-tail tail call-undead-box)]
                     [(undead-call) (unbox call-undead-box-tail)])
         (for ([e undead-out])
           (when (or (aloc? e) (fvar? e))
             (set! undead-call (set-union (my-flatten (list undead-call)) (list e)))))
         (values (set-remove (set-union undead-in undead-out) (current-return-value-register)) `((,undead-out ,(my-flatten ust))) (box undead-call)))]))


  ;; asm-pred-lang-v5/locals.Definition -> asm-pred-lang-v5/undead.Definition
  (define (undead-analysis-definition def)
    (match def
      [`(define ,label ,info ,tail)
       (let*-values ([(x ust call-undead-box) (undead-analysis-tail tail (box '()))]
                     [(new-info) (info-set (info-set info 'undead-out (first ust)) 'call-undead (unbox call-undead-box))])
         `(define ,label ,new-info ,tail))]))

  ;; asm-pred-lang-v5/locals.Opand -> (list aloc) or (list)
  (define (undead-analysis-opand e)
    (if (loc? e)
        (list e)
        (list)))

  (match p
    [`(module ,info ,defs ... ,tail)
     (let*-values ([(_ ust call-undead-box) (undead-analysis-tail tail (box '()))]
                   [(new-info) (info-set (info-set info 'call-undead (unbox call-undead-box)) 'undead-out (first ust))])
       `(module ,new-info ,@(map undead-analysis-definition defs) ,tail))]))

(module+ tests
  (check-equal?
    (undead-analysis
    '(module ((locals (x.1 y.2 b.3 c.4)) (new-frames (())))
        (begin
          (set! x.1 5)
          (set! y.2 x.1)
          (begin
            (set! b.3 x.1)
            (set! b.3 (+ b.3 y.2))
            (set! c.4 b.3)
            (if (= c.4 b.3)
                (begin
                  (set! rax c.4)
                  (jump r15))
                (begin
                  (set! x.1 c.4)
                  (begin
                    (set! rax c.4)
                    (jump r15))))))))
    '(module
        ((locals (x.1 y.2 b.3 c.4))
          (new-frames (()))
          (call-undead ())
          (undead-out
          ((x.1 r15)
            (x.1 y.2 r15)
            ((y.2 b.3 r15)
            (b.3 r15)
            (b.3 c.4 r15)
            ((c.4 r15) ((r15) ()) ((c.4 r15) ((r15) ())))))))
      (begin
        (set! x.1 5)
        (set! y.2 x.1)
        (begin
          (set! b.3 x.1)
          (set! b.3 (+ b.3 y.2))
          (set! c.4 b.3)
          (if (= c.4 b.3)
              (begin (set! rax c.4) (jump r15))
              (begin (set! x.1 c.4) (begin (set! rax c.4) (jump r15))))))))

  (check-equal?
    (undead-analysis
    '(module ((locals ()) (new-frames (()))) (begin (set! rax 5) (jump r15))))
    '(module
        ((locals ()) (new-frames (())) (call-undead ()) (undead-out ((r15) ())))
      (begin (set! rax 5) (jump r15))))

  (check-equal?
    (undead-analysis
    '(module ((locals (w.1 y.1 x.1)) (new-frames (())))
        (begin
          (set! x.1 0)
          (set! w.1 0)
          (set! y.1 x.1)
          (set! w.1 (+ w.1 x.1))
          (set! w.1 (+ w.1 y.1))
          (begin (set! rax w.1) (jump r15)))))
    '(module
        ((locals (w.1 y.1 x.1))
          (new-frames (()))
          (call-undead ())
          (undead-out
          ((x.1 r15)
            (x.1 w.1 r15)
            (x.1 w.1 y.1 r15)
            (y.1 w.1 r15)
            (w.1 r15)
            ((r15) ()))))
      (begin
        (set! x.1 0)
        (set! w.1 0)
        (set! y.1 x.1)
        (set! w.1 (+ w.1 x.1))
        (set! w.1 (+ w.1 y.1))
        (begin (set! rax w.1) (jump r15)))))

  (check-equal?
    (undead-analysis
    '(module ((locals (x.1)) (new-frames (()))) (begin (set! x.1 5) (begin (set! rax x.1) (jump r15)))))
    '(module
        ((locals (x.1))
          (new-frames (()))
          (call-undead ())
          (undead-out ((x.1 r15) ((r15) ()))))
      (begin (set! x.1 5) (begin (set! rax x.1) (jump r15)))))

  (check-equal?
    (undead-analysis
    '(module
          ((new-frames ()) (locals (tmp-ra.2)))
        (define L.swap.1
          ((new-frames (())) (locals (z.3 tmp-ra.1 x.1 y.2)))
          (begin
            (set! tmp-ra.1 r15)
            (set! x.1 rdi)
            (set! y.2 rsi)
            (if (< y.2 x.1)
                (begin (set! rax x.1) (jump tmp-ra.1 rbp rax))
                (begin
                  (return-point L.rp.1
                                (begin
                                  (set! rsi x.1)
                                  (set! rdi y.2)
                                  (set! r15 L.rp.1)
                                  (jump L.swap.1 rbp r15 rdi rsi)))
                  (set! z.3 rax)
                  (set! rax z.3)
                  (jump tmp-ra.1 rbp rax)))))
        (begin
          (set! tmp-ra.2 r15)
          (set! rsi 2)
          (set! rdi 1)
          (set! r15 tmp-ra.2)
          (jump L.swap.1 rbp r15 rdi rsi))))
    '(module
        ((new-frames ())
          (locals (tmp-ra.2))
          (call-undead ())
          (undead-out
          ((tmp-ra.2 rbp)
            (tmp-ra.2 rsi rbp)
            (tmp-ra.2 rsi rdi rbp)
            (rsi rdi r15 rbp)
            (rsi rdi r15 rbp))))
      (define L.swap.1
        ((new-frames (()))
          (locals (z.3 tmp-ra.1 x.1 y.2))
          (undead-out
          ((rdi rsi rbp tmp-ra.1)
            (rsi x.1 rbp tmp-ra.1)
            (y.2 x.1 rbp tmp-ra.1)
            ((y.2 x.1 rbp tmp-ra.1)
            ((rax rbp tmp-ra.1) (rax rbp))
            (((rax rbp tmp-ra.1)
              ((y.2 rsi rbp) (rsi rdi rbp) (rsi rdi r15 rbp) (rsi rdi r15 rbp)))
              (z.3 rbp tmp-ra.1)
              (rax rbp tmp-ra.1)
              (rax rbp)))))
          (call-undead (tmp-ra.1)))
        (begin
          (set! tmp-ra.1 r15)
          (set! x.1 rdi)
          (set! y.2 rsi)
          (if (< y.2 x.1)
              (begin (set! rax x.1) (jump tmp-ra.1 rbp rax))
              (begin
                (return-point L.rp.1
                              (begin
                                (set! rsi x.1)
                                (set! rdi y.2)
                                (set! r15 L.rp.1)
                                (jump L.swap.1 rbp r15 rdi rsi)))
                (set! z.3 rax)
                (set! rax z.3)
                (jump tmp-ra.1 rbp rax)))))
      (begin
        (set! tmp-ra.2 r15)
        (set! rsi 2)
        (set! rdi 1)
        (set! r15 tmp-ra.2)
        (jump L.swap.1 rbp r15 rdi rsi))))

  (check-equal?
    (parameterize ([current-parameter-registers '()])
      (undead-analysis
      '(module
            ((new-frames ()) (locals (tmp-ra.4)))
          (define L.swap.1
            ((new-frames ((nfv.2 nfv.3))) (locals (nfv.2 nfv.3 z.3 tmp-ra.1 x.1 y.2)))
            (begin
              (set! tmp-ra.1 r15)
              (set! x.1 fv0)
              (set! y.2 fv1)
              (if (< y.2 x.1)
                  (begin (set! rax x.1) (jump tmp-ra.1 rbp rax))
                  (begin
                    (return-point L.rp.1
                                  (begin
                                    (set! nfv.3 x.1)
                                    (set! nfv.2 y.2)
                                    (set! r15 L.rp.1)
                                    (jump L.swap.1 rbp r15 nfv.2 nfv.3)))
                    (set! z.3 rax)
                    (set! rax z.3)
                    (jump tmp-ra.1 rbp rax)))))
          (begin
            (set! tmp-ra.4 r15)
            (set! fv1 2)
            (set! fv0 1)
            (set! r15 tmp-ra.4)
            (jump L.swap.1 rbp r15 fv0 fv1)))))
    '(module
        ((new-frames ())
          (locals (tmp-ra.4))
          (call-undead ())
          (undead-out
          ((tmp-ra.4 rbp)
            (tmp-ra.4 fv1 rbp)
            (tmp-ra.4 fv1 fv0 rbp)
            (fv1 fv0 r15 rbp)
            (fv1 fv0 r15 rbp))))
      (define L.swap.1
        ((new-frames ((nfv.2 nfv.3)))
          (locals (nfv.2 nfv.3 z.3 tmp-ra.1 x.1 y.2))
          (undead-out
          ((fv0 fv1 rbp tmp-ra.1)
            (fv1 x.1 rbp tmp-ra.1)
            (y.2 x.1 rbp tmp-ra.1)
            ((y.2 x.1 rbp tmp-ra.1)
            ((rax rbp tmp-ra.1) (rax rbp))
            (((rax rbp tmp-ra.1)
              ((y.2 nfv.3 rbp)
                (nfv.3 nfv.2 rbp)
                (nfv.3 nfv.2 r15 rbp)
                (nfv.3 nfv.2 r15 rbp)))
              (z.3 rbp tmp-ra.1)
              (rax rbp tmp-ra.1)
              (rax rbp)))))
          (call-undead (tmp-ra.1)))
        (begin
          (set! tmp-ra.1 r15)
          (set! x.1 fv0)
          (set! y.2 fv1)
          (if (< y.2 x.1)
              (begin (set! rax x.1) (jump tmp-ra.1 rbp rax))
              (begin
                (return-point L.rp.1
                              (begin
                                (set! nfv.3 x.1)
                                (set! nfv.2 y.2)
                                (set! r15 L.rp.1)
                                (jump L.swap.1 rbp r15 nfv.2 nfv.3)))
                (set! z.3 rax)
                (set! rax z.3)
                (jump tmp-ra.1 rbp rax)))))
      (begin
        (set! tmp-ra.4 r15)
        (set! fv1 2)
        (set! fv0 1)
        (set! r15 tmp-ra.4)
        (jump L.swap.1 rbp r15 fv0 fv1))))

  (check-equal?
    (undead-analysis
    '(module
          ((new-frames ()) (locals (ra.12)))
        (define L.fact.4
          ((new-frames ((nfv.16)))
          (locals (ra.13 x.9 tmp.14 tmp.15 new-n.10 nfv.16 factn-1.11 tmp.17)))
          (begin
            (set! x.9 fv0)
            (set! ra.13 r15)
            (if (= x.9 0)
                (begin (set! rax 1) (jump ra.13 rbp rax))
                (begin
                  (set! tmp.14 -1)
                  (set! tmp.15 x.9)
                  (set! tmp.15 (+ tmp.15 tmp.14))
                  (set! new-n.10 tmp.15)
                  (return-point
                  L.rp.6
                  (begin
                    (set! nfv.16 new-n.10)
                    (set! r15 L.rp.6)
                    (jump L.fact.4 rbp r15 nfv.16)))
                  (set! factn-1.11 rax)
                  (set! tmp.17 x.9)
                  (set! tmp.17 (* tmp.17 factn-1.11))
                  (set! rax tmp.17)
                  (jump ra.13 rbp rax)))))
        (begin
          (set! ra.12 r15)
          (set! fv0 5)
          (set! r15 ra.12)
          (jump L.fact.4 rbp r15 fv0))))
    '(module
        ((new-frames ())
          (locals (ra.12))
          (call-undead ())
          (undead-out ((ra.12 rbp) (ra.12 fv0 rbp) (fv0 r15 rbp) (fv0 r15 rbp))))
      (define L.fact.4
        ((new-frames ((nfv.16)))
          (locals (ra.13 x.9 tmp.14 tmp.15 new-n.10 nfv.16 factn-1.11 tmp.17))
          (undead-out
          ((r15 x.9 rbp)
            (x.9 rbp ra.13)
            ((x.9 rbp ra.13)
            ((rax rbp ra.13) (rax rbp))
            ((tmp.14 ra.13 x.9 rbp)
              (tmp.14 tmp.15 ra.13 x.9 rbp)
              (tmp.15 ra.13 x.9 rbp)
              (ra.13 x.9 new-n.10 rbp)
              ((rax x.9 rbp ra.13) ((nfv.16 rbp) (nfv.16 r15 rbp) (nfv.16 r15 rbp)))
              (x.9 factn-1.11 rbp ra.13)
              (factn-1.11 tmp.17 rbp ra.13)
              (tmp.17 rbp ra.13)
              (rax rbp ra.13)
              (rax rbp)))))
          (call-undead (ra.13 x.9)))
        (begin
          (set! x.9 fv0)
          (set! ra.13 r15)
          (if (= x.9 0)
              (begin (set! rax 1) (jump ra.13 rbp rax))
              (begin
                (set! tmp.14 -1)
                (set! tmp.15 x.9)
                (set! tmp.15 (+ tmp.15 tmp.14))
                (set! new-n.10 tmp.15)
                (return-point L.rp.6
                              (begin
                                (set! nfv.16 new-n.10)
                                (set! r15 L.rp.6)
                                (jump L.fact.4 rbp r15 nfv.16)))
                (set! factn-1.11 rax)
                (set! tmp.17 x.9)
                (set! tmp.17 (* tmp.17 factn-1.11))
                (set! rax tmp.17)
                (jump ra.13 rbp rax)))))
      (begin
        (set! ra.12 r15)
        (set! fv0 5)
        (set! r15 ra.12)
        (jump L.fact.4 rbp r15 fv0))))

  (check-equal?
    (undead-analysis
    '(module
          ((new-frames ()) (locals (tmp-ra.242 tmp.404 tmp.405 tmp.406 x.132 y.133 z.134)))
        (begin
          (begin (set! tmp-ra.242 r15))
          (begin (begin (set! x.132 20))
                (begin (set! y.133 21))
                (if (not (begin (set! tmp.404 x.132) (> tmp.404 12)))
                    (if (if (begin (begin (set! z.134 x.132))
                                    (begin (set! tmp.405 y.133) (< tmp.405 z.134)))
                            (true)
                            (false))
                        (begin (begin (set! rax 10))
                                (jump tmp-ra.242 rbp rax))
                        (begin (begin (set! rax 12))
                                (jump tmp-ra.242 rbp rax)))
                    (begin (begin (set! tmp.406 x.132)
                                  (set! tmp.406 (+ tmp.406 y.133))
                                  (set! rax tmp.406))
                            (jump tmp-ra.242 rbp rax)))))))
    '(module
        ((new-frames ())
          (locals (tmp-ra.242 tmp.404 tmp.405 tmp.406 x.132 y.133 z.134))
          (call-undead ())
          (undead-out
          (((rbp tmp-ra.242))
            (((x.132 rbp tmp-ra.242))
            ((x.132 y.133 rbp tmp-ra.242))
            (((tmp.404 x.132 y.133 rbp tmp-ra.242) (x.132 y.133 rbp tmp-ra.242))
              (((((y.133 z.134 rbp tmp-ra.242))
                ((z.134 tmp.405 rbp tmp-ra.242) (rbp tmp-ra.242)))
                (rbp tmp-ra.242)
                (rbp tmp-ra.242))
              (((rax rbp tmp-ra.242)) (rax rbp))
              (((rax rbp tmp-ra.242)) (rax rbp)))
              (((y.133 tmp.406 rbp tmp-ra.242)
                (tmp.406 rbp tmp-ra.242)
                (rax rbp tmp-ra.242))
              (rax rbp)))))))
      (begin
        (begin (set! tmp-ra.242 r15))
        (begin
          (begin (set! x.132 20))
          (begin (set! y.133 21))
          (if (not (begin (set! tmp.404 x.132) (> tmp.404 12)))
              (if (if (begin
                        (begin (set! z.134 x.132))
                        (begin (set! tmp.405 y.133) (< tmp.405 z.134)))
                      (true)
                      (false))
                  (begin (begin (set! rax 10)) (jump tmp-ra.242 rbp rax))
                  (begin (begin (set! rax 12)) (jump tmp-ra.242 rbp rax)))
              (begin
                (begin
                  (set! tmp.406 x.132)
                  (set! tmp.406 (+ tmp.406 y.133))
                  (set! rax tmp.406))
                (jump tmp-ra.242 rbp rax)))))))

  (check-equal?
    (undead-analysis
    '(module ((new-frames ()) (locals (tmp-ra.242 tmp.406 tmp.407 tmp.408 x.132 y.133 z.134)))
        (begin (begin (set! tmp-ra.242 r15))
              (begin (begin (set! x.132 20))
                      (begin (set! y.133 21))
                      (if (not (begin (set! tmp.406 x.132) (> tmp.406 12)))
                          (if (if (begin (begin (set! z.134 x.132))
                                        (begin (set! tmp.407 y.133) (< tmp.407 z.134)))
                                  (true)
                                  (false))
                              (begin (begin (set! rax 10))
                                    (jump tmp-ra.242 rbp rax))
                              (begin (begin (set! rax 12))
                                    (jump tmp-ra.242 rbp rax)))
                          (begin (begin (set! tmp.408 x.132)
                                        (set! tmp.408 (+ tmp.408 y.133))
                                        (set! rax tmp.408))
                                (jump tmp-ra.242 rbp rax)))))))
    '(module
        ((new-frames ())
          (locals (tmp-ra.242 tmp.406 tmp.407 tmp.408 x.132 y.133 z.134))
          (call-undead ())
          (undead-out
          (((rbp tmp-ra.242))
            (((x.132 rbp tmp-ra.242))
            ((x.132 y.133 rbp tmp-ra.242))
            (((tmp.406 x.132 y.133 rbp tmp-ra.242) (x.132 y.133 rbp tmp-ra.242))
              (((((y.133 z.134 rbp tmp-ra.242))
                ((z.134 tmp.407 rbp tmp-ra.242) (rbp tmp-ra.242)))
                (rbp tmp-ra.242)
                (rbp tmp-ra.242))
              (((rax rbp tmp-ra.242)) (rax rbp))
              (((rax rbp tmp-ra.242)) (rax rbp)))
              (((y.133 tmp.408 rbp tmp-ra.242)
                (tmp.408 rbp tmp-ra.242)
                (rax rbp tmp-ra.242))
              (rax rbp)))))))
      (begin
        (begin (set! tmp-ra.242 r15))
        (begin
          (begin (set! x.132 20))
          (begin (set! y.133 21))
          (if (not (begin (set! tmp.406 x.132) (> tmp.406 12)))
              (if (if (begin
                        (begin (set! z.134 x.132))
                        (begin (set! tmp.407 y.133) (< tmp.407 z.134)))
                      (true)
                      (false))
                  (begin (begin (set! rax 10)) (jump tmp-ra.242 rbp rax))
                  (begin (begin (set! rax 12)) (jump tmp-ra.242 rbp rax)))
              (begin
                (begin
                  (set! tmp.408 x.132)
                  (set! tmp.408 (+ tmp.408 y.133))
                  (set! rax tmp.408))
                (jump tmp-ra.242 rbp rax)))))))

  (check-equal?
    (undead-analysis
    '(module ((new-frames ()) (locals (tmp-ra.267)))
        (define L.fact.8 ((new-frames (())) (locals (tmp-ra.268 tmp.446 tmp.447 tmp.448 x.64 y.66 z.65)))
          (begin (begin (set! tmp-ra.268 r15))
                (begin (begin (set! x.64 rdi))
                        (if (begin (set! tmp.446 x.64) (= tmp.446 0))
                            (begin (begin (set! rax 1)) (jump tmp-ra.268 rbp rax))
                            (begin (begin (set! tmp.447 x.64) (set! tmp.447 (+ tmp.447 -1)) (set! z.65 tmp.447))
                                  (begin (begin (return-point L.rp.42 (begin (begin (set! rdi z.65))
                                                                              (begin (set! r15 L.rp.42)) (jump L.fact.8 rbp r15 rdi)))
                                                (begin (set! y.66 rax))) (begin (begin (set! tmp.448 x.64) (set! tmp.448 (* tmp.448 y.66)) (set! rax tmp.448)) (jump tmp-ra.268 rbp rax)))))))) (begin (begin (set! tmp-ra.267 r15))
                                                                                                                                                                                                        (begin (begin (set! rdi 10)) (begin (set! r15 tmp-ra.267)) (jump L.fact.8 rbp r15 rdi)))))
    '(module
        ((new-frames ())
          (locals (tmp-ra.267))
          (call-undead ())
          (undead-out
          (((tmp-ra.267 rbp))
            (((tmp-ra.267 rdi rbp)) ((rdi r15 rbp)) (rdi r15 rbp)))))
      (define L.fact.8
        ((new-frames (()))
          (locals (tmp-ra.268 tmp.446 tmp.447 tmp.448 x.64 y.66 z.65))
          (undead-out
          (((rdi rbp tmp-ra.268))
            (((x.64 rbp tmp-ra.268))
            (((tmp.446 x.64 rbp tmp-ra.268) (x.64 rbp tmp-ra.268))
              (((rax rbp tmp-ra.268)) (rax rbp))
              (((tmp.447 tmp-ra.268 x.64 rbp)
                (tmp.447 tmp-ra.268 x.64 rbp)
                (tmp-ra.268 x.64 z.65 rbp))
              ((((rax x.64 rbp tmp-ra.268)
                  (((rdi rbp)) ((rdi r15 rbp)) (rdi r15 rbp)))
                ((x.64 y.66 rbp tmp-ra.268)))
                (((y.66 tmp.448 rbp tmp-ra.268)
                  (tmp.448 rbp tmp-ra.268)
                  (rax rbp tmp-ra.268))
                (rax rbp))))))))
          (call-undead (tmp-ra.268 x.64)))
        (begin
          (begin (set! tmp-ra.268 r15))
          (begin
            (begin (set! x.64 rdi))
            (if (begin (set! tmp.446 x.64) (= tmp.446 0))
                (begin (begin (set! rax 1)) (jump tmp-ra.268 rbp rax))
                (begin
                  (begin
                    (set! tmp.447 x.64)
                    (set! tmp.447 (+ tmp.447 -1))
                    (set! z.65 tmp.447))
                  (begin
                    (begin
                      (return-point L.rp.42
                                    (begin
                                      (begin (set! rdi z.65))
                                      (begin (set! r15 L.rp.42))
                                      (jump L.fact.8 rbp r15 rdi)))
                      (begin (set! y.66 rax)))
                    (begin
                      (begin
                        (set! tmp.448 x.64)
                        (set! tmp.448 (* tmp.448 y.66))
                        (set! rax tmp.448))
                      (jump tmp-ra.268 rbp rax))))))))
      (begin
        (begin (set! tmp-ra.267 r15))
        (begin
          (begin (set! rdi 10))
          (begin (set! r15 tmp-ra.267))
          (jump L.fact.8 rbp r15 rdi)))))

  (check-equal?
    (undead-analysis
    '(module
          ((new-frames ())
          (locals (tmp-ra.506)))
        (define L.tmp.41
          ((new-frames ())
          (locals (tmp-ra.507 tmp.123 tmp.124 tmp.236 tmp.241 tmp.764 tmp.765)))
          (begin
            (begin (set! tmp-ra.507 r15))
            (begin
              (begin (set! tmp.123 rdi))
              (begin (set! tmp.124 rsi))
              (begin
                (begin
                  (begin
                    (begin (set! tmp.764 r12)
                          (set! r12 (+ r12 16)))
                    (set! tmp.241 tmp.764))
                  (begin (set! tmp.765 tmp.241)
                        (set! tmp.765 (+ tmp.765 1))
                        (set! tmp.236 tmp.765)))
                (begin (mset! tmp.236 -1 tmp.123)
                      (mset! tmp.236 7 tmp.124)
                      (begin
                        (begin (set! rax tmp.236))
                        (jump tmp-ra.507 rbp rax)))))))
        (begin
          (begin (set! tmp-ra.506 r15))
          (begin
            (begin (set! rsi 22))
            (begin (set! rdi 56))
            (begin (set! r15 tmp-ra.506))
            (jump L.tmp.41 rbp r15 rdi rsi)))))
    '(module
        ((new-frames ())
          (locals (tmp-ra.506))
          (call-undead ())
          (undead-out
          (((tmp-ra.506 rbp))
            (((tmp-ra.506 rsi rbp))
            ((tmp-ra.506 rsi rdi rbp))
            ((rsi rdi r15 rbp))
            (rsi rdi r15 rbp)))))
      (define L.tmp.41
        ((new-frames ())
          (locals (tmp-ra.507 tmp.123 tmp.124 tmp.236 tmp.241 tmp.764 tmp.765))
          (undead-out
          (((rdi rsi r12 rbp tmp-ra.507))
            (((rsi r12 tmp.123 rbp tmp-ra.507))
            ((r12 tmp.123 tmp.124 rbp tmp-ra.507))
            (((((r12 tmp.764 tmp.123 tmp.124 rbp tmp-ra.507)
                (tmp.764 tmp.123 tmp.124 rbp tmp-ra.507))
                (tmp.241 tmp.123 tmp.124 rbp tmp-ra.507))
              ((tmp.765 tmp.123 tmp.124 rbp tmp-ra.507)
                (tmp.765 tmp.123 tmp.124 rbp tmp-ra.507)
                (tmp.123 tmp.236 tmp.124 rbp tmp-ra.507)))
              ((tmp.124 tmp.236 rbp tmp-ra.507)
              (tmp.236 rbp tmp-ra.507)
              (((rax rbp tmp-ra.507)) (rax rbp)))))))
          (call-undead ()))
        (begin
          (begin (set! tmp-ra.507 r15))
          (begin
            (begin (set! tmp.123 rdi))
            (begin (set! tmp.124 rsi))
            (begin
              (begin
                (begin
                  (begin (set! tmp.764 r12) (set! r12 (+ r12 16)))
                  (set! tmp.241 tmp.764))
                (begin
                  (set! tmp.765 tmp.241)
                  (set! tmp.765 (+ tmp.765 1))
                  (set! tmp.236 tmp.765)))
              (begin
                (mset! tmp.236 -1 tmp.123)
                (mset! tmp.236 7 tmp.124)
                (begin (begin (set! rax tmp.236)) (jump tmp-ra.507 rbp rax)))))))
      (begin
        (begin (set! tmp-ra.506 r15))
        (begin
          (begin (set! rsi 22))
          (begin (set! rdi 56))
          (begin (set! r15 tmp-ra.506))
          (jump L.tmp.41 rbp r15 rdi rsi)))))

  (check-equal?
    (undead-analysis
    '(module
          ((new-frames ()) (locals (tmp.2 tmp.1 tmp.3 tmp-ra.4)))
        (begin
          (set! tmp-ra.4 r15)
          (begin (set! tmp.3 r12) (set! r12 (+ r12 16)))
          (set! tmp.1 tmp.3)
          (set! tmp.1 (+ tmp.1 1))
          (mset! tmp.1 -1 40)
          (mset! tmp.1 7 48)
          (set! tmp.2 tmp.1)
          (set! rax (mref tmp.2 -1))
          (jump tmp-ra.4 rbp rax))))
    '(module
        ((new-frames ())
          (locals (tmp.2 tmp.1 tmp.3 tmp-ra.4))
          (call-undead ())
          (undead-out
          ((r12 rbp tmp-ra.4)
            ((r12 tmp.3 rbp tmp-ra.4) (tmp.3 rbp tmp-ra.4))
            (tmp.1 rbp tmp-ra.4)
            (tmp.1 rbp tmp-ra.4)
            (tmp.1 rbp tmp-ra.4)
            (tmp.1 rbp tmp-ra.4)
            (tmp.2 rbp tmp-ra.4)
            (rax rbp tmp-ra.4)
            (rax rbp))))
      (begin
        (set! tmp-ra.4 r15)
        (begin (set! tmp.3 r12) (set! r12 (+ r12 16)))
        (set! tmp.1 tmp.3)
        (set! tmp.1 (+ tmp.1 1))
        (mset! tmp.1 -1 40)
        (mset! tmp.1 7 48)
        (set! tmp.2 tmp.1)
        (set! rax (mref tmp.2 -1))
        (jump tmp-ra.4 rbp rax))))
)