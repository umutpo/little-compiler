#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide replace-locations)

;; Compiles the given Asm-lang-v5/assignments program to Nested-asm-lang-v5
;; by replacing each abstract location with its corresponding physical location
;; in the info field
;;
;; asm-pred-lang-v8/assignments -> nested-asm-lang-fvars-v8
(define (replace-locations p)

  ;; (source Triv) (Set aloc -> triv) -> (Target Triv)
  (define (replace-triv-name t assignments)
    (if (aloc? t)
        (info-ref assignments t)
        t))

  ;; (Source Pred) (Set aloc -> triv) -> (Target Pred)
  (define (replace-locations-pred e assignments)
    (match e
      [`(true) `(true)]
      [`(false) `(false)]
      [`(not ,pred) `(not ,(replace-locations-pred pred assignments))]
      [`(begin ,effects ... ,pred)
       `(begin ,@(map (lambda (e) (replace-locations-effect e assignments)) effects)
               ,(replace-locations-pred pred assignments))]
      [`(if ,pred ,pred1 ,pred2)
       `(if ,(replace-locations-pred pred assignments)
            ,(replace-locations-pred pred1 assignments)
            ,(replace-locations-pred pred2 assignments))]
      [`(,relop ,loc ,triv) `(,relop ,(replace-triv-name loc assignments) ,(replace-triv-name triv assignments))]))

  ;; (Source Effect) (Set aloc -> triv) -> (Target Effect)
  (define (replace-locations-effect e assignments)
    (match e
      [`(set! ,loc_1 (mref ,loc_2 ,index))
        `(set! ,(replace-triv-name loc_1 assignments)
          (mref ,(replace-triv-name loc_2 assignments) ,(replace-triv-name index assignments)))]
      [`(set! ,loc (,binop ,loc ,triv))
       `(set! ,(replace-triv-name loc assignments)
              (,binop ,(replace-triv-name loc assignments) ,(replace-triv-name triv assignments)))]
      [`(set! ,loc ,triv)
       `(set! ,(replace-triv-name loc assignments) ,(replace-triv-name triv assignments))]
      [`(mset! ,loc ,index ,triv) 
        `(mset! ,(replace-triv-name loc assignments)
          ,(replace-triv-name index assignments) ,(replace-triv-name triv assignments))]
      [`(begin ,effects ... ,effect)
       `(begin ,@(map (lambda (e) (replace-locations-effect e assignments)) effects)
               ,(replace-locations-effect effect assignments))]
      [`(if ,pred ,effect1 ,effect2)
       `(if ,(replace-locations-pred pred assignments)
            ,(replace-locations-effect effect1 assignments)
            ,(replace-locations-effect effect2 assignments))]
      [`(return-point ,label ,tail)
       `(return-point ,label ,(replace-locations-tail tail assignments))]))

  ;; (Source Tail) (Set aloc -> triv) -> (Target Tail)
  (define (replace-locations-tail e assignments)
    (match e
      [`(jump ,trg ,locs ...) `(jump ,(if (aloc? trg) (info-ref assignments trg) trg))]
      [`(begin ,effects ... ,tail)
       `(begin ,@(map (lambda (e) (replace-locations-effect e assignments)) effects)
               ,(replace-locations-tail tail assignments))]
      [`(if ,pred ,tail1 ,tail2)
       `(if ,(replace-locations-pred pred assignments)
            ,(replace-locations-tail tail1 assignments)
            ,(replace-locations-tail tail2 assignments))]))

  ;; (Source Definition) -> (Target Definition)
  (define (replace-locations-definition def)
    (match def
      [`(define ,label ,info ,tail)
       `(define ,label ,(replace-locations-tail tail (info-ref info 'assignment)))]))

  (match p
    [`(module ,info ,defs ... ,tail)
     `(module ,@(map replace-locations-definition defs)
        ,(replace-locations-tail tail (info-ref info 'assignment)))]))

(module+ tests
  (check-equal?
    (replace-locations '(module ((locals ()) (assignment ()) (new-frames (()))) (begin (set! rax 5) (jump r15))))
    '(module (begin (set! rax 5) (jump r15))))

  (check-equal? 
    (replace-locations 
      '(module ((locals ()) 
      (undead-out (((tmp-ra.488 rbp)) (((r15 rbp)) (r15 rbp))))
      (conflicts ((tmp-ra.488 (rbp)) (rbp (r15 tmp-ra.488)) (r15 (rbp))))
      (assignment ((tmp-ra.488 r15)))) 
      (define L.addup.1 
        ((locals ())
        (undead-out (((r12 rbp tmp-ra.489)) ((((r12 tmp.800 rbp tmp-ra.489) (tmp.800 rbp tmp-ra.489)) (rbp tmp-ra.489)) (((x.2 rbp tmp-ra.489)) ((x.2 x.3 rbp tmp-ra.489)) (((x.3 tmp.801 rbp tmp-ra.489) (tmp.801 rbp tmp-ra.489) (y.1 rbp tmp-ra.489)) (y.1 rbp tmp-ra.489))) (((tmp.802 rbp tmp-ra.489) (rax rbp tmp-ra.489)) (rax rbp)))))
        (conflicts ((y.1 (tmp-ra.489 rbp)) (x.3 (tmp.801 tmp-ra.489 rbp x.2)) (x.2 (x.3 tmp-ra.489 rbp)) (tmp.802 (tmp-ra.489 rbp)) (tmp.801 (tmp-ra.489 rbp x.3)) (tmp.800 (r12 tmp-ra.489 rbp)) (tmp-ra.489 (rax tmp.802 tmp.801 x.3 x.2 y.1 tmp.800 rbp r12)) (r12 (rbp tmp.800 tmp-ra.489)) (rbp (rax tmp.802 tmp.801 x.3 x.2 y.1 r12 tmp.800 tmp-ra.489)) (rax (tmp-ra.489 rbp))))
        (assignment ((tmp-ra.489 r15) (x.3 r14) (tmp.800 r14) (tmp.801 r13) (x.2 r13) (tmp.802 r14) (y.1 r14))))
        (begin (begin (set! tmp-ra.489 r15))
            (begin (begin (begin (set! tmp.800 r12) 
                                  (set! r12 (+ r12 16)))
                                  (set! y.1 tmp.800))
                            (begin (begin (set! x.2 8))
                            (begin (set! x.3 16))
                            (begin (begin (set! tmp.801 x.2) 
                                  (set! tmp.801 (+ tmp.801 x.3))
                                  (set! y.1 tmp.801)) (mset! y.1 8 y.1)))
                                  (begin (begin (set! tmp.802 (mref y.1 8)) (set! rax tmp.802)) (jump tmp-ra.489 rbp rax)))))
        (begin (begin (set! tmp-ra.488 r15)) (begin (begin (set! r15 tmp-ra.488)) (jump L.addup.1 rbp r15)))))

    '(module
      (define L.addup.1
      (begin
        (begin (set! r15 r15))
        (begin
          (begin (begin (set! r14 r12) (set! r12 (+ r12 16))) (set! r14 r14))
          (begin
            (begin (set! r13 8))
            (begin (set! r14 16))
            (begin
              (begin (set! r13 r13) (set! r13 (+ r13 r14)) (set! r14 r13))
              (mset! r14 8 r14)))
          (begin (begin (set! r14 (mref r14 8)) (set! rax r14)) (jump r15)))))
    (begin
      (begin (set! r15 r15))
      (begin (begin (set! r15 r15)) (jump L.addup.1)))))
)