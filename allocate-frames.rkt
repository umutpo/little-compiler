#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide allocate-frames)

(define (my-flatten lst)
  (foldr append '() lst))

;; Compiles Asm-pred-lang-v6/pre-framed to Asm-pred-lang-v6/framed
;; by allocating frames for each non-tail call,
;; and assigning all new-frame variables to frame variables in the new frame.
;;
;; Asm-pred-lang-v6/pre-framed -> Asm-pred-lang-v6/framed
(define (allocate-frames p)

  ;; (listof loc) (listof (aloc fvar))
  (define (get-number-of-slots call-undead assignment)
    (if (empty? call-undead)
        1
        (+ 1
           (argmax identity (for/list ([x call-undead])
                              (fvar->index (info-ref assignment x)))))))

  ;; (listof (aloc fvar)) -> number
  (define (pick-max-fvar-index assignment)
    (argmax identity (for/list ([x (my-flatten (dict-values assignment))])
                       (fvar->index x))))

  ;; (listof (aloc fvar)) (listof loc) -> (listof (aloc fvar))
  (define (update-assignment assignment locs)
    (for ([loc locs])
      (when (aloc? loc)
        (set! assignment (info-set assignment loc (make-fvar (+ (pick-max-fvar-index assignment) 1))))))
    assignment)

  ;; (listof aloc) (listof (aloc fvar)) -> (listof aloc)
  (define (update-locals locals assignment)
    (remove* (dict-keys assignment) locals))

  ;; Asm-pred-lang-v6/pre-framed.Def -> Asm-pred-lang-v6/framed.Def
  (define (allocate-frames-def e)
    (match e
      [`(define ,label ,info ,tail)
       (let*-values ([(assignment) (info-ref info `assignment)]
                     [(call-undead) (info-ref info `call-undead)]
                     [(new-tail new-assignment) (allocate-frames-tail tail assignment call-undead)]
                     [(new-locals) (update-locals (reverse (info-ref info `locals)) new-assignment)]
                     [(new-info) (info-set (info-set (info-remove (info-remove (info-remove info `undead-out) `new-frames) `call-undead) `assignment new-assignment) `locals new-locals)])
         `(define ,label ,new-info ,new-tail))]))

  ;; (listof Asm-pred-lang-v6/pre-framed.Effect) (listof (aloc fvar)) (listof loc) -> (listof Asm-pred-lang-v6/framed.Effect) (listof (aloc fvar))
  (define (allocate-frames-effects effects assignment call-undead)
    (values (for/list ([effect effects])
              (let-values ([(new-effect new-assignment) (allocate-frames-effect effect assignment call-undead)])
                (set! assignment new-assignment)
                new-effect))
            assignment))

  ;; Asm-pred-lang-v6/pre-framed.Pred (listof (aloc fvar)) (listof loc) -> Asm-pred-lang-v6/framed.Pred (listof (aloc fvar))
  (define (allocate-frames-pred e assignment call-undead)
    (match e
      [`(true) (values `(true) assignment)]
      [`(false) (values `(false) assignment)]
      [`(not ,pred)
       (let-values ([(new-pred new-assignments) (allocate-frames-pred pred assignment call-undead)])
         (values `(not ,new-pred) new-assignments))]
      [`(begin ,effects ... ,pred)
       (let*-values ([(new-effects new-assignment) (allocate-frames-effects effects assignment call-undead)]
                     [(new-pred new-assignment-pred) (allocate-frames-pred pred new-assignment call-undead)])
         (values `(begin ,@new-effects ,new-pred) new-assignment-pred))]
      [`(if ,pred ,pred1 ,pred2)
       (let*-values ([(new-pred new-assignment) (allocate-frames-pred pred assignment call-undead)]
                     [(new-pred1 new-assignment1) (allocate-frames-pred pred1 new-assignment call-undead)]
                     [(new-pred2 new-assignment2) (allocate-frames-pred pred2 new-assignment1 call-undead)])
         (values `(if ,new-pred ,new-pred1 ,new-pred2) new-assignment2))]
      [`(,relop ,loc ,opand) (values `(,relop ,loc ,opand) assignment)]))

  ;; Asm-pred-lang-v6/pre-framed.Tail (listof (aloc fvar)) (listof loc) -> Asm-pred-lang-v6/framed.Tail (listof (aloc fvar))
  (define (allocate-frames-tail e assignment call-undead)
    (match e
      [`(jump ,trg ,locs ...)
       (values `(jump ,trg ,@locs) (update-assignment assignment locs))]
      [`(begin ,effects ... ,tail)
       (let*-values ([(new-effects new-assignment) (allocate-frames-effects effects assignment call-undead)]
                     [(new-tail new-assignment-tail) (allocate-frames-tail tail new-assignment call-undead)])
         (values `(begin ,@new-effects ,new-tail) new-assignment-tail))]
      [`(if ,pred ,tail1 ,tail2)
       (let*-values ([(new-pred new-assignment) (allocate-frames-pred pred assignment call-undead)]
                     [(new-tail1 new-assignment1) (allocate-frames-tail tail1 new-assignment call-undead)]
                     [(new-tail2 new-assignment2) (allocate-frames-tail tail2 new-assignment1 call-undead)])
         (values `(if ,new-pred ,new-tail1 ,new-tail2) new-assignment2))]))

  ;; Asm-pred-lang-v6/pre-framed.Effect (listof (aloc fvar)) (listof loc) -> Asm-pred-lang-v6/framed.Effect (listof (aloc fvar))
  (define (allocate-frames-effect e assignment call-undead)
    (match e
      [`(set! ,loc1 (mref ,loc2 ,index)) (values `(set! ,loc1 (mref ,loc2 ,index)) assignment)]
      [`(set! ,loc (,binop ,loc ,opand)) (values `(set! ,loc (,binop ,loc ,opand)) assignment)]
      [`(set! ,loc ,triv) (values `(set! ,loc ,triv) assignment)]
      [`(mset! ,loc ,index ,triv) (values `(mset! ,loc ,index ,triv) assignment)]
      [`(begin ,effects ...)
       (let*-values ([(new-effects new-assignment) (allocate-frames-effects effects assignment call-undead)])
         (values `(begin ,@new-effects) new-assignment))]
      [`(if ,pred ,effect1 ,effect2)
       (let*-values ([(new-pred new-assignment) (allocate-frames-pred pred assignment call-undead)]
                     [(new-effect1 new-assignment1) (allocate-frames-effect effect1 new-assignment call-undead)]
                     [(new-effect2 new-assignment2) (allocate-frames-effect effect2 new-assignment1 call-undead)])
         (values `(if ,new-pred ,new-effect1 ,new-effect2) new-assignment2))]
      [`(return-point ,label ,tail)
       (allocate-frames-return-point label tail assignment call-undead)]))

  ;; label Asm-pred-lang-v6/pre-framed.Tail (listof (aloc fvar)) (listof loc) -> Asm-pred-lang-v6/framed.Tail (listof (aloc fvar))
  (define (allocate-frames-return-point label tail assignment call-undead)
    (let*-values ([(fbp) (current-frame-base-pointer-register)]
                  [(n) (get-number-of-slots call-undead assignment)]
                  [(nb) (* n (current-word-size-bytes))]
                  [(new-tail new-assignment) (allocate-frames-tail tail assignment call-undead)])
      (values `(begin (set! ,fbp (- ,fbp ,nb))
                      (return-point ,label ,new-tail)
                      (set! ,fbp (+ ,fbp ,nb)))
              new-assignment)))

  (match p
    [`(module ,info ,defs ... ,tail)
     (let*-values ([(assignment) (info-ref info `assignment)]
                   [(call-undead) (info-ref info `call-undead)]
                   [(new-tail new-assignment) (allocate-frames-tail tail assignment call-undead)]
                   [(new-locals) (update-locals (reverse (info-ref info `locals)) new-assignment)]
                   [(new-info) (info-set (info-remove (info-remove (info-remove info `undead-out) `new-frames) `call-undead) `assignment new-assignment)])
       `(module ,new-info ,@(map allocate-frames-def defs) ,new-tail))]))
