#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide assign-frame-variables)

;; Performs graph-colouring register allocation.
;; Allocates all abstract locations in the locals set to free frame variables.
;;
;; asm-pred-lang-v6/spilled -> asm-pred-lang-v5/assignment
(define (assign-frame-variables p)

  ;; (setof loc) Graph (dict loc -> (listof loc)) -> (values (listof loc)) AND (listof loc))
  (define (assign-helper locals-set conflict-graph assignments)

    (define spills '()) ;; mutable

    ;; hopefully only this function needs to change for other assignment passes
    ;; loc (listof loc) (dict loc -> (listof loc)) -> Boolean (dict loc -> (listof loc))
    ;; returns whether assignment was successful or not AND updated assignment
    (define (assigner loc conflict assignments)
      (define conflict-set (list->set conflict))

      (define (assign-loc-to-fvar index)
        (let ([new-fvar (make-fvar index)])
          (if (or (set-member? conflict-set new-fvar)
                  (member new-fvar (map (lambda (conflict-loc) (car (dict-ref assignments conflict-loc (list #f)))) conflict)))
              (assign-loc-to-fvar (add1 index))
              (dict-set assignments loc (list (make-fvar index))))))

      (values #t (assign-loc-to-fvar 0)))

    ;; loc (listof loc) (dict loc -> (listof loc)) -> (dict loc -> (listof loc))
    (define (assign-registers--one curr-local conflict assignments)
      (if (set-member? locals-set curr-local)
          (let-values ([(success? assignments) (assigner curr-local conflict assignments)])
            (unless success? (set! spills (append spills `(,curr-local))))
            assignments)
          assignments))

    ;; Graph (dict loc -> (listof loc)) -> (dict loc -> (listof loc))
    (define (assign-registers--all conflict-graph assignments)
      (if (empty? conflict-graph)
          assignments
          (let* ([curr-local (car (first conflict-graph))]
                 [next-conflicts (rest conflict-graph)]
                 [new-assignments (assign-registers--all next-conflicts assignments)])
            (assign-registers--one curr-local (get-neighbors conflict-graph curr-local) new-assignments))))

    (values (assign-registers--all (sort-graph conflict-graph) assignments) spills))

  ;; Graph -> (list aloc (listof aloc))
  (define (sort-graph graph)
    (sort (dict->list graph) #:key (λ (x) (length (second x))) <))

  ;; Info -> Info
  (define (assign-frame-variables-info info)
    (let ([locals (info-ref info 'locals)]
          [conflicts (info-ref info 'conflicts)]
          [assignments (info-ref info 'assignment)])
      (if (empty? locals)
          info
          (let-values ([(assignments locals) (assign-helper (list->set locals) conflicts assignments)])
            (info-set '() 'assignment assignments)))))

  ;; Definition -> Definition
  (define (assign-frame-variables-definition def)
    (match def
      [`(define ,label ,info ,tail)
       `(define ,label ,(assign-frame-variables-info info) ,tail)]))

  (match p
    [`(module ,info ,defs ... ,tail)
     `(module ,(assign-frame-variables-info info)
        ,@(map assign-frame-variables-definition defs)
        ,tail)]))

(module+ tests
  (check-equal?
    (assign-frame-variables '(module
                                ((locals (tmp-ra.4))
                                  (undead-out
                                  ((tmp-ra.4 rbp)
                                    (tmp-ra.4 fv1 rbp)
                                    (tmp-ra.4 fv1 fv0 rbp)
                                    (fv1 fv0 r15 rbp)
                                    (fv1 fv0 r15 rbp)))
                                  (conflicts
                                  ((tmp-ra.4 (fv0 fv1 rbp))
                                    (rbp (r15 fv0 fv1 tmp-ra.4))
                                    (fv1 (r15 fv0 rbp tmp-ra.4))
                                    (fv0 (r15 rbp fv1 tmp-ra.4))
                                    (r15 (rbp fv0 fv1))))
                                  (assignment ()))
                              (define L.swap.1
                                ((locals (z.3 x.1 y.2))
                                  (undead-out
                                  ((fv0 fv1 tmp-ra.1 rbp)
                                    (fv1 x.1 tmp-ra.1 rbp)
                                    (y.2 x.1 tmp-ra.1 rbp)
                                    ((y.2 x.1 tmp-ra.1 rbp)
                                    ((tmp-ra.1 rax rbp) (rax rbp))
                                    (((rax tmp-ra.1 rbp)
                                      ((y.2 nfv.3 rbp)
                                        (nfv.3 nfv.2 rbp)
                                        (nfv.3 nfv.2 r15 rbp)
                                        (nfv.3 nfv.2 r15 rbp)))
                                      (z.3 tmp-ra.1 rbp)
                                      (tmp-ra.1 rax rbp)
                                      (rax rbp)))))
                                  (conflicts
                                  ((y.2 (rbp tmp-ra.1 x.1 nfv.3))
                                    (x.1 (y.2 rbp tmp-ra.1 fv1))
                                    (tmp-ra.1 (y.2 x.1 rbp fv1 fv0 rax z.3))
                                    (z.3 (rbp tmp-ra.1))
                                    (nfv.3 (r15 nfv.2 rbp y.2))
                                    (nfv.2 (r15 rbp nfv.3))
                                    (rbp (y.2 x.1 tmp-ra.1 rax z.3 r15 nfv.2 nfv.3))
                                    (r15 (rbp nfv.2 nfv.3))
                                    (rax (rbp tmp-ra.1))
                                    (fv0 (tmp-ra.1))
                                    (fv1 (x.1 tmp-ra.1))))
                                  (assignment ((tmp-ra.1 fv2) (nfv.2 fv3) (nfv.3 fv4))))
                                (begin
                                  (set! tmp-ra.1 r15)
                                  (set! x.1 fv0)
                                  (set! y.2 fv1)
                                  (if (< y.2 x.1)
                                      (begin (set! rax x.1) (jump tmp-ra.1 rbp rax))
                                      (begin
                                        (begin
                                          (set! rbp (- rbp 24))
                                          (return-point L.rp.1
                                                        (begin
                                                          (set! nfv.3 x.1)
                                                          (set! nfv.2 y.2)
                                                          (set! r15 L.rp.1)
                                                          (jump L.swap.1 rbp r15 nfv.2 nfv.3)))
                                          (set! rbp (+ rbp 24)))
                                        (set! z.3 rax)
                                        (set! rax z.3)
                                        (jump tmp-ra.1 rbp rax)))))
                              (begin
                                (set! tmp-ra.4 r15)
                                (set! fv1 2)
                                (set! fv0 1)
                                (set! r15 tmp-ra.4)
                                (jump L.swap.1 rbp r15 fv0 fv1))))

    '(module
        ((assignment ((tmp-ra.4 fv2))))
      (define L.swap.1
        ((assignment
          ((tmp-ra.1 fv2) (nfv.2 fv3) (nfv.3 fv4) (x.1 fv0) (y.2 fv1) (z.3 fv0))))
        (begin
          (set! tmp-ra.1 r15)
          (set! x.1 fv0)
          (set! y.2 fv1)
          (if (< y.2 x.1)
              (begin (set! rax x.1) (jump tmp-ra.1 rbp rax))
              (begin
                (begin
                  (set! rbp (- rbp 24))
                  (return-point L.rp.1
                                (begin
                                  (set! nfv.3 x.1)
                                  (set! nfv.2 y.2)
                                  (set! r15 L.rp.1)
                                  (jump L.swap.1 rbp r15 nfv.2 nfv.3)))
                  (set! rbp (+ rbp 24)))
                (set! z.3 rax)
                (set! rax z.3)
                (jump tmp-ra.1 rbp rax)))))
      (begin
        (set! tmp-ra.4 r15)
        (set! fv1 2)
        (set! fv0 1)
        (set! r15 tmp-ra.4)
        (jump L.swap.1 rbp r15 fv0 fv1))))
)  