#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide patch-instructions)

(define auxiliary-registers (current-patch-instructions-registers))

(define (my-flatten lst)
  (foldr append '() lst))

;; Patches instructions that have no x64 analogue
;; into to a sequence of instructions and
;; an auxiliary register from current-patch-instructions-registers
;;
;; Para-asm-lang-v8 -> Paren-x64-mops-v8
(define (patch-instructions p)

  ;; Any -> Boolean
  (define (addr? e)
    (match e
      [`(,fbp - ,dispoffset) (and (frame-base-pointer-register? fbp) (dispoffset? dispoffset))]
      [_ #f]))

  ;; Any -> Boolean
  (define (opand? e)
    (or (int64? e) (register? e) (addr? e)))

  ;; Any -> Boolean
  (define (triv? e)
    (or (opand? e) (label? e)))

  ;; Relop -> Relop
  (define (negate-relop relop)
    (match relop
      ['< '>=]
      ['<= '>]
      ['= '!=]
      ['>= '<]
      ['> '<=]
      ['!= '=]))

  ;; Para-asm-lang-v8.Trg -> (listof Paren-x64-mops-v8.Statement)
  (define (patch-instructions-jump trg)
    (cond
      [(label? trg) `((jump ,trg))]
      [(register? trg) `((jump ,trg))]
      [(addr? trg) `((set! ,(first auxiliary-registers) ,trg)
                     (jump ,(first auxiliary-registers)))]))

  ;; Para-asm-lang-v8.Relop Para-asm-lang-v8.Trg -> (listof Paren-x64-mops-v8.Statement)
  (define (patch-instructions-jump-if relop trg)
    (cond
      [(label? trg) `((jump-if ,relop ,trg))]
      [(register? trg)
       (let* ([negated-relop (negate-relop relop)]
              [fresh-label (fresh-label)])
         `((jump-if ,negated-relop ,fresh-label)
           (jump ,trg)
           (with-label ,fresh-label
             (set! ,(first auxiliary-registers) ,(first auxiliary-registers)))))]
      [(addr? trg)
       (let* ([negated-relop (negate-relop relop)]
              [fresh-label (fresh-label)])
         `((set! ,(first auxiliary-registers) ,trg)
           (jump-if ,negated-relop ,fresh-label)
           (jump ,(first auxiliary-registers))
           (with-label ,fresh-label
             (set! ,(first auxiliary-registers) ,(first auxiliary-registers)))))]))

  ;; Para-asm-lang-v8.Loc Para-asm-lang-v8.Opand -> (listof Paren-x64-mops-v8.Statement)
  (define (patch-instructions-compare loc opand)
    (cond
      [(and (register? loc) (int64? opand))
       `((compare ,loc ,opand))]
      [(and (register? loc) (register? opand))
       `((compare ,loc ,opand))]
      [(and (register? loc) (addr? opand))
       `((set! ,(first auxiliary-registers) ,opand)
         (compare ,loc ,(first auxiliary-registers)))]
      [(and (addr? loc) (int64? opand))
       `((set! ,(first auxiliary-registers) ,loc)
         (compare ,(first auxiliary-registers) ,opand))]
      [(and (addr? loc) (register? opand))
       `((set! ,(first auxiliary-registers) ,loc)
         (compare ,(first auxiliary-registers) ,opand))]
      [(and (addr? loc) (addr? opand))
       `((set! ,(second auxiliary-registers) ,opand)
         (set! ,(first auxiliary-registers) ,loc)
         (compare ,(first auxiliary-registers) ,(second auxiliary-registers)))]))

  ;; Para-asm-lang-v8.Loc Para-asm-lang-v8.Triv -> (listof Paren-x64-mops-v8.Statement)
  (define (patch-instructions-set-reg loc triv)
    (cond
      [(and (register? loc) (int64? triv))
       `((set! ,loc ,triv))]
      [(and (register? loc) (register? triv))
       `((set! ,loc ,triv))]
      [(and (register? loc) (addr? triv))
       `((set! ,loc ,triv))]
      [(and (register? loc) (label? triv))
       `((set! ,loc ,triv))]
      [(and (addr? loc) (int32? triv))
       `((set! ,loc ,triv))]
      [(and (addr? loc) (int64? triv))
       `((set! ,(first auxiliary-registers) ,triv)
         (set! ,loc ,(first auxiliary-registers)))]
      [(and (addr? loc) (register? triv))
       `((set! ,loc ,triv))]
      [(and (addr? loc) (addr? triv))
       `((set! ,(first auxiliary-registers) ,triv)
         (set! ,loc ,(first auxiliary-registers)))]
      [(and (addr? loc) (label? triv))
       `((set! ,loc ,triv))]))

  ;; Para-asm-lang-v8.Loc Para-asm-lang-v8.Opand Para-asm-lang-v8.Binop -> (listof Paren-x64-mops-v8.Statement)
  (define (patch-instructions-binop loc opand binop)
    (cond
      [(and (register? loc) (int32? opand))
       `((set! ,loc (,binop ,loc ,opand)))]
      [(and (register? loc) (int64? opand))
       `((set! ,(first auxiliary-registers) ,opand)
         (set! ,loc (,binop ,loc ,(first auxiliary-registers))))]
      [(and (addr? loc) (int32? opand))
       `((set! ,(first auxiliary-registers) ,loc)
         (set! ,(first auxiliary-registers) (,binop ,(first auxiliary-registers) ,opand))
         (set! ,loc ,(first auxiliary-registers)))]
      [(and (addr? loc) (int64? opand))
       `((set! ,(first auxiliary-registers) ,loc)
         (set! ,(second auxiliary-registers) ,opand)
         (set! ,(first auxiliary-registers) (,binop ,(first auxiliary-registers) ,(second auxiliary-registers)))
         (set! ,loc ,(first auxiliary-registers)))]
      [(and (register? loc) (register? opand))
       `((set! ,loc (,binop ,loc ,opand)))]
      [(and (register? loc) (addr? opand))
       `((set! ,loc (,binop ,loc ,opand)))]
      [(and (addr? loc) (register? opand))
       `((set! ,(first auxiliary-registers) ,loc)
         (set! ,(first auxiliary-registers) (,binop ,(first auxiliary-registers) ,opand))
         (set! ,loc ,(first auxiliary-registers)))]
      [(and (addr? loc) (addr? opand))
       `((set! ,(first auxiliary-registers) ,loc)
         (set! ,(first auxiliary-registers) (,binop ,(first auxiliary-registers) ,opand))
         (set! ,loc ,(first auxiliary-registers)))]))

  ;; Para-asm-lang-v8.Loc Para-asm-lang-v8.Loc Para-asm-lang-v8.Index -> (listof Paren-x64-mops-v8.Statement)
  (define (patch-instructions-mref loc1 loc2 index)
    (cond
      [(and (register? loc1) (register? loc2) (int32? index))
       `((set! ,loc1 (mref ,loc2 ,index)))]
      [(and (register? loc1) (register? loc2) (int64? index))
       `((set! ,(first auxiliary-registers) ,index)
         (set! ,loc1 (mref ,loc2 ,(first auxiliary-registers))))]
      [(and (register? loc1) (register? loc2) (register? index))
       `((set! ,loc1 (mref ,loc2 ,index)))]
      [(and (register? loc1) (register? loc2) (addr? index))
       `((set! ,(first auxiliary-registers) ,index)
         (set! ,loc1 (mref ,loc2 ,(first auxiliary-registers))))]
      [(and (register? loc1) (addr? loc2) (int32? index))
       `((set! ,(first auxiliary-registers) ,loc2)
         (set! ,loc1 (mref ,(first auxiliary-registers) ,index)))]
      [(and (register? loc1) (addr? loc2) (int64? index))
       `((set! ,(first auxiliary-registers) ,loc2)
         (set! ,(second auxiliary-registers) ,index)
         (set! ,loc1 (mref ,(first auxiliary-registers) ,(second auxiliary-registers))))]
      [(and (register? loc1) (addr? loc2) (register? index))
       `((set! ,(first auxiliary-registers) ,loc2)
         (set! ,loc1 (mref ,(first auxiliary-registers) ,index)))]
      [(and (register? loc1) (addr? loc2) (addr? index))
       `((set! ,(first auxiliary-registers) ,loc2)
         (set! ,(second auxiliary-registers) ,index)
         (set! ,loc1 (mref ,(first auxiliary-registers) ,(second auxiliary-registers))))]
      [(and (addr? loc1) (register? loc2) (int32? index))
       `((set! ,(first auxiliary-registers) (mref ,loc2 ,index))
         (set! ,loc1 ,(first auxiliary-registers)))]
      [(and (addr? loc1) (register? loc2) (int64? index))
       `((set! ,(first auxiliary-registers) ,index)
         (set! ,(first auxiliary-registers) (mref ,loc2 ,(first auxiliary-registers)))
         (set! ,loc1 ,(first auxiliary-registers)))]
      [(and (addr? loc1) (register? loc2) (register? index))
       `((set! ,(first auxiliary-registers) (mref ,loc2 ,index))
         (set! ,loc1 ,(first auxiliary-registers)))]
      [(and (addr? loc1) (register? loc2) (addr? index))
       `((set! ,(first auxiliary-registers) ,index)
         (set! ,(first auxiliary-registers) (mref ,loc2 ,(first auxiliary-registers)))
         (set! ,loc1 ,(first auxiliary-registers)))]
      [(and (addr? loc1) (addr? loc2) (int32? index))
       `((set! ,(first auxiliary-registers) ,loc2)
         (set! ,(first auxiliary-registers) (mref ,(first auxiliary-registers) ,index))
         (set! ,loc1 ,(first auxiliary-registers)))]
      [(and (addr? loc1) (addr? loc2) (int64? index))
       `((set! ,(first auxiliary-registers) ,loc2)
         (set! ,(second auxiliary-registers) ,index)
         (set! ,(first auxiliary-registers) (mref ,(first auxiliary-registers) ,(second auxiliary-registers)))
         (set! ,loc1 ,(first auxiliary-registers)))]
      [(and (addr? loc1) (addr? loc2) (register? index))
       `((set! ,(first auxiliary-registers) ,loc2)
         (set! ,(first auxiliary-registers) (mref ,(first auxiliary-registers) ,index))
         (set! ,loc1 ,(first auxiliary-registers)))]
      [(and (addr? loc1) (addr? loc2) (addr? index))
       `((set! ,(first auxiliary-registers) ,loc2)
         (set! ,(second auxiliary-registers) ,index)
         (set! ,(first auxiliary-registers) (mref ,(first auxiliary-registers) ,(second auxiliary-registers)))
         (set! ,loc1 ,(first auxiliary-registers)))]))

  ;; Para-asm-lang-v8.Loc Para-asm-lang-v8.Index Para-asm-lang-v8.Triv -> (listof Paren-x64-mops-v8.Statement)
  (define (patch-instructions-mset loc index triv)
    (cond
      [(and (register? loc) (int32? index) (int32? triv))
       `((mset! ,loc ,index ,triv))]
      [(and (register? loc) (int32? index) (int64? triv))
       `((set! ,(first auxiliary-registers) ,triv)
         (mset! ,loc ,index ,(first auxiliary-registers)))]
      [(and (register? loc) (int32? index) (register? triv))
       `((mset! ,loc ,index ,triv))]
      [(and (register? loc) (int32? index) (addr? triv))
       `((set! ,(first auxiliary-registers) ,triv)
         (mset! ,loc ,index ,(first auxiliary-registers)))]
      [(and (register? loc) (int32? index) (label? triv))
       `((set! ,(first auxiliary-registers) ,triv)
         (mset! ,loc ,index ,(first auxiliary-registers)))]
      [(and (register? loc) (int64? index) (int32? triv))
       `((set! ,(first auxiliary-registers) ,index)
         (mset! ,loc ,(first auxiliary-registers) ,triv))]
      [(and (register? loc) (int64? index) (int64? triv))
       `((set! ,(first auxiliary-registers) ,triv)
         (set! ,(second auxiliary-registers) ,index)
         (mset! ,loc ,(second auxiliary-registers) ,(first auxiliary-registers)))]
      [(and (register? loc) (int64? index) (register? triv))
       `((set! ,(second auxiliary-registers) ,index)
         (mset! ,loc ,(second auxiliary-registers) ,triv))]
      [(and (register? loc) (int64? index) (addr? triv))
       `((set! ,(first auxiliary-registers) ,triv)
         (set! ,(second auxiliary-registers) ,index)
         (mset! ,loc ,(second auxiliary-registers) ,(first auxiliary-registers)))]
      [(and (register? loc) (int64? index) (label? triv))
       `((set! ,(first auxiliary-registers) ,triv)
         (set! ,(second auxiliary-registers) ,index)
         (mset! ,loc ,(second auxiliary-registers) ,(first auxiliary-registers)))]
      [(and (register? loc) (register? index) (int32? triv))
       `((mset! ,loc ,index ,triv))]
      [(and (register? loc) (register? index) (int64? triv))
       `((set! ,(first auxiliary-registers) ,triv)
         (mset! ,loc ,index ,(first auxiliary-registers)))]
      [(and (register? loc) (register? index) (register? triv))
       `((mset! ,loc ,index ,triv))]
      [(and (register? loc) (register? index) (addr? triv))
       `((set! ,(first auxiliary-registers) ,triv)
         (mset! ,loc ,index ,(first auxiliary-registers)))]
      [(and (register? loc) (register? index) (label? triv))
       `((set! ,(first auxiliary-registers) ,triv)
         (mset! ,loc ,index ,(first auxiliary-registers)))]
      [(and (register? loc) (addr? index) (int32? triv))
       `((set! ,(first auxiliary-registers) ,index)
         (mset! ,loc ,(first auxiliary-registers) ,triv))]
      [(and (register? loc) (addr? index) (int64? triv))
       `((set! ,(first auxiliary-registers) ,triv)
         (set! ,(second auxiliary-registers) ,index)
         (mset! ,loc ,(second auxiliary-registers) ,(first auxiliary-registers)))]
      [(and (register? loc) (addr? index) (register? triv))
       `((set! ,(first auxiliary-registers) ,index)
         (mset! ,loc ,(first auxiliary-registers) ,triv))]
      [(and (register? loc) (addr? index) (addr? triv))
       `((set! ,(first auxiliary-registers) ,triv)
         (set! ,(second auxiliary-registers) ,index)
         (mset! ,loc ,(second auxiliary-registers) ,(first auxiliary-registers)))]
      [(and (register? loc) (addr? index) (label? triv))
       `((set! ,(first auxiliary-registers) ,triv)
         (set! ,(second auxiliary-registers) ,index)
         (mset! ,loc ,(second auxiliary-registers) ,(first auxiliary-registers)))]
      [(and (addr? loc) (int32? index) (int32? triv))
       `((set! ,(first auxiliary-registers) ,loc)
         (mset! ,(first auxiliary-registers) ,index ,triv))]
      [(and (addr? loc) (int32? index) (int64? triv))
       `((set! ,(first auxiliary-registers) ,triv)
         (set! ,(second auxiliary-registers) ,loc)
         (mset! ,(second auxiliary-registers) ,index ,(first auxiliary-registers)))]
      [(and (addr? loc) (int32? index) (register? triv))
       `((set! ,(first auxiliary-registers) ,loc)
         (mset! ,(first auxiliary-registers) ,index ,triv))]
      [(and (addr? loc) (int32? index) (addr? triv))
       `((set! ,(first auxiliary-registers) ,triv)
         (set! ,(second auxiliary-registers) ,loc)
         (mset! ,(second auxiliary-registers) ,index ,(first auxiliary-registers)))]
      [(and (addr? loc) (int32? index) (label? triv))
       `((set! ,(first auxiliary-registers) ,triv)
         (set! ,(second auxiliary-registers) ,loc)
         (mset! ,(second auxiliary-registers) ,index ,(first auxiliary-registers)))]
      [(and (addr? loc) (int64? index) (int32? triv))
       `((set! ,(first auxiliary-registers) ,loc)
         (set! ,(second auxiliary-registers) ,index)
         (mset! ,(first auxiliary-registers) ,(second auxiliary-registers) ,triv))]
      [(and (addr? loc) (int64? index) (int64? triv))
       `((set! ,(first auxiliary-registers) ,loc)
         (set! ,(second auxiliary-registers) ,index)
         (set! ,(first auxiliary-registers) (+ ,(first auxiliary-registers) ,(second auxiliary-registers)))
         (set! ,(second auxiliary-registers) ,triv)
         (mset! ,(first auxiliary-registers) 0 ,(second auxiliary-registers)))]
      [(and (addr? loc) (int64? index) (register? triv))
       `((set! ,(first auxiliary-registers) ,loc)
         (set! ,(second auxiliary-registers) ,index)
         (mset! ,(first auxiliary-registers) ,(second auxiliary-registers) ,triv))]
      [(and (addr? loc) (int64? index) (addr? triv))
       `((set! ,(first auxiliary-registers) ,loc)
         (set! ,(second auxiliary-registers) ,index)
         (set! ,(first auxiliary-registers) (+ ,(first auxiliary-registers) ,(second auxiliary-registers)))
         (set! ,(second auxiliary-registers) ,triv)
         (mset! ,(first auxiliary-registers) 0 ,(second auxiliary-registers)))]
      [(and (addr? loc) (int64? index) (label? triv))
       `((set! ,(first auxiliary-registers) ,loc)
         (set! ,(second auxiliary-registers) ,index)
         (set! ,(first auxiliary-registers) (+ ,(first auxiliary-registers) ,(second auxiliary-registers)))
         (set! ,(second auxiliary-registers) ,triv)
         (mset! ,(first auxiliary-registers) 0 ,(second auxiliary-registers)))]
      [(and (addr? loc) (register? index) (int32? triv))
       `((set! ,(first auxiliary-registers) ,loc)
         (mset! ,(first auxiliary-registers) ,index ,triv))]
      [(and (addr? loc) (register? index) (int64? triv))
       `((set! ,(first auxiliary-registers) ,triv)
         (set! ,(second auxiliary-registers) ,loc)
         (mset! ,(second auxiliary-registers) ,index ,(first auxiliary-registers)))]
      [(and (addr? loc) (register? index) (register? triv))
       `((set! ,(first auxiliary-registers) ,loc)
         (mset! ,(first auxiliary-registers) ,index ,triv))]
      [(and (addr? loc) (register? index) (addr? triv))
       `((set! ,(first auxiliary-registers) ,triv)
         (set! ,(second auxiliary-registers) ,loc)
         (mset! ,(second auxiliary-registers) ,index ,(first auxiliary-registers)))]
      [(and (addr? loc) (register? index) (label? triv))
       `((set! ,(first auxiliary-registers) ,triv)
         (set! ,(second auxiliary-registers) ,loc)
         (mset! ,(second auxiliary-registers) ,index ,(first auxiliary-registers)))]
      [(and (addr? loc) (addr? index) (int32? triv))
       `((set! ,(first auxiliary-registers) ,loc)
         (set! ,(second auxiliary-registers) ,index)
         (mset! ,(first auxiliary-registers) ,(second auxiliary-registers) ,triv))]
      [(and (addr? loc) (addr? index) (int64? triv))
       `((set! ,(first auxiliary-registers) ,loc)
         (set! ,(second auxiliary-registers) ,index)
         (set! ,(first auxiliary-registers) (+ ,(first auxiliary-registers) ,(second auxiliary-registers)))
         (set! ,(second auxiliary-registers) ,triv)
         (mset! ,(first auxiliary-registers) 0 ,(second auxiliary-registers)))]
      [(and (addr? loc) (addr? index) (register? triv))
       `((set! ,(first auxiliary-registers) ,loc)
         (set! ,(second auxiliary-registers) ,index)
         (mset! ,(first auxiliary-registers) ,(second auxiliary-registers) ,triv))]
      [(and (addr? loc) (addr? index) (addr? triv))
       `((set! ,(first auxiliary-registers) ,loc)
         (set! ,(second auxiliary-registers) ,index)
         (set! ,(first auxiliary-registers) (+ ,(first auxiliary-registers) ,(second auxiliary-registers)))
         (set! ,(second auxiliary-registers) ,triv)
         (mset! ,(first auxiliary-registers) 0 ,(second auxiliary-registers)))]
      [(and (addr? loc) (addr? index) (label? triv))
       `((set! ,(first auxiliary-registers) ,loc)
         (set! ,(second auxiliary-registers) ,index)
         (set! ,(first auxiliary-registers) (+ ,(first auxiliary-registers) ,(second auxiliary-registers)))
         (set! ,(second auxiliary-registers) ,triv)
         (mset! ,(first auxiliary-registers) 0 ,(second auxiliary-registers)))]))

  ;; Para-asm-lang-v8.Effect -> (listof Paren-x64-mops-v8.Statement)
  (define (patch-instructions-s e)
    (match e
      [`(set! ,loc1 (mref ,loc2 ,index))
       (patch-instructions-mref loc1 loc2 index)]
      [`(set! ,loc (,binop ,loc ,opand))
       (patch-instructions-binop loc opand binop)]
      [`(set! ,loc ,triv)
       (patch-instructions-set-reg loc triv)]
      [`(mset! ,loc ,index ,triv)
       (patch-instructions-mset loc index triv)]
      [`(jump ,trg)
       (patch-instructions-jump trg)]
      [`(with-label ,label ,s)
       (let ([new-s (patch-instructions-s s)])
         (if (= (length new-s) 1)
             `((with-label ,label ,@new-s))
             `((with-label ,label ,(first new-s))
               ,@(rest new-s))))]
      [`(compare ,loc ,opand)
       (patch-instructions-compare loc opand)]
      [`(jump-if ,relop ,trg)
       (patch-instructions-jump-if relop trg)]))

  (match p
    [`(begin ,effects ...)
     `(begin ,@(my-flatten (map patch-instructions-s effects)))]))

(module+ tests
  (check-equal?
   (patch-instructions
    '(begin (set! rbx 42)))
   '(begin (set! rbx 42)))

  (check-equal?
   (patch-instructions
    '(begin
       (set! rbx 0)
       (set! rcx 0)
       (set! r9 42)
       (set! rbx rcx)
       (set! rbx (+ rbx r9))
       (set! rax rbx)))
   '(begin
      (set! rbx 0)
      (set! rcx 0)
      (set! r9 42)
      (set! rbx rcx)
      (set! rbx (+ rbx r9))
      (set! rax rbx)))

  (check-equal?
   (patch-instructions
    '(begin
       (set! (rbp - 0) 42)
       (set! rax 15)
       (set! rax (+ rax (rbp - 0)))
       (with-label L.A.0
         (set! rax (+ rax 1)))
       (compare rax 57)
       (jump-if = L.A.0)))
   '(begin
      (set! (rbp - 0) 42)
      (set! rax 15)
      (set! rax (+ rax (rbp - 0)))
      (with-label L.A.0 (set! rax (+ rax 1)))
      (compare rax 57)
      (jump-if = L.A.0)))

  (check-equal?
   (patch-instructions
    '(begin
       (set! (rbp - 0) 0)
       (set! (rbp - 8) 1)
       (compare (rbp - 0) (rbp - 8))
       (jump-if > L.foo.1)
       (set! rax 0)
       (with-label L.foo.1
         (set! rax 1))
       (with-label L.end.1
         (set! rax rax))))
   '(begin
      (set! (rbp - 0) 0)
      (set! (rbp - 8) 1)
      (set! r11 (rbp - 8))
      (set! r10 (rbp - 0))
      (compare r10 r11)
      (jump-if > L.foo.1)
      (set! rax 0)
      (with-label L.foo.1 (set! rax 1))
      (with-label L.end.1 (set! rax rax))))

  (check-equal?
   (patch-instructions
    '(begin
       (set! (rbp - 0) 42)
       (set! rax 15)
       (set! rax (bitwise-ior rax (rbp - 0)))
       (with-label L.A.0
         (set! rax (+ rax 1)))
       (compare rax 57)
       (jump-if = L.A.0)))
   '(begin
      (set! (rbp - 0) 42)
      (set! rax 15)
      (set! rax (bitwise-ior rax (rbp - 0)))
      (with-label L.A.0 (set! rax (+ rax 1)))
      (compare rax 57)
      (jump-if = L.A.0)))

  (check-equal?
   (patch-instructions
    '(begin
       (with-label L.__main.4 (set! r15 r15))
       (set! r14 r12)
       (set! r12 (+ r12 16))
       (set! r14 (+ r14 1))
       (mset! r14 -1 40)
       (mset! r14 7 48)
       (set! rax r14)
       (jump r15)))
   '(begin
      (with-label L.__main.4 (set! r15 r15))
      (set! r14 r12)
      (set! r12 (+ r12 16))
      (set! r14 (+ r14 1))
      (mset! r14 -1 40)
      (mset! r14 7 48)
      (set! rax r14)
      (jump r15)))

  (check-equal?
   (patch-instructions
    '(begin
       (with-label L.__main.4 (set! r15 r15))
       (set! r14 r12)
       (set! r12 (+ r12 16))
       (set! r14 (+ r14 1))
       (mset! r14 -1 40)
       (mset! r14 7 48)
       (set! r14 r14)
       (set! rax (mref r14 -1))
       (jump r15)))
   '(begin
      (with-label L.__main.4 (set! r15 r15))
      (set! r14 r12)
      (set! r12 (+ r12 16))
      (set! r14 (+ r14 1))
      (mset! r14 -1 40)
      (mset! r14 7 48)
      (set! r14 r14)
      (set! rax (mref r14 -1))
      (jump r15)))

  (check-equal?
   (patch-instructions
    '(begin
       (with-label L.__main.4 (set! r15 r15))
       (set! r14 r12)
       (set! r12 (+ r12 32))
       (set! r14 r14)
       (set! r14 (+ r14 3))
       (mset! r14 -3 24)
       (set! r14 r14)
       (set! rax (mref r14 53))
       (jump r15)))
   '(begin
      (with-label L.__main.4 (set! r15 r15))
      (set! r14 r12)
      (set! r12 (+ r12 32))
      (set! r14 r14)
      (set! r14 (+ r14 3))
      (mset! r14 -3 24)
      (set! r14 r14)
      (set! rax (mref r14 53))
      (jump r15)))

  (check-equal?
   (patch-instructions
    '(begin
       (with-label L.__main.4 (set! r15 r15))
       (set! r14 r12)
       (set! r12 (+ r12 16))
       (set! r14 (+ r14 1))
       (mset! r14 -1 40)
       (mset! r14 7 48)
       (set! r14 r14)
       (set! rax (mref r14 r12))
       (jump r15)))
   '(begin
      (with-label L.__main.4 (set! r15 r15))
      (set! r14 r12)
      (set! r12 (+ r12 16))
      (set! r14 (+ r14 1))
      (mset! r14 -1 40)
      (mset! r14 7 48)
      (set! r14 r14)
      (set! rax (mref r14 r12))
      (jump r15)))

  (check-equal?
   (patch-instructions
    '(begin
       (with-label L.__main.4 (set! r15 r15))
       (set! r14 r12)
       (set! r12 (+ r12 32))
       (set! r14 r14)
       (set! r14 (+ r14 3))
       (mset! r14 -3 24)
       (set! r14 r14)
       (set! rax (mref r14 2147483648))
       (jump r15)))
   '(begin
      (with-label L.__main.4 (set! r15 r15))
      (set! r14 r12)
      (set! r12 (+ r12 32))
      (set! r14 r14)
      (set! r14 (+ r14 3))
      (mset! r14 -3 24)
      (set! r14 r14)
      (set! r10 2147483648)
      (set! rax (mref r14 r10))
      (jump r15)))

  (check-equal?
   (patch-instructions
    '(begin
       (with-label L.__main.4 (set! r15 r15))
       (set! r14 r12)
       (set! r12 (+ r12 16))
       (set! r14 (+ r14 1))
       (mset! r14 -1 40)
       (mset! r14 7 48)
       (set! r14 r14)
       (set! rax (mref r14 (rbp - 8)))
       (jump r15)))
   '(begin
      (with-label L.__main.4 (set! r15 r15))
      (set! r14 r12)
      (set! r12 (+ r12 16))
      (set! r14 (+ r14 1))
      (mset! r14 -1 40)
      (mset! r14 7 48)
      (set! r14 r14)
      (set! r10 (rbp - 8))
      (set! rax (mref r14 r10))
      (jump r15)))

  (check-equal?
   (patch-instructions
    '(begin
       (with-label L.__main.4 (set! r15 r15))
       (set! r14 r12)
       (set! r12 (+ r12 16))
       (set! r14 (+ r14 1))
       (mset! r14 -1 40)
       (mset! r14 7 48)
       (set! r14 r14)
       (set! rax (mref (rbp - 8) -1))
       (jump r15)))
   '(begin
      (with-label L.__main.4 (set! r15 r15))
      (set! r14 r12)
      (set! r12 (+ r12 16))
      (set! r14 (+ r14 1))
      (mset! r14 -1 40)
      (mset! r14 7 48)
      (set! r14 r14)
      (set! r10 (rbp - 8))
      (set! rax (mref r10 -1))
      (jump r15)))

  (check-equal?
   (patch-instructions
    '(begin
       (with-label L.__main.4 (set! r15 r15))
       (set! r14 r12)
       (set! r12 (+ r12 16))
       (set! r14 (+ r14 1))
       (mset! r14 -1 40)
       (mset! r14 7 48)
       (set! r14 r14)
       (set! rax (mref (rbp - 8) (rbp - 0)))
       (jump r15)))
   '(begin
      (with-label L.__main.4 (set! r15 r15))
      (set! r14 r12)
      (set! r12 (+ r12 16))
      (set! r14 (+ r14 1))
      (mset! r14 -1 40)
      (mset! r14 7 48)
      (set! r14 r14)
      (set! r10 (rbp - 8))
      (set! r11 (rbp - 0))
      (set! rax (mref r10 r11))
      (jump r15)))

  (check-equal?
   (patch-instructions
    '(begin
       (with-label L.__main.4 (set! r15 r15))
       (set! r14 r12)
       (set! r12 (+ r12 16))
       (set! r14 (+ r14 1))
       (mset! r14 -1 40)
       (mset! r14 7 48)
       (set! r14 r14)
       (set! (rbp - 16) (mref (rbp - 8) (rbp - 0)))
       (jump r15)))
   '(begin
      (with-label L.__main.4 (set! r15 r15))
      (set! r14 r12)
      (set! r12 (+ r12 16))
      (set! r14 (+ r14 1))
      (mset! r14 -1 40)
      (mset! r14 7 48)
      (set! r14 r14)
      (set! r10 (rbp - 8))
      (set! r11 (rbp - 0))
      (set! r10 (mref r10 r11))
      (set! (rbp - 16) r10)
      (jump r15)))

  (check-equal?
   (patch-instructions
    '(begin
       (with-label L.__main.4 (set! r15 r15))
       (set! r14 r12)
       (set! r12 (+ r12 16))
       (set! r14 (+ r14 1))
       (mset! r14 -1 2147483648)
       (mset! r14 7 48)
       (set! r14 r14)
       (set! (rbp - 16) (mref (rbp - 8) (rbp - 0)))
       (jump r15)))
   '(begin
      (with-label L.__main.4 (set! r15 r15))
      (set! r14 r12)
      (set! r12 (+ r12 16))
      (set! r14 (+ r14 1))
      (set! r10 2147483648)
      (mset! r14 -1 r10)
      (mset! r14 7 48)
      (set! r14 r14)
      (set! r10 (rbp - 8))
      (set! r11 (rbp - 0))
      (set! r10 (mref r10 r11))
      (set! (rbp - 16) r10)
      (jump r15)))

  (check-equal?
   (patch-instructions
    '(begin
       (with-label L.__main.4 (set! r15 r15))
       (set! r14 r12)
       (set! r12 (+ r12 16))
       (set! r14 (+ r14 1))
       (mset! (rbp - 0) 2147483649 2147483648)
       (mset! r14 7 48)
       (set! r14 r14)
       (set! (rbp - 16) (mref (rbp - 8) (rbp - 0)))
       (jump r15)))
   '(begin
      (with-label L.__main.4 (set! r15 r15))
      (set! r14 r12)
      (set! r12 (+ r12 16))
      (set! r14 (+ r14 1))
      (set! r10 (rbp - 0))
      (set! r11 2147483649)
      (set! r10 (+ r10 r11))
      (set! r11 2147483648)
      (mset! r10 0 r11)
      (mset! r14 7 48)
      (set! r14 r14)
      (set! r10 (rbp - 8))
      (set! r11 (rbp - 0))
      (set! r10 (mref r10 r11))
      (set! (rbp - 16) r10)
      (jump r15)))

  (check-equal?
   (patch-instructions
    '(begin
       (with-label L.__main.4 (set! r15 r15))
       (set! r14 r12)
       (set! r12 (+ r12 16))
       (set! r14 (+ r14 1))
       (mset! r14 -1 40)
       (mset! r14 7 48)
       (set! r14 r14)
       (set! (rbp - 16) (mref r14 (rbp - 8)))
       (jump r15)))
   '(begin
      (with-label L.__main.4 (set! r15 r15))
      (set! r14 r12)
      (set! r12 (+ r12 16))
      (set! r14 (+ r14 1))
      (mset! r14 -1 40)
      (mset! r14 7 48)
      (set! r14 r14)
      (set! r10 (rbp - 8))
      (set! r10 (mref r14 r10))
      (set! (rbp - 16) r10)
      (jump r15))
   )

  (check-equal?
   (patch-instructions
    '(begin
       (with-label L.__main.4 (set! r15 r15))
       (set! r14 r12)
       (set! r12 (+ r12 16))
       (set! r14 (+ r14 1))
       (mset! r14 -1 r12)
       (mset! (rbp - 16) (rbp - 8) (rbp - 0))
       (set! rax r14)
       (jump r15)))
   '(begin
      (with-label L.__main.4 (set! r15 r15))
      (set! r14 r12)
      (set! r12 (+ r12 16))
      (set! r14 (+ r14 1))
      (mset! r14 -1 r12)
      (set! r10 (rbp - 16))
      (set! r11 (rbp - 8))
      (set! r10 (+ r10 r11))
      (set! r11 (rbp - 0))
      (mset! r10 0 r11)
      (set! rax r14)
      (jump r15)))

  (check-equal?
   (patch-instructions
    '(begin
       (with-label L.__main.4 (set! r15 r15))
       (set! r14 r12)
       (set! r12 (+ r12 16))
       (set! r14 (+ r14 1))
       (mset! r14 -1 r12)
       (mset! r14 7 (rbp - 8))
       (set! rax r14)
       (jump r15)))
   '(begin
      (with-label L.__main.4 (set! r15 r15))
      (set! r14 r12)
      (set! r12 (+ r12 16))
      (set! r14 (+ r14 1))
      (mset! r14 -1 r12)
      (set! r10 (rbp - 8))
      (mset! r14 7 r10)
      (set! rax r14)
      (jump r15)))

  (check-equal?
   (patch-instructions
    '(begin
       (with-label L.__main.4 (set! r15 r15))
       (set! r14 r12)
       (set! r12 (+ r12 16))
       (set! r14 (+ r14 1))
       (mset! r14 -1 r12)
       (mset! r14 (rbp - 0) (rbp - 8))
       (set! rax r14)
       (jump r15)))
   '(begin
      (with-label L.__main.4 (set! r15 r15))
      (set! r14 r12)
      (set! r12 (+ r12 16))
      (set! r14 (+ r14 1))
      (mset! r14 -1 r12)
      (set! r10 (rbp - 8))
      (set! r11 (rbp - 0))
      (mset! r14 r11 r10)
      (set! rax r14)
      (jump r15)))

  (check-equal?
   (patch-instructions
    '(begin
       (with-label L.__main.4 (set! r15 r15))
       (set! r14 r12)
       (set! r12 (+ r12 16))
       (set! r14 (+ r14 1))
       (mset! r14 -1 r12)
       (mset! (rbp - 0) 7 1)
       (set! rax r14)
       (jump r15)))
   '(begin
      (with-label L.__main.4 (set! r15 r15))
      (set! r14 r12)
      (set! r12 (+ r12 16))
      (set! r14 (+ r14 1))
      (mset! r14 -1 r12)
      (set! r10 (rbp - 0))
      (mset! r10 7 1)
      (set! rax r14)
      (jump r15)))

  (check-equal?
   (patch-instructions
    '(begin
       (with-label L.__main.4 (set! r15 r15))
       (set! r14 r12)
       (set! r12 (+ r12 16))
       (set! r14 (+ r14 1))
       (mset! r14 -1 r12)
       (mset! (rbp - 0) 7 (rbp - 8))
       (set! rax r14)
       (jump r15)))
   '(begin
      (with-label L.__main.4 (set! r15 r15))
      (set! r14 r12)
      (set! r12 (+ r12 16))
      (set! r14 (+ r14 1))
      (mset! r14 -1 r12)
      (set! r10 (rbp - 8))
      (set! r11 (rbp - 0))
      (mset! r11 7 r10)
      (set! rax r14)
      (jump r15)))

  (pretty-display
   '(begin (with-label L.__main.264 (set! r15 r15)) (set! r14 0) (set! r14 (arithmetic-shift-right r14 3)) (set! r14 r14) (set! r13 2) (set! r13 (+ r13 r14)) (set! r14 r13) (set! r14 r14) (set! r14 (* r14 8)) (set! r14 r14) (set! r13 r12) (set! r12 (+ r12 r14)) (set! r14 r13) (set! r14 r14) (set! r14 (+ r14 2)) (set! r14 r14) (set! r13 L.tmp.7) (mset! r14 -2 r13) (set! r13 16) (mset! r14 6 r13) (set! r14 r14) (set! r13 16) (set! r13 (arithmetic-shift-right r13 3)) (set! r13 r13) (set! r9 2) (set! r9 (+ r9 r13)) (set! r13 r9) (set! r13 r13) (set! r13 (* r13 8)) (set! r13 r13) (set! r9 r12) (set! r12 (+ r12 r13)) (set! r13 r9) (set! r13 r13) (set! r13 (+ r13 2)) (set! r13 r13) (set! r9 L.tmp.8) (mset! r13 -2 r9) (set! r9 16) (mset! r13 6 r9) (set! r13 r13) (set! r9 0) (set! r9 (arithmetic-shift-right r9 3)) (set! r9 r9) (set! r9 r9) (set! r9 (* r9 8)) (set! r9 r9) (set! r9 r9) (set! r9 (+ r9 14)) (set! r9 r9) (set! r14 r14) (mset! r13 r9 r14) (set! r14 8) (set! r14 (arithmetic-shift-right r14 3)) (set! r14 r14) (set! r14 r14) (set! r14 (* r14 8)) (set! r14 r14) (set! r14 r14) (set! r14 (+ r14 14)) (set! r14 r14) (set! r9 r13) (mset! r13 r14 r9) (set! r14 (mref r13 -2)) (set! r14 r14) (set! rdx 16) (set! rsi 8) (set! rdi r13) (set! r15 r15) (jump r14) (with-label L.tmp.243 (set! r15 (mref (rbp - 0) -2))) (set! r14 r15) (set! rdx (rbp - 16)) (set! rsi (rbp - 8)) (set! rdi (rbp - 0)) (set! r15 (rbp - 24)) (jump r14) (with-label L.tmp.242 (set! rax (rbp - 16))) (jump (rbp - 24)) (with-label L.tmp.245 (jump L.tmp.243)) (with-label L.tmp.244 (jump L.tmp.242)) (with-label L.rp.143 (set! rbp (+ rbp 32))) (set! r15 rax) (set! r15 r15) (compare r15 6) (jump-if != L.tmp.244) (jump L.tmp.245) (with-label L.tmp.8 (set! (rbp - 24) r15)) (set! r15 rdi) (set! (rbp - 16) rsi) (set! (rbp - 8) rdx) (set! r14 0) (set! r14 (arithmetic-shift-right r14 3)) (set! r14 r14) (set! r14 r14) (set! r14 (* r14 8)) (set! r14 r14) (set! r14 r14) (set! r14 (+ r14 14)) (set! r14 r14) (set! r14 (mref r15 r14)) (set! r14 r14) (set! r13 8) (set! r13 (arithmetic-shift-right r13 3)) (set! r13 r13) (set! r13 r13) (set! r13 (* r13 8)) (set! r13 r13) (set! r13 r13) (set! r13 (+ r13 14)) (set! r13 r13) (set! r15 (mref r15 r13)) (set! (rbp - 0) r15) (set! r15 (mref r14 -2)) (set! r13 r15) (set! rbp (- rbp 32)) (set! rdi r14) (set! rsi (rbp - -24)) (set! rdx (rbp - -16)) (set! r15 L.rp.143) (jump r13) (with-label L.tmp.247 (set! rax 1086)) (jump r15) (with-label L.tmp.249 (set! rax 1086)) (jump r15) (with-label L.tmp.251 (set! rax 6)) (jump r15) (with-label L.tmp.250 (set! rax 14)) (jump r15) (with-label L.tmp.248 (set! r14 r14)) (compare r14 r13) (jump-if < L.tmp.250) (jump L.tmp.251) (with-label L.tmp.257 (jump L.tmp.249)) (with-label L.tmp.256 (jump L.tmp.248)) (with-label L.join.252 (set! r9 r9)) (compare r9 6) (jump-if != L.tmp.256) (jump L.tmp.257) (with-label L.tmp.254 (set! r9 14)) (jump L.join.252) (with-label L.tmp.255 (set! r9 6)) (jump L.join.252) (with-label L.tmp.246 (set! r9 r14)) (set! r9 (bitwise-and r9 7)) (set! r9 r9) (set! r9 r9) (compare r9 0) (jump-if = L.tmp.254) (jump L.tmp.255) (with-label L.tmp.263 (jump L.tmp.247)) (with-label L.tmp.262 (jump L.tmp.246)) (with-label L.join.258 (set! r9 r9)) (compare r9 6) (jump-if != L.tmp.262) (jump L.tmp.263) (with-label L.tmp.260 (set! r9 14)) (jump L.join.258) (with-label L.tmp.261 (set! r9 6)) (jump L.join.258) (with-label L.tmp.7 (set! r15 r15)) (set! r14 rdi) (set! r14 rsi) (set! r13 rdx) (set! r9 r13) (set! r9 (bitwise-and r9 7)) (set! r9 r9) (set! r9 r9) (compare r9 0) (jump-if = L.tmp.260) (jump L.tmp.261)))

  (check-equal?
   (patch-instructions
    '(begin
       (with-label L.__main.264 (set! r15 r15))
       (set! r14 0)
       (set! r14 (arithmetic-shift-right r14 3))
       (set! r14 r14)
       (set! r13 2)
       (set! r13 (+ r13 r14))
       (set! r14 r13)
       (set! r14 r14)
       (set! r14 (* r14 8))
       (set! r14 r14)
       (set! r13 r12)
       (set! r12 (+ r12 r14))
       (set! r14 r13)
       (set! r14 r14)
       (set! r14 (+ r14 2))
       (set! r14 r14)
       (set! r13 L.tmp.7)
       (mset! r14 -2 r13)
       (set! r13 16)
       (mset! r14 6 r13)
       (set! r14 r14)
       (set! r13 16)
       (set! r13 (arithmetic-shift-right r13 3))
       (set! r13 r13)
       (set! r9 2)
       (set! r9 (+ r9 r13))
       (set! r13 r9)
       (set! r13 r13)
       (set! r13 (* r13 8))
       (set! r13 r13)
       (set! r9 r12)
       (set! r12 (+ r12 r13))
       (set! r13 r9)
       (set! r13 r13)
       (set! r13 (+ r13 2))
       (set! r13 r13)
       (set! r9 L.tmp.8)
       (mset! r13 -2 r9)
       (set! r9 16)
       (mset! r13 6 r9)
       (set! r13 r13)
       (set! r9 0)
       (set! r9 (arithmetic-shift-right r9 3))
       (set! r9 r9)
       (set! r9 r9)
       (set! r9 (* r9 8))
       (set! r9 r9)
       (set! r9 r9)
       (set! r9 (+ r9 14))
       (set! r9 r9)
       (set! r14 r14)
       (mset! r13 r9 r14)
       (set! r14 8)
       (set! r14 (arithmetic-shift-right r14 3))
       (set! r14 r14)
       (set! r14 r14)
       (set! r14 (* r14 8))
       (set! r14 r14)
       (set! r14 r14)
       (set! r14 (+ r14 14))
       (set! r14 r14)
       (set! r9 r13)
       (mset! r13 r14 r9)
       (set! r14 (mref r13 -2))
       (set! r14 r14)
       (set! rdx 16)
       (set! rsi 8)
       (set! rdi r13)
       (set! r15 r15)
       (jump r14)
       (with-label L.tmp.243 (set! r15 (mref (rbp - 0) -2)))
       (set! r14 r15)
       (set! rdx (rbp - 16))
       (set! rsi (rbp - 8))
       (set! rdi (rbp - 0))
       (set! r15 (rbp - 24))
       (jump r14)
       (with-label L.tmp.242 (set! rax (rbp - 16)))
       (jump (rbp - 24))
       (with-label L.tmp.245 (jump L.tmp.243))
       (with-label L.tmp.244 (jump L.tmp.242))
       (with-label L.rp.143 (set! rbp (+ rbp 32)))
       (set! r15 rax)
       (set! r15 r15)
       (compare r15 6)
       (jump-if != L.tmp.244)
       (jump L.tmp.245)
       (with-label L.tmp.8 (set! (rbp - 24) r15))
       (set! r15 rdi)
       (set! (rbp - 16) rsi)
       (set! (rbp - 8) rdx)
       (set! r14 0)
       (set! r14 (arithmetic-shift-right r14 3))
       (set! r14 r14)
       (set! r14 r14)
       (set! r14 (* r14 8))
       (set! r14 r14)
       (set! r14 r14)
       (set! r14 (+ r14 14))
       (set! r14 r14)
       (set! r14 (mref r15 r14))
       (set! r14 r14)
       (set! r13 8)
       (set! r13 (arithmetic-shift-right r13 3))
       (set! r13 r13)
       (set! r13 r13)
       (set! r13 (* r13 8))
       (set! r13 r13)
       (set! r13 r13)
       (set! r13 (+ r13 14))
       (set! r13 r13)
       (set! r15 (mref r15 r13))
       (set! (rbp - 0) r15)
       (set! r15 (mref r14 -2))
       (set! r13 r15)
       (set! rbp (- rbp 32))
       (set! rdi r14)
       (set! rsi (rbp - -24))
       (set! rdx (rbp - -16))
       (set! r15 L.rp.143)
       (jump r13)
       (with-label L.tmp.247 (set! rax 1086))
       (jump r15)
       (with-label L.tmp.249 (set! rax 1086))
       (jump r15)
       (with-label L.tmp.251 (set! rax 6))
       (jump r15)
       (with-label L.tmp.250 (set! rax 14))
       (jump r15)
       (with-label L.tmp.248 (set! r14 r14))
       (compare r14 r13)
       (jump-if < L.tmp.250)
       (jump L.tmp.251)
       (with-label L.tmp.257 (jump L.tmp.249))
       (with-label L.tmp.256 (jump L.tmp.248))
       (with-label L.join.252 (set! r9 r9))
       (compare r9 6)
       (jump-if != L.tmp.256)
       (jump L.tmp.257)
       (with-label L.tmp.254 (set! r9 14))
       (jump L.join.252)
       (with-label L.tmp.255 (set! r9 6))
       (jump L.join.252)
       (with-label L.tmp.246 (set! r9 r14))
       (set! r9 (bitwise-and r9 7))
       (set! r9 r9)
       (set! r9 r9)
       (compare r9 0)
       (jump-if = L.tmp.254)
       (jump L.tmp.255)
       (with-label L.tmp.263 (jump L.tmp.247))
       (with-label L.tmp.262 (jump L.tmp.246))
       (with-label L.join.258 (set! r9 r9))
       (compare r9 6)
       (jump-if != L.tmp.262)
       (jump L.tmp.263)
       (with-label L.tmp.260 (set! r9 14))
       (jump L.join.258)
       (with-label L.tmp.261 (set! r9 6))
       (jump L.join.258)
       (with-label L.tmp.7 (set! r15 r15))
       (set! r14 rdi)
       (set! r14 rsi)
       (set! r13 rdx)
       (set! r9 r13)
       (set! r9 (bitwise-and r9 7))
       (set! r9 r9)
       (set! r9 r9)
       (compare r9 0)
       (jump-if = L.tmp.260)
       (jump L.tmp.261)))
   '(begin
      (with-label L.__main.264 (set! r15 r15))
      (set! r14 0)
      (set! r14 (arithmetic-shift-right r14 3))
      (set! r14 r14)
      (set! r13 2)
      (set! r13 (+ r13 r14))
      (set! r14 r13)
      (set! r14 r14)
      (set! r14 (* r14 8))
      (set! r14 r14)
      (set! r13 r12)
      (set! r12 (+ r12 r14))
      (set! r14 r13)
      (set! r14 r14)
      (set! r14 (+ r14 2))
      (set! r14 r14)
      (set! r13 L.tmp.7)
      (mset! r14 -2 r13)
      (set! r13 16)
      (mset! r14 6 r13)
      (set! r14 r14)
      (set! r13 16)
      (set! r13 (arithmetic-shift-right r13 3))
      (set! r13 r13)
      (set! r9 2)
      (set! r9 (+ r9 r13))
      (set! r13 r9)
      (set! r13 r13)
      (set! r13 (* r13 8))
      (set! r13 r13)
      (set! r9 r12)
      (set! r12 (+ r12 r13))
      (set! r13 r9)
      (set! r13 r13)
      (set! r13 (+ r13 2))
      (set! r13 r13)
      (set! r9 L.tmp.8)
      (mset! r13 -2 r9)
      (set! r9 16)
      (mset! r13 6 r9)
      (set! r13 r13)
      (set! r9 0)
      (set! r9 (arithmetic-shift-right r9 3))
      (set! r9 r9)
      (set! r9 r9)
      (set! r9 (* r9 8))
      (set! r9 r9)
      (set! r9 r9)
      (set! r9 (+ r9 14))
      (set! r9 r9)
      (set! r14 r14)
      (mset! r13 r9 r14)
      (set! r14 8)
      (set! r14 (arithmetic-shift-right r14 3))
      (set! r14 r14)
      (set! r14 r14)
      (set! r14 (* r14 8))
      (set! r14 r14)
      (set! r14 r14)
      (set! r14 (+ r14 14))
      (set! r14 r14)
      (set! r9 r13)
      (mset! r13 r14 r9)
      (set! r14 (mref r13 -2))
      (set! r14 r14)
      (set! rdx 16)
      (set! rsi 8)
      (set! rdi r13)
      (set! r15 r15)
      (jump r14)
      (with-label L.tmp.243 (set! r10 (rbp - 0)))
      (set! r15 (mref r10 -2))
      (set! r14 r15)
      (set! rdx (rbp - 16))
      (set! rsi (rbp - 8))
      (set! rdi (rbp - 0))
      (set! r15 (rbp - 24))
      (jump r14)
      (with-label L.tmp.242 (set! rax (rbp - 16)))
      (set! r10 (rbp - 24))
      (jump r10)
      (with-label L.tmp.245 (jump L.tmp.243))
      (with-label L.tmp.244 (jump L.tmp.242))
      (with-label L.rp.143 (set! rbp (+ rbp 32)))
      (set! r15 rax)
      (set! r15 r15)
      (compare r15 6)
      (jump-if != L.tmp.244)
      (jump L.tmp.245)
      (with-label L.tmp.8 (set! (rbp - 24) r15))
      (set! r15 rdi)
      (set! (rbp - 16) rsi)
      (set! (rbp - 8) rdx)
      (set! r14 0)
      (set! r14 (arithmetic-shift-right r14 3))
      (set! r14 r14)
      (set! r14 r14)
      (set! r14 (* r14 8))
      (set! r14 r14)
      (set! r14 r14)
      (set! r14 (+ r14 14))
      (set! r14 r14)
      (set! r14 (mref r15 r14))
      (set! r14 r14)
      (set! r13 8)
      (set! r13 (arithmetic-shift-right r13 3))
      (set! r13 r13)
      (set! r13 r13)
      (set! r13 (* r13 8))
      (set! r13 r13)
      (set! r13 r13)
      (set! r13 (+ r13 14))
      (set! r13 r13)
      (set! r15 (mref r15 r13))
      (set! (rbp - 0) r15)
      (set! r15 (mref r14 -2))
      (set! r13 r15)
      (set! rbp (- rbp 32))
      (set! rdi r14)
      (set! rsi (rbp - -24))
      (set! rdx (rbp - -16))
      (set! r15 L.rp.143)
      (jump r13)
      (with-label L.tmp.247 (set! rax 1086))
      (jump r15)
      (with-label L.tmp.249 (set! rax 1086))
      (jump r15)
      (with-label L.tmp.251 (set! rax 6))
      (jump r15)
      (with-label L.tmp.250 (set! rax 14))
      (jump r15)
      (with-label L.tmp.248 (set! r14 r14))
      (compare r14 r13)
      (jump-if < L.tmp.250)
      (jump L.tmp.251)
      (with-label L.tmp.257 (jump L.tmp.249))
      (with-label L.tmp.256 (jump L.tmp.248))
      (with-label L.join.252 (set! r9 r9))
      (compare r9 6)
      (jump-if != L.tmp.256)
      (jump L.tmp.257)
      (with-label L.tmp.254 (set! r9 14))
      (jump L.join.252)
      (with-label L.tmp.255 (set! r9 6))
      (jump L.join.252)
      (with-label L.tmp.246 (set! r9 r14))
      (set! r9 (bitwise-and r9 7))
      (set! r9 r9)
      (set! r9 r9)
      (compare r9 0)
      (jump-if = L.tmp.254)
      (jump L.tmp.255)
      (with-label L.tmp.263 (jump L.tmp.247))
      (with-label L.tmp.262 (jump L.tmp.246))
      (with-label L.join.258 (set! r9 r9))
      (compare r9 6)
      (jump-if != L.tmp.262)
      (jump L.tmp.263)
      (with-label L.tmp.260 (set! r9 14))
      (jump L.join.258)
      (with-label L.tmp.261 (set! r9 6))
      (jump L.join.258)
      (with-label L.tmp.7 (set! r15 r15))
      (set! r14 rdi)
      (set! r14 rsi)
      (set! r13 rdx)
      (set! r9 r13)
      (set! r9 (bitwise-and r9 7))
      (set! r9 r9)
      (set! r9 r9)
      (compare r9 0)
      (jump-if = L.tmp.260)
      (jump L.tmp.261)))
  )