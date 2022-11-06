#lang racket

(require
  cpsc411/compiler-lib
  cpsc411/graph-lib
  cpsc411/ptr-run-time
  racket/trace
  rackunit)

(provide generate-x64)

;; Produces the x64 instruction sequence from the source language; paren-x64-v8
;;
;; Paren-x64-v8 -> x64-instruction-sequence
(define (generate-x64 p)
  (define (trg? e)
    (or (register? e) (label? e)))

  (define (triv? e)
    (or (int64? e) (trg? e)))

  (define (addr? e)
    (match e
      [`(,fbp - ,dispoffset)
       #:when (and (frame-base-pointer-register? fbp) (dispoffset? dispoffset))
       #t]
      [`(,reg + ,int32) #:when (and (register? reg) (int32? int32)) #t]
      [`(,reg_1 + ,reg_2) #:when (and (register? reg_1) (register? reg_2)) #t]
      [_ #f]))

  (define (loc? e)
    (or (register? e) (addr? e)))

  ;; Paren-x64-v8.Statement -> String
  (define (generate-x64-instruction s)
    (match s
      [`(set! ,addr ,int32)
       #:when (int32? int32)
       (format "mov ~a, ~a" (loc->instruction addr) int32)]
      [`(set! ,addr ,trg)
       #:when (trg? trg)
       (format "mov ~a, ~a" (loc->instruction addr) trg)]
      [`(set! ,reg ,loc)
       #:when (loc? loc)
       (format "mov ~a, ~a" reg (loc->instruction loc))]
      [`(set! ,reg ,triv)
       #:when (triv? triv)
       (format "mov ~a, ~a" reg triv)]
      [`(set! ,reg (,binop ,reg ,int32))
       #:when (int32? int32)
       (binop->instruction binop reg int32)]
      [`(set! ,reg (,binop ,reg ,loc))
       (binop->instruction binop reg (loc->instruction loc))]
      [`(with-label ,label ,s)
       (format "~a:\n~a" label (generate-x64-instruction s))]
      [`(jump ,trg)
       (format "jmp ~a" trg)]
      [`(compare ,reg ,opand)
       (format "cmp ~a, ~a" reg opand)]
      [`(jump-if ,relop ,label)
       (jump-if->instruction relop label)]))

  ;; Paren-x64-v8.Loc -> String
  (define (loc->instruction loc)
    (match loc
      [`,reg #:when (register? reg) (symbol->string reg)]
      [`(,fbp - ,off) #:when (frame-base-pointer-register? fbp) (format "QWORD [~a - ~a]" fbp off)]
      [`(,reg + ,int32) #:when (int32? int32) (format "QWORD [~a + ~a]" reg int32)]
      [`(,reg_1 + ,reg_2) (format "QWORD [~a + ~a]" reg_1 reg_2)]
      ))

  ;; Paren-x64-v8.Relop Paren-x64-v8.Label -> String
  (define (jump-if->instruction relop label)
    (match relop
      [`< (format "jl ~a" label)]
      [`<= (format "jle ~a" label)]
      [`= (format "je ~a" label)]
      [`>= (format "jge ~a" label)]
      [`> (format "jg ~a" label)]
      [`!= (format "jne ~a" label)]))

  ;; Paren-x64-v8.Binop String String -> String
  (define (binop->instruction b dest src)
    (match b
      [`+ (format "add ~a, ~a" dest src)]
      [`* (format "imul ~a, ~a" dest src)]
      [`- (format "sub ~a, ~a" dest src)]
      [`bitwise-and (format "and ~a, ~a" dest src)]
      [`bitwise-ior (format "or ~a, ~a" dest src)]
      [`bitwise-xor (format "xor ~a, ~a" dest src)]
      [`arithmetic-shift-right (format "sar ~a, ~a" dest src)]))

  (match p
    [`(begin ,s ...)
     (foldr (lambda (ins res) (string-append ins "\n" res))
            ""
            (map generate-x64-instruction s))]))

(module+ tests
  (check-equal? (generate-x64 '(begin (set! rax 42)))
                "mov rax, 42\n")

  (check-equal? (generate-x64 '(begin (set! rax 42) (set! rax (+ rax 0))))
                "mov rax, 42\nadd rax, 0\n")

  (check-equal? (generate-x64
                '(begin
                    (set! (rbp - 0) 0)
                    (set! (rbp - 8) 42)
                    (set! rax (rbp - 0))
                    (set! rax (+ rax (rbp - 8)))))
                "mov QWORD [rbp - 0], 0\nmov QWORD [rbp - 8], 42\nmov rax, QWORD [rbp - 0]\nadd rax, QWORD [rbp - 8]\n")

  (check-equal? (generate-x64
                '(begin
                    (set! rax 0)
                    (set! rbx 0)
                    (set! r9 42)
                    (set! rax (+ rax r9))))
                "mov rax, 0\nmov rbx, 0\nmov r9, 42\nadd rax, r9\n")

  (check-equal? (generate-x64
                '(begin
                    (set! rax 12)
                    (set! rbx 11)
                    (with-label L.A.1
                      (set! rbx (+ rbx 1)))
                    (compare rax rbx)
                    (jump-if >= L.A.1)
                    (set! rax 0)))
                "mov rax, 12\nmov rbx, 11\nL.A.1:\nadd rbx, 1\ncmp rax, rbx\njge L.A.1\nmov rax, 0\n")

  (check-equal? (generate-x64
                '(begin
                    (set! rax 12)
                    (set! rbx 11)
                    (with-label L.A.1
                      (set! rbx (+ rbx 1)))
                    (compare rax rbx)
                    (jump-if >= L.A.1)
                    (jump L.B.2)
                    (with-label L.B.2
                      (set! rax 0))))
                "mov rax, 12\nmov rbx, 11\nL.A.1:\nadd rbx, 1\ncmp rax, rbx\njge L.A.1\njmp L.B.2\nL.B.2:\nmov rax, 0\n")

  (check-equal? (generate-x64
                '(begin
                    (set! rax 0)
                    (set! rbx 15)
                    (with-label L.A.0
                      (set! rax (+ rax 1)))
                    (set! rax (bitwise-and rax rbx))
                    (compare rax 8)
                    (jump-if = L.A.0)))
                "mov rax, 0\nmov rbx, 15\nL.A.0:\nadd rax, 1\nand rax, rbx\ncmp rax, 8\nje L.A.0\n")

  (check-equal?
  (generate-x64
    '(begin
      (set! r12 (r8 + r11))
      (set! (r8 + r9) 5)
      (set! (r8 + r9) r11)
      (set! (r8 + r9) L.start.1)
      (set! (r8 + 8) r11)
      (set! (r8 + -7) r11)))

  "mov r12, QWORD [r8 + r11]
  mov QWORD [r8 + r9], 5
  mov QWORD [r8 + r9], r11
  lea QWORD [r8 + r9], [rel L.start.1]
  mov QWORD [r8 + 8], r11
  mov QWORD [r8 + -7], r11")
)