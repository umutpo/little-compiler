# Little Compiler
An optimizing ahead-of-time compiler from a high-level language with functional and imperative features to x86-64

## Overview
This compiler provides various passes, each associated with a single file, that compile the initial high-level language, defined below, to many intermediate source 
languages which at the end compiles to x86-64. The order of these passes can be seen in `compiler.rkt's pass-map`.

## Source Language
```
p ::= (module (define x (lambda (x ...) value)) ... value)

value ::= triv
      |	  (let ([x value] ...) value)
      |	  (if value value value)
      |   (call value value ...)

triv ::= x
     |   fixnum
     |   #t
     |   #f
     |   empty
     |   (void)
     |   (error uint8)
     |   ascii-char-literal
     |   (lambda (x ...) value)
     
x ::= name?
  |   prim-f

prim-f ::= *
       |   +
       |   -
       |   <
       |   <=
       |   >
       |   >=
       |   eq?
       |   fixnum?
       |   boolean?
       |   empty?
       |   void?
       |   ascii-char?
       |   error?
       |   not
       |   pair?
       |   procedure?
       |   vector?
       |   cons
       |   car
       |   cdr
       |   make-vector
       |   vector-length
       |   vector-set!
       |   vector-ref
       |   procedure-arity

fixnum ::= int61?
 	 	 	 	 
uint8 ::= uint8?
 	 	 	 	 
ascii-char-literal ::= ascii-char-literal?
```

## Project Background
This project is done with two other classmates as a final project in UBC CPSC 411 on March 2022. The design of the compiler belongs to our instructor at the time, William J. Bowman.
