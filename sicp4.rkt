#lang racket
;scheme interpreter in scheme D:

;expression selectors
;enforces left-to-right evaluation of function args
(define (list-of-values exps env)
  (if (no-operands? exps) '()
      (let ((val (eval (first-operand exps) env)))
        (cons val (list-of-values (rest-operands exps) env)))))
        
;expression predicates

;expressions evaluations

(define (eval exp env)
  (cond ((self-evaluating? exp) exp)
        ((variable? exp) (lookup-variable exp env))
        ((quoted? exp) (text-of-quotation exp))
        ((assignment? exp) (eval-assignment exp env))
        ((definition? exp) (eval-definition exp env))
        ((if? exp) (eval-if exp env))
        ((lambda? exp)
         (make-procedure (lambda-paramaters exp)
                         (lambda-body exp)
                         env))
        ((begin? exp)
         (eval-sequence (begin-actions exp) env))
        ((cond? exp) (eval (cond->if exp) env))
        ((application? exp)
         (apply (eval (operator exp) env)
                (list-of-values (operands exp) env)))
        (else (error "wut"))))

(define (apply procedure arguments)
  ((primitive-procedure? procedure)
   (apply-primitive-procedure procedure arguments))
  ((compound-procedure? procedure)
   (eval-sequence
    (procedure-body procedure)
    (extend-environment
     (procedure-paramters procedure)
     arguments
     (procedure-environment procedure))))
  (else (error "wut")))