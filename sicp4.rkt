#lang racket
(include "sicp3.rkt")

;scheme interpreter in scheme D:

;expression selectors
;enforces left-to-right evaluation of function args
(define (list-of-values exps env)
  (if (no-operands? exps) '()
      (let ((val (eval (first-operand exps) env)))
        (cons val (list-of-values (rest-operands exps) env)))))

(define text-of-quotation cadr)
(define assignment-variable cadr)
(define assignment-value caddr)
(define (definition-variable exp)
  (if (symbol? (cadr exp))
      (cadr exp)
      (caadr exp)))
(define (definition-value exp)
  (if (symbol? (cadr exp))
      (caddr exp)
      (make-lambda (cdadr exp)
                   (cddr exp))))
(define lambda-parameters cadr)
(define lambda-body cddr)
(define if-predicate cadr)
(define if-consequent caddr)
(define (if-alternative exp)
  (if (not (null? (cdddr exp)))
      (cadddr exp)
      'false))
(define begin-actions cdr)
(define first-exp car)
(define rest-exps cdr)
(define operator car)
(define operands cdr)
(define first-operand car)
(define rest-operands cdr)
(define cond-clauses cdr)
(define (cond-arrow-clause? exp)
  (and (= (length exp) 3)
       (eq? (cadr exp) '=>)))
(define cond-arrow-func caddr)
(define cond-predicate car)
(define cond-actions cdr)
(define not-body cadr)
(define and-body cdr)
(define or-body cdr)
(define (let-defs exp)
  (if (named-let? exp)
      (caddr exp)
      (cadr exp)))
(define (let-body exp)
  (if (named-let? exp)
      (cadddr exp)
      (caddr exp)))
(define let-def-var car)
(define let-def-exp cadr)
(define let-name-var cadr)
(define procedure-parameters cadr)
(define procedure-body caddr)
(define procedure-evnironment cadddr)
(define enclosing-envirnoment cdr)
(define first-frame car)
(define empty-env '())

;expression constructors
(define (make-not exp)
  (list 'not exp))

(define (make-and exp1 exp2)
  (list 'and exp1 exp2))

;or expressed in nots/ands
(define (make-or exp1 exp2)
  (make-not
   (make-and (make-not exp1) (make-not exp1))))
    
(define (make-lambda parameters body)
  (cons 'lambda (cons parameters body)))

(define (make-if predicate consequent alternative)
  (list 'if predicate consequent alternative))

(define (sequence->exp seq)
  (cond ((null? seq) seq)
        ((last-exp? seq) (first-exp seq))
        (else (make-begin seq))))

(define (make-begin seq) (cons 'begin seq))

(define (make-cond-clause predicate consequent)
  (cons predicate consequent))

(define (make-let defs-list body)
  (list 'let defs-list body))

(define (make-let* defs-list body)
  (list 'let* defs-list body))

;convert cond arrow clauses to a canonical form
(define (convert-arrow-clause exp env)
  (make-cond-clause
   (cond-predicate exp)
   (apply
    (eval (cond-arrow-func exp) env)
    (list (eval (cond-predicate exp) env)))))
  
;express or in terms of not/and ala demorgan's laws
(define (or->nand exp)
  (let ((exps (or-body exp)))
    (foldl make-or
          (make-or (car exps) (cadr exps))
          (cddr exps))))

(define (make-procedure parameters body env)
  (list 'procedure parameters body env))

(define (make-frame variables values)
  (cons variables values))

;expression predicates
(define (true? exp)
  (not (eq? exp #f)))
(define (false? exp)
  (eq? exp #f))
(define (tagged-list? exp tag)
  (and (pair? exp) (eq? (car exp) tag)))
(define (self-evaluating exp)
  (if (or (number? exp) (string? exp)) #t #f))
(define variable? symbol?)
(define (quoted? exp) (tagged-list? exp 'quote))
(define (last-exp? seq) (null? (cdr seq)))
;everything is a list in lisp
;everything is an application D:
(define application? pair?)
(define no-operands? null?)
(define (cond? exp) (tagged-list? exp 'cond))
(define (cond-else-clause? clause)
  (eq? (cond-predicate clause) 'else))
(define (named-let? exp)
  (not (pair? (cadr exp))))
(define (compound-procedure? p)
  (tagged-list? p 'procedure))

;expressions evaluations
(define (eval-if exp env)
  (if (true? (eval (if-predicate exp) env))
      (eval (if-consequent exp) env)
      (eval (if-alternative exp) env)))

(define (eval-sequence exps env)
  (cond ((last-exp? exps) (eval (first-exp exps) env))
        (else (eval (first-exp exps) env)
              (eval-sequence (rest-exps exps) env))))

(define (eval-assignment exp env)
  (set-variable-value! (assignment-variable exp)
                       (eval (assignment-value exp) env)
                       env))

(define (eval-definition exp env)
  (define-variable! 
    (definition-variable exp)
    (eval (definition-value exp) env)
    env)
  'ok)

(define (eval-lambda exp env)
  (make-procedure (lambda-parameters exp)
                  (lambda-body exp)
                  env))

(define (eval-not exp env)
  (if (= (length (not-body exp)) 1)
      (not (true? (eval (not-body exp) env)))
      (error "arity mismatch: not requires 1 arg")))

(define (eval-and exp env)
  (if (>= (length (and-body exp)) 2)
      (foldl (lambda (acc x)
               (if (not acc) #f (true? (eval x env))))
             #t
             (and-body exp))
      (error "arity mismatch: and requires >=2 args")))

(define (eval-or exp env)
  (if (>= (length (or-body exp)) 2)
      (eval (or->nand exp) env)
      (error "airty mismatch: or requires >=2 args")))

(define (eval-cond exp env)
  (define (expand-clauses clauses)
    (if (null? clauses)
        'false
        (let ((first (car clauses))
              (rest (cdr clauses)))
          (cond ((cond-arrow-clause? first)
                 (expand-clauses (cons (convert-arrow-clause first) rest)))
                ((cond-else-clause? first)
                 (if (null? rest)
                     (sequence->exp (cond-actions first))
                     (error "else clause is not last")))
                (else (make-if (cond-predicate first)
                         (sequence->exp (cond-actions first))
                         (expand-clauses rest)))))))
  (eval (expand-clauses (cond-clauses exp)) env))

(define (eval-let exp env)
  (define (lambda-setup exp2)
    (make-lambda
     (map car (let-defs exp2)) 
     (let-body exp2) env))
  (if (named-let? exp)
      (let ((var-name (list (let-name-var exp) (lambda-setup exp))))
        (eval
         (make-let
          (cons var-name (let-defs exp))
          (let-body exp))
         env))
      (apply
       (lambda-setup exp)
       (map (lambda (p)
              (eval (cdr p) env))
            (let-defs exp)))))

(define (eval-let* exp env)
  (define (let*->let exp)
    (if (null? (let-defs exp))
        (make-let '() (let-body exp))
        (make-let (list (car (let-defs exp)))
                  (let*->let 
                   (make-let* (cdr (let-defs exp))
                              (let-body exp))))))
  (eval (let*->let exp) env))
  
(define op-table
  (foldl (lambda (op table)
           (put table (car op) (cadr op) (caddr op)))
         (make-table eq?)
         (list (list 'set! eval-assignment)
               (list 'define eval-definition)
               (list 'lambda eval-lambda)
               (list 'if eval-if)
               (list 'begin eval-begin)
               (list 'not eval-not)
               (list 'and eval-and)
               (list 'or eval-or)
               (list 'cond eval-cond)
               (list 'let eval-let)
               (list 'let* eval-let*))))

;environment stuff
(

(define (eval exp env)
  (cond ((self-evaluating? exp) exp)
        ((variable? exp) (lookup-variable exp env))
        ((quoted? exp) (text-of-quotation exp))
        ;see if this operation is in the table
        ((lookup op-table (car exp)) 
         ((lookup op-table (car exp)) exp env))
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

