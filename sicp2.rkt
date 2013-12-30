#lang racket
;constants for testing use
(define tree1 (list 1 2 (list 3 4) (list 4 (list 6 7) 8) 9))
(define smalllist (list 1 2 3))
(define list1 (list 1 2 3 4 5 6 7 8 9))

;helpers
;sum a list
(define (sum l)
  (if (null? l) 0
      (+ (car l) (sum (cdr l)))))

;reverse a list
(define (reverse l)
  (define (inner acc subl)
    (if (null? subl) acc
        (inner (cons (car subl) acc) (cdr subl))))
  (inner null l))

;returns [lower, upper]
(define (range lower upper)
  (if (> lower upper) null
      (cons lower (range (+ 1 lower) upper))))
  
;removes the first instance of element from l
(define (remove element l)
  (cond ((null? l) l)
        ((= element (car l)) (cdr l))
        (else (cons (car l) (remove element (cdr l))))))

;2.6: church numerals
(define zero (lambda (f) (lambda (x) x)))
(define (succ n)
  (lambda (f) (lambda (x) (f ((n f) x)))))
(define one (lambda (f) (lambda (x) (f x))))
(define two (lambda (f) (lambda (x) (f (f x)))))
(define (add m n) 
  (lambda (f) 
    (lambda (x)
      ((m f) ((n f) x)))))

;2.7 to 2.16: interval arithmetic
(define make-interval cons)
(define lower-bound car)
(define upper-bound cdr)
(define (sub m n)
  (make-interval
    (- (lower-bound m) (upper-bound n))
    (- (upper-bound m) (lower-bound n))))

;change coin
;Intuition: you want to find valid paths in the tree, valid 
;being that the sequence of coins in the path exactly equals n
(define (change n cointypes)
  (cond ((null? cointypes) 0)
        ((= n 0) 1)
        ((< n (car cointypes)) 0) 
        (else (+ (change (- n (car cointypes)) cointypes)
                 (change n (cdr cointypes))))))

;dotted tail notation!
(define (same-parity . l)
  (define (inner acc subl)
    (if (null? subl) acc
        (if (null? acc) (inner (cons (car subl) acc) (cdr subl))
            (if (= (remainder (car subl) 2) (remainder (car acc) 2))
                (inner (cons (car subl) acc) (cdr subl))
                (inner acc (cdr subl))))))
  (inner null l))

;2.30, 2.31
(define (tree-map f t)
  (map (lambda (subt)
         (if (pair? subt) (tree-map f subt)
             (f subt)))
       t))
(define (square-tree t) (tree-map (lambda (x) (* x x)) t))

;2.32
;intuition: an element is either in a subset or not in a subset
;for a set of size n there will be 2^n subsets
(define (subsets s)
  (if (null? s) (cons null s)
      (let ((sl (subsets (cdr s))))
      (append (map (lambda (subl) (cons (car s) subl)) sl) sl))))

;signal-flow paradigm (flow-based programming?)
;and sequences as interfaces

;2.34: implementation of horner's method
(define (horner x coefficient-sequence)
  (foldr (lambda (current higher-terms)
           (+ current (* x higher-terms)))
         0
         coefficient-sequence))

;2.35 count leaves of a tree
(define (leaf-count t)
  (foldr (lambda (leaf-count acc) (+ leaf-count acc))
         0
         (map (lambda (subt)
                (if (pair? subt) (leaf-count subt) 1))
              t)))

;2.36 accumulate for n lists
(define (accumulate-n f acc lists)
  (if (null? (car lists)) null
      (cons (foldr f acc (map car lists))
            (accumulate-n f acc (map cdr lists)))))

;2.37 matrix library!
;represent vectors as rows in a matrix
;e.g. ((1 2 3 4) (1 2 3 4)) is a 2x4 matrix
(define (dot-product u v)
  (foldr + 0 (map * u v)))

(define (vector-mult m v)
  (accumulate-n + 0 (map (lambda (vec c)
                          (map (lambda (xi) (* xi c)) vec))
                         m v)))

(define (matrix-mult m n)
  (map (lambda (v) (vector-mult m v)) n))
      
(define (matrix-transpose m)
  (accumulate-n cons null m))

;2.41
;produces all unique triples (i, j, k) such that
; i < j < k and i,j,k <= n
(define (unique-triples n)
  (foldr (lambda (i acc)
           (append 
            acc
           (foldr (lambda (j acc2) 
                    (append acc2 
                            (map (lambda (k)
                                   (list i j k))
                                 (range (+ j 1) n))))
                  null
                  (range (+ i 1) n))))
         null
        (range 1 n)))

(define (triples-pair-sum n s)
  (foldr (lambda (t acc)
           (cons (reverse (cons (sum t) t)) acc))
         null
         (filter (lambda (t) (= (sum t) s))
                 (unique-triples n))))

;2.54 equality for lists containing symbols           
(define (equals? l1 l2)
  (cond ((and (null? l1) (null? l2)) true)
        ((and (null? l1) (not (null? l2))) false)
        ((and (not (null? l1)) (null? l2)) false)
        (else (and (eq? (car l1) (car l2)) (equals? (cdr l1) (cdr l2))))))

;symbolic differentiation (on infix operators!!!)
(define (deriv exp var)
  ;symbolic checks
  (define constant? number?)
  (define variable? symbol?)
  (define (same-variable? v1 v2)
    (and (and (variable? v1) (variable? v2))
         (eq? v1 v2)))
  (define (make-sum a1 a2) 
    (cond ((and (number? a1) (number? a2)) (+ a1 a2))
          ((eq? a1 0) a2)
          ((eq? a2 0) a1)
          (else (list a1 '+ a2))))
  (define (make-product a1 a2)
    (cond ((and (number? a1) (number? a2)) (* a1 a2))
          ((or (eq? a1 0) (eq? a2 0)) 0)
          ((eq? a1 1) a2)
          ((eq? a2 1) a1)
          (else (list a1 '* a2))))
  (define (make-exponentiation base exponent)
    (cond ((eq? exponent 1) base)
          ((eq? exponent 0) 1)
          (else (list base '** exponent))))
  (define (operator? symbol) 
    (lambda (a) (and (pair? a) (eq? symbol (cadr a)))))
  (define sum? (operator? '+))
  (define addend car)
  (define augend caddr)
  (define product? (operator? '*))
  (define multiplier car)
  (define multiplicand caddr)
  (define exponentiation? (operator? '**))
  (define base car)
  (define exponent caddr)
  (define (more-terms? e)
    (if (and (pair? e) (pair? (cdddr e))) #t #f))
  (define get-next-operation cadddr)
  (define get-next-terms cddddr)
  (define (get-cur-term e)
    (list (car e) (cadr e) (caddr e)))
  ;differentiation algorithm
  (cond ((more-terms? exp)
         (let ((cur-term (deriv (get-cur-term exp) var))
               (next-operation (get-next-operation exp))
               (next-terms (get-next-terms exp)))
           (cond ((eq? next-operation '+)
                  (make-sum cur-term (deriv next-terms var)))
                 ((eq? next-operation '*)
                  (make-product cur-term (deriv next-terms var)))
                 ((eq? next-operation '**)
                  (make-exponentiation cur-term (deriv next-terms var))))))
        ((constant? exp) 0)
        ((variable? exp)
         (if (same-variable? exp var) 1 0))        
        ;can only do numerical exponents
        ((exponentiation? exp)
         (if (eq? (exponent exp) 0) 1
             (make-product
              (exponent exp)
              (make-exponentiation
               (base exp)
               (- (exponent exp) 1)))))
        ((product? exp)
         (make-sum
          (make-product (multiplier exp) (deriv (multiplicand exp) var))
          (make-product (multiplicand exp) (deriv (multiplier exp) var))))
        ((sum? exp)
         (make-sum (deriv (addend exp) var)
                   (deriv (augend exp) var)))))

(define (element-in-set? e set)
  (cond ((null? set) #f)
        ((eq? (car set) e) #t)
        (else (element-in-set? e (cdr set)))))
        
;2.61 adjoin of ordered set
(define (adjoin-set s x)
  (cond ((null? s) (list x))
        ((>= (car s) x) (cons x s))
        (else (cons (car s) (adjoin-set (cdr s) x)))))

;2.62 union of ordered set
(define (union-set s t)
  (cond ((null? s) t)
        ((null? t) s)
        ((< (car s) (car t))
         (cons (car s) (union-set (cdr s) t)))
        ((= (car s) (car t))
         (cons (car s) (union-set (cdr s) (cdr t))))
        (else (cons (car t) (union-set s (cdr t))))))

;huffman trees!
(define (keyed-adjoin-set key-func x s)
  (display "item:")
  (display x)(newline)
  (display "set:")
  (display s)(newline)
  (cond ((null? s) (list x))
        ((>= (key-func (car s)) (key-func x)) (cons x s))
        (else (cons (car s) (keyed-adjoin-set key-func x (cdr s))))))
  
(define (is-leaf? arg)
  (eq? (car arg) 'leaf))
(define (symbol tree)
    (if (is-leaf? tree) (list (cadr tree))
        (caddr tree)))
(define (weight tree)
  (if (is-leaf? tree) (caddr tree)
      (cadddr tree)))
(define (left-branch tree) (car tree))
(define (right-branch tree) (car (cdr tree)))
(define (make-leaf symbol weight)
    (list 'leaf symbol weight))

(define (make-tree left right)
  (display left)
  (list left right
   (append (symbol left) (symbol right))
   (+ (weight left) (weight right))))

(define (make-leaf-set pairs)
    (if (null? pairs) null
        (let ((pair (car pairs)))
          (keyed-adjoin-set weight
                            (make-leaf (car pair) (cadr pair))
                            (make-leaf-set (cdr pairs))))))

(define (decode bits tree cur-branch)
  (define (choose-branch bit branch)
    (cond ((= 0 bit) (left-branch branch))
          ((= 1 bit) (right-branch branch))))
  (if (null? bits) (list)
      (let ((next-branch (choose-branch (car bits) cur-branch)))
        (if (is-leaf? next-branch) 
            (cons (symbol next-branch) (decode (cdr bits) tree tree))
            (decode (cdr bits) tree next-branch)))))

(define sample-tree
  (make-tree (make-leaf 'A 4)
             (make-tree (make-leaf 'B 2)
                        (make-tree (make-leaf 'D 1)
                                   (make-leaf 'C 1)))))

;2.67 huffman encoding
(define (encode-symbol s tree)
  (if (is-leaf? tree) null
      (if (element-in-set? s (symbol (left-branch tree)))
          (cons 0 (encode-symbol s (left-branch tree)))
          (cons 1 (encode-symbol s (right-branch tree))))))

(define (encode message tree)
  (if (null? message) null
      (append (encode-symbol (car message) tree)
              (encode (cdr message) tree))))

;2.69 creating huffman trees
(define (generate-huffman-tree pairs)
  (define (successive-merge tree-list)
    (if (null? (cdr tree-list)) (car tree-list)
        (successive-merge
         (keyed-adjoin-set weight
          (make-tree (car tree-list) (cadr tree-list))
          (cddr tree-list)))))
  (successive-merge (make-leaf-set pairs)))

;(let ((pairs `((A 3) (B 4) (C 4) (D 1) (E 5) (F 2) (G 3)))
;     (bits `(1 1 1 1 1 1 1 0 0 1)))
;  (define tree (generate-huffman-tree pairs))
;  (decode (encode '(C A B) tree) tree tree))

;delete binding in alist
(define attach-type cons)
(define get-tag car)
(define get-contents cadr)

(define (del-assq key alist)
  (if (eq? (caar alist) key) (cdr alist)
      (cons (car alist) (del-assq key (cdr alist)))))

(define (put fun-table op type fun)
  (let ((op-table (let ((op-in-table (assq op fun-table)))
                    (if op-in-table (cdr op-in-table) #f))))
    (if op-table
        (cons (cons op (cons (list type fun) op-table))
              (del-assq op fun-table))
        (cons (cons op (cons (list type fun) '())) fun-table))))

(define (get fun-table op type)
  (let ((op-table (assq op fun-table)))
    (if op-table
        (let ((type-pair (assq type (cdr op-table))))
          (if type-pair (cadr type-pair) #f))
        #f)))

(define (apply-generic fun-table op . args)
  (let ((arg-types (map get-tag args)))
    (let ((fun (get fun-table op arg-types)))
      (if fun (apply fun (map get-contents args)) #f))))

;2.73a: we associated operators with functions that perform the derivation
;rule for that particular operator and put this in a table via put so that
;it is abstracted away from the derivation function

;2.73b
(define (make-derivator fun-table)
  (define constant? number?)
  (define variable? symbol?)
  (define same-variable? eq?)
  (define (deriv exp var)
    (define operator car)
    (define operands cdr)
    (cond ((constant? exp) 0)
          ((variable? exp) (if (same-variable? exp var) 1 0))
          (else ((get fun-table 'deriv (operator exp)) deriv (operands exp) var))))
  deriv)

(define (make-sum a1 a2) 
  (cond ((and (number? a1) (number? a2)) (+ a1 a2))
        ((eq? a1 0) a2)
        ((eq? a2 0) a1)
        (else (list '+ a1 a2))))

(define (make-product a1 a2)
  (cond ((and (number? a1) (number? a2)) (* a1 a2))
        ((or (eq? a1 0) (eq? a2 0)) 0)
        ((eq? a1 1) a2)
        ((eq? a2 1) a1)
        (else (list '* a1 a2))))

;operators must have a define 'derivator' param to enable derivation
;operations on operand (need even if no derivation performed)
(define (add-deriv derivator exp var)
  (make-sum (derivator (car exp) var)
            (derivator (cadr exp) var)))

(define (mult-deriv derivator exp var)
  (make-sum
   (make-product (car exp)
                 (derivator (cadr exp) var))
   (make-product (derivator (car exp) var)
                 (cadr exp))))

;just a sample op table!
(define op-table
  (foldl (lambda (op table)
           (put table (car op) (cadr op) (caddr op)))
         '()
         (list (list 'deriv '+ add-deriv) (list 'deriv '* mult-deriv))))

;2.73d: very little change would actually be needed. We would simply
;need to switch the order of the parameters in our "put" call

;2.76: new types often: message passing or data-directed
;new operations often: data-directed. Data directed can handle both well
;because of its table, which can dynamically accomodate the addition
;of either new types and/or new operations. In message-passing,
;adding a new operation will force you to update all types to handle
;said operation.

;2.77; essentially the "magnitude" function is not in the table as an op
;so it must be put there, as alyssa does. all the functions it invokes
;(i.e. could possibly invoke) must also be put in the table. apply-generic
;will be invoked twice if the complex number is in angular representation,
;while it will be invoked once if the complex number is in rectangular

;2.81a: we will get an error if we attempt to call exp with two complex
;numbers as we cannot coerce complex numbers down to integers
;2.81b: Louis was wrong as all possible operations for a type are defined
;when both arguments are of that type

;2.82: attempting to coerce all types in this manner will simply coerce
;them into the type that is highest in the hierarcy. however, if we are
;attempting to do an operation that exists below this type, then it will
;not work e.g. all args are coerced to complex values but we try a
;rational operation

(define (apply-generic2 fun-table coerce-table op . args)
  (let ((arg-types (map get-tag args)))
    (let ((fun (get fun-table op arg-types)))
      (if fun (apply fun (map get-contents args))
          (if (= (length args) 2)
              (let ((arg1 (car args))
                    (type1 (get-tag (car args)))
                    (arg2 (cadr args))
                    (type2 (get-tag (cadr args))))
                (let ((t1->t2 (get coerce-table type1 type2))
                      (t2->t1 (get coerce-table type2 type1)))
                  (cond (t1->t2
                         (apply-generic2 fun-table coerce-table op (t1->t2 arg1) arg2))
                        (t2->t1
                         (apply-generic2 fun-table coerce-table op arg1 (t2->t1 arg2)))
                        (else (error "not a valid intertype operation")))))
              (error "only defined for binary operations"))))))