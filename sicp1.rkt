#lang racket

;newton's method
(define (abs x)
  (cond ((< x 0) (- x))
        (else x)))
(define (avg x y) (/ (+ x y) 2))
(define (sq x) (* x x))
(define (good-enough x y)
  (cond ((< (abs (- x y)) 0.0001) true)
        (else false)))
;recurse the avg of x and x/g until it is good enough
(define (sqrt-guess x g)
  (if (good-enough g (/ x g)) g
      (sqrt-guess x (avg g (/ x g)))))
(define (sqrt x) (sqrt-guess x 1))

;1.6 defining a new if for the sqrt function
;given Lisp's applicative order, every argument to a function
;is evaluated before it is passed to the function. Since the
;method is recursive, even when it has reached its base case,
;it will keep evaluating (calling) itself even though it doesn't 
;need to anymore. It is clear that the native if statement
;accounts for this infinite recursion in some fashion
;in order to terminate the computation when necessary.

;1.7 the good-enough approximation is best for inputs that are close
;in magnitude to the constant that is hard coded in. For large inputs,
;the method will do more unnecessary work. Approximations for very
;small inputs will be less accuarate, since any guesses will already
;be "good enough", especially for inputs that are the same magnitude
;or less in magnitude than the constant.
(define (sqrt-guess2 x g old-g)
  (if (good-enough old-g g) g
      (sqrt-guess x (avg g (/ x g)) g)))
(define (sqrt2 x) (sqrt-guess x 1 2))

;1.8 a cube root implementation
(define (cube-guess x g old-g)
  (if (good-enough old-g g) g
      (cube-guess x (/ (+ (/ x (sq g)) (* 2 g)) 3) g)))
(define (cubert x) (cube-guess x 1 2))

;1.9
;the first function is iterative (tail-recursive)
;the second is recursive

;1.11
(define (exp base power)
  (define (exp-inner running power)
    (if (= power 0) running
        (exp-inner (* running base) (- power 1))))
  (exp-inner 1 power))
(define (recurse-f n)
  (if (< n 3) n
      (+ (recurse-f (- n 1)) (* (recurse-f (- n 2)) 2) (* (recurse-f (- n 3)) 3))))
(define (iterate-f n)
  (define (inner n1 n2 n3 counter)
    (if (= counter 0) n1
        (inner n2 n3 (+ n3 (* n2 2) (* n1 3)) (- counter 1))))
  (inner 0 1 2 n))

(define (iter-fibo n)
  (define (inner a b counter)
    (if (= counter n) b
        (inner b (+ a b) (+ 1 counter))))
  (inner 0 1 1))

;pascal's
(define (pascal n k)
  (cond ((or (< k 0) (and (> k n))) 0)
        ((and (= k 0) (= n 0)) 1)
        (else (+ (pascal (- n 1) (- k 1)) (pascal (- n 1) k)))))

;1.16 O(log n) exponentiation
(define (log-exp base power)
  (define (inner base power a)
    (cond ((= power 0) a)
          ((not (= (remainder power 2) 0)) (inner base (- power 1) (* base a)))
          (else (inner (sq base) (/ power 2) a))))
  (inner base power 1))

;O(log n) multiplier
(define (double x) (+ x x))
(define (log-multiply base power)
  (define (inner base power a)
    (cond ((= power 0) a)
          ((not (= (remainder power 2) 0)) (inner base (- power 1) (+ base a)))
          (else (inner (double base) (/ power 2) a))))
  (inner base power 0))

;1.21 smallest divisors
(define (smallest-div n)
  (define (next-div div)
    (if (= div 2) 3
        (+ div 2)))
  (define (inner n div)
    (cond ((> (sq div) n) n)
          ((= (remainder n div) 0) div)
          (else (inner n (next-div div)))))
  (inner n 2))
(define (prime? n)
  (= (smallest-div n) n))

;1.22: unfortunately racket does not implement the 
;(runtime) primitive
(define (prime-finder number start)
   (if (prime? start) start
       (prime-finder (+ start 1))))
(define (fermat a n)
  (= (remainder (log-exp a n) n) a))
(define (fast-prime? n times)
  (define (inner a times)
    (cond ((not (fermat a n)) false)
          ((= times 1) true)
          (else (fast-prime? n (- times 1)))))
  (inner (random n) times))

;1.23 + 1.24
;term combination: abstraction of summing or 
;multiplying a bunch of terms
(define (id-func x) x)
(define (1+ x) (+ 1 x))
(define (accumulate comb identity f next a b)
  (if (> a b) 0
      (comb (f a) (accumulate comb identity f next (next a) b))))
(define (accumulate-iter comb identity f next a b)
  (define (inner acc a)
    (if (> a b) acc
        (inner (comb acc (f a)) (next a))))
  (inner identity a))
(define (sum f next a b)
  (accumulate-iter + 0 f next a b))
(define (simpsons f a b n)
  (define (inner i acc h)
    (cond ((> i n) (* (/ h 3) acc))
          ((or (= i n) (= i 0)) (inner (+ i 1) (+ acc (f (+ a (* i h)))) h))
          ((= (remainder i 2) 0) (inner (+ i 1) (+ acc (* 4 (f (+ a (* i h))))) h))
          (else (inner (+ i 1) (+ acc (* 2 (f (+ a (* i h))))) h))))
  (inner 0 0 (/ (- b a) n)))
;(simpsons (lambda (x) (* 2 x)) 5 10 100)

;1.25
(define (product f next a b)
  (accumulate-iter * 1 f next a b))
(define (factorial n)
  (product id-func 1+ 1 n))

;1.27
(define (filter-acc predicate comb identity f next a b)
  (define (inner acc a)
    (cond ((> a b) acc)
          ((predicate a) (inner (comb acc (f a)) (next a)))
          (else (inner acc (next a)))))
  (inner 0 identity))
(define (sum-prime a b)
  ;must set identity to 1 so (random identity) can be called
  ;on the first iteration without violating random's contract
  (- (filter-acc (lambda (x) (fast-prime? x 10)) + 1 id-func 1+ a b) 1))
;(sum-prime 2 10)

;number of primes from 2 to n
(define (num-primes n)
  (- (filter-acc (lambda (x) (fast-prime? x 10)) + 1 (lambda (x) 1) 1+ 2 n) 1))

;euclid's gcd algorithm
(define (gcd a b)
  (if (= b 0) a
      (gcd b (remainder a b))))

;euler's totient function
(define (euler n)
  (- (filter-acc (lambda (x) (gcd x n)) + 1 (lambda (x) 1) 1+ 1 n) 1))
;(euler 17)

(define (close-enough? a b)
  (< (abs (- a b)) 0.0000001))

;O(logn) root finder for function f in the
;interval [a,b] (constraint: f(a) and f(b) must not
;be the same sign - one must be positive, the other negative
(define (root f a b)
  (define (search a b)
    (let ((midpt (avg a b)) (f-midpt (f (avg a b))))
      (display b)
      (newline)
      (cond ((close-enough? a b) midpt)
            ((> f-midpt 0) (search a midpt))
            ((< f-midpt 0) (search midpt b))
            (else midpt))))
  (search a b))
;(root (lambda (x) (- (* x x) 3)) 1 2)
;(sqrt 3)

;1.29; f is the function for which we will find the max,
;while n is the number of partitions to be made.
;[a,b] is the interval over which the max will be found
(define (func-max f n a b)
  (define (max a b)
    (if (> a b) a
        b))
  (accumulate-iter max 1 f (lambda (x) (+ x (/ (- b a) n))) a b))

;1.31
(define (fixed-point f x)
  (if (close-enough? (f x) x) x
      (fixed-point f (f x))))
;(fixed-point cos 1)

;1.32
(define (n-apply f x n)
  (if (= n 1) (f x)
      (n-apply f (f x) (- n 1))))
;(n-apply sq 5 2)

;1.33
(define (smooth f)
  (let ((dx 0.001))
  (lambda (x)
    (/ (+ (f (- x dx)) (f x) (f (+ x dx))) 3))))
(define (n-smooth f n)
  (n-apply smooth f n))
;((n-smooth (lambda (x) (/ (sin x) x)) 10) 3.14)

;Newton's method for calculating roots
(define (derive f)
  (let ((dx 0.001))
    (lambda (x) (/ (- (f (+ x dx)) (f x)) dx))))
(define (newton f)
  (define (improve f guess)
    (- guess (/ (f guess) ((derive f) guess))))
  (define (inner f guess)
    (if (close-enough? 0 (f guess)) guess
        (inner f (improve f guess))))
  (inner f 1))
;(newton (lambda (x) (sq x)))

;1.34
(define (cubic a b c)
  (newton (lambda (x) (+ (* x x x) (* a (sq x)) (* b x) c))))

(define (xor a b)
  (cond ((and a b) false)  ;1 1
        ((and a (not b)) true) ;1 0
        ((and (not a) b) true) ;0 1
        ((and (not a) (not b))))) ;0 0

;rational number arithmetic
(define (make-rat n d)
  (cons (* (/ (abs n) (gcd (abs n) (abs d)))
           (if (xor (< n 0) (< d 0)) -1
               1))
        (/ (abs d) (gcd (abs n) (abs d)))))
(define (numer rat-num)
  (car rat-num))
(define (denom rat-num)
  (cdr rat-num))

;2d point representation
(define (make-point x y)
  (cons x y))
(define (get-x point)
  (car point))
(define (get-y point)
  (cdr point))
(define (make-segment startpoint endpoint)
  (cons startpoint endpoint))
(define (get-start segment)
  (car segment))
(define (get-end segment)
  (cdr segment))
(define (midpoint segment)
  (cons (avg (get-x (get-start segment)) (get-x (get-end segment)))
        (avg (get-y (get-start segment)) (get-y (get-end segment)))))

;2.4 alt cons/car/cdr
;x and y can be any pair of relatively prime numbers
(define x 37)
(define y 29)
(define xy (* x y))
(define (alt-cons a b)
  (* (exp x a) (exp y b)))
(define (alt-car pair)
  (define (countx pair n)
    (if (= pair 1) n
        (countx (/ pair x) (+ n 1))))
  (define (inner pair n)
    (if (= (remainder pair xy) 0) (inner (/ pair xy) (+ n 1))
        (if (= (remainder pair y) 0) n   ;n = a
            (+ n (countx pair 0)))))     ;n = b
  (inner pair 0))
(define (alt-cdr pair)
  (define (county pair n)
    (if (= pair 1) n
        (county (/ pair y) (+ n 1))))
  (define (inner pair n)
    (if (= (remainder pair xy) 0) (inner (/ pair xy) (+ n 1))
        (if (= (remainder pair y) 0) (+ n (county pair 0))  ;n = a
            n)))     ;n = b
  (inner pair 0))
;(alt-cdr (alt-cons 3 2))

;2.5 Church numerals
;zero returns a function that returns a function
(define zero (lambda (f) (lambda (x) x)))
(define (increment n)
  (lambda (f) (lambda (x) (f ((n f) x)))))

;2.6 interval arithmetic system
(define (make-int lower upper)
  (cons lower upper))
(define (lower-bound i)
  (car i))
(define (upper-bound i)
  (cdr i))

;2.16
(define (last l)
  (if (null? (cdr l)) (car l)
      (last (cdr l))))
;(last (list 1 2 3 4 5 6 7 8 9))

;2.17
(define (reverse l)
  (define (inner sublist acc)
    (if (null? sublist) acc
        (inner (cdr sublist) (cons (car sublist) acc))))
  (inner l (list)))
;(reverse (list 1 2 3 4 5))

;2.18 is trivial, so here is 2.19
;The answer comes out in reverse order because the accumulation
;list that contains the answer can only be cons'd to, which is an
;operation that only prepends to the list. Switching the arguments
;cons doesn't quite work, as it produces a nested list.

;2.20 - recursive implementation of map
(define (map operation list)
  (if (null? list) null
      (cons (operation (car list)) (map operation (cdr list)))))
;(map (lambda (x) (+ 1 x)) (list 1 2 3 4))

;2.21 - number of ways to change n with a list of coins
;the number produced by cc will vary if the order of coins
;is changed. When returning 0 for the value of n when n < (car coins),
;we are making the assumption that (car coins) is the smallest
;denomination still in the list, which is only true for the entire
;process if coins was sorted to begin with. If they are out of order,
;this assumption fails at some point in the process, which will
;make cc return an inaccurate result
(define (cc n coins)
  (cond ((null? coins) 0)
        ((= n 0) 1) ;successful changing
        ((< n (car coins)) 0) ;smallest coin is larger than n
        (else (+ (cc (- n (car coins)) coins)
                 (cc n (cdr coins))))))

;definition for atom? since it doesn't exist in Racket :(
(define (atom? a)
  (if (with-handlers ([exn:fail? (lambda (v) #f)])
        (car a)) #f #t))

;count atomic elements in a list
(define (countatoms l)
  (cond ((null? l) 0) 
        ((atom? l) 1)
        (else (+ (countatoms (car l)) (countatoms (cdr l))))))
;(countatoms (list 1 2 3 (list 1 2 3 4)))

;2.25
(define (deep-reverse l)
  (define (inner sublist acc)
    (cond ((null? sublist) acc)
          ((atom? (car sublist))
           (inner (cdr sublist) (cons (car sublist) acc)))
          (else
           (inner (cdr sublist) (cons (deep-reverse (car sublist)) acc)))))
    (inner l (list)))
;(deep-reverse (list 1 2 3 (list 4 5) (list 6 (list 7 8 9) 10)))

;append two lists together
(define (append x y)
  (if (null? x) y
      (cons (car x) (append (cdr x) y))))

;2.26 - return the leaves of a tree
(define (fringe l)
  (define (inner sublist acc)
    (cond ((null? sublist) acc)
          ((atom? (car sublist))
           (inner (cdr sublist) (cons (car sublist) acc)))
          (else
           (inner (cdr sublist) (append (fringe (car sublist)) acc)))))
  (inner l (list)))
;(fringe (list 1 2 3 (list 4 5) (list 6 (list 7 8 9) 10)))

;2.27
(define (mobile t)
  (define (make-mobile left-branch right-branch)
    (cons left-branch right-branch))
  (define left-branch car)
  (define right-branch cdr)
  (define (make-branch length structure)
    (cons length structure))
  (define length car)
  (define structure cdr)
  (define (total-weight t)
    (cond ((null? t) 0)
          ((atom? t) t)
          (else (let ((left (if (atom? (left-branch t)) (left-branch t)
                                (total-weight (structure (left-branch t)))))
                      (right (if (atom? (right-branch t)) (right-branch t)
                                 (total-weight (structure (right-branch t))))))
                  (+ left right)))))
  (define (balanced? t)
    (if (atom? t) #t
        (let ((left (left-branch t))
              (right (right-branch t)))
          (if (= (* (length left) (total-weight (structure left)))
                 (* (length right) (total-weight (structure right))))
              (and (balanced? (structure left)) (balanced? (structure right)))
              #f))))
  t)
;(let ((a (make-mobile (make-branch 3 (make-mobile (make-branch 6 2) (make-branch 6 2))) 
 ;                     (make-branch 3 (make-mobile (make-branch 6 2) (make-branch 6 2))))))
 ; (balanced? a))

;2.31 - symbolic differentiator
(define (deriv exp var)
  (define (constant? exp) (number? exp))
  (define (variable? exp) (symbol? exp))
  (define (same-variable? v1 v2)
    (and (variable? v1) (variable? v2)
         (eq? v1 v2)))
  ;operation checks
  (define (operator-check operator)
    (lambda (x)
      (if (not (atom? exp)) (eq? (car exp) operator)
        #f)))
  (define sum? (operator-check '+))
  (define product? (operator-check '*))
  (define exponentation? (operator-check '**))
  ;expression selectors
  (define (addend exp) (car (cdr exp)))
  (define (augend exp) (car (cdr (cdr exp))))
  (define (multiplier exp) (car (cdr exp)))
  (define (multiplicand exp) (car (cdr (cdr exp))))
  (define (base exp) (car (cdr exp)))
  (define (exponent exp) (car (cdr (cdr exp))))
  ;expression creators
  ;checks is a lambda; return #f if no simplification is done
  ;and return a single atomic element if there is simplification
  (define (make-expression operator checks)
    (lambda (x y) 
      (let ((simplify (checks x y)))
        (if simplify simplify
            (list operator x y)))))
  (define make-sum 
    (let ((checks (lambda (x y)
                    (cond ((and (number? x) (= x 0)) y)
                          ((and (number? y) (= y 0)) x)
                          (else #f)))))
           (make-expression '+ checks)))
  (define make-product
    (let ((checks (lambda (x y)
                    (cond ((and (number? x) (= x 1)) y)
                          ((and (number? y) (= y 1)) x)
                          ((and (number? x) (= x 0)) 0)
                          ((and (number? y) (= y 0)) 0)
                          ((and (number? x) (product? y))
                           (cond ((number? (multiplier y))
                                  (list '* (* x (multiplier y)) (multiplicand y)))
                                 ((number? (multiplicand y))
                                  (list '* (* x (multiplicand y)) (multiplier y)))
                                 (else #f)))
                          ((and (number? y) (product? x))
                           (cond ((number? (multiplier x))
                                  (list '* (* y (multiplier x)) (multiplicand x)))
                                 ((number? (multiplicand x))
                                  (list '* (* y (multiplicand x)) (multiplier x)))
                                 (else #f)))
                          (else #f)))))
           (make-expression '* checks)))
  ;only supports numerical exponents
  (define make-exponentation
    (let ((checks (lambda (x y)
                    (cond ((and (number? x) (= y 1)) x)
                          ((and (number? y) (= y 0)) 1)
                          (else #f)))))
           (make-expression '** checks)))
  ;differentiation algorithm
  (cond ((constant? exp) 0)
        ((variable? exp)
         (if (same-variable? exp var) 1 0))
        ((sum? exp)
         (make-sum (deriv (addend exp) var)
                   (deriv (augend exp) var)))
        ((product? exp)
         (make-sum
          (make-product (multiplier exp) (deriv (multiplicand exp) var))
          (make-product (multiplicand exp) (deriv (multiplier exp) var))))
        ((exponentation? exp)
         (make-product
          (exponent exp)
          (make-exponentation (base exp) (- (exponent exp) 1))))))
;(deriv '(* 4 (** x 5)) 'x)

(define (is-leaf? arg)
  (eq? (car arg) 'leaf))
(define (symbol tree)
    (if (is-leaf? tree) (car (cdr tree))
        (car (cdr (cdr tree)))))
(define (weight tree) 
  (if (is-leaf? tree) (car (cdr (cdr tree)))
      (car (cdr (cdr (cdr tree))))))
(define (left-branch tree) (car tree))
(define (right-branch tree) (car (cdr tree)))
;huffman encoding scheme
(define (huffman symbol-pairs)
  (define (make-leaf symbol weight)
    (list 'leaf symbol weight))
  (define (append-symbol a b)
    (let ((l (if (atom? a) (list a) a))
          (r (if (atom? b) (list b) b)))
      (append l r)))
  (define (make-tree left right)
    (list
     left
     right
     (append-symbol (symbol left) (symbol right))
     (+ (weight left) (weight right))))
  (define (adjoin-set e set)
    (cond ((null? set) (list e))
          ((< (weight e) (weight (car set))) (cons e set))
          (else (cons (car set)
                      (adjoin-set e (cdr set))))))
  ;keep merging the set of leaf nodes until there is only one left
  (define (merge set)
    (let ((left (car set))
          (right (if (null? (cdr set)) (cdr set) 
                     (car (cdr set)))))
      (if (null? right) left
          (merge (cons (make-tree left right)
                       (cdr (cdr set)))))))
  ;create the initial set of leaf nodes
  ;leaves is a list of (symbol, weight)
  (define (make-leaf-set leaves)
    (if (null? leaves) (list)
        (let ((leaf (car leaves)))
          (adjoin-set (make-leaf (car leaf) (car (cdr leaf)))
                      (make-leaf-set (cdr leaves))))))
  (merge (make-leaf-set symbol-pairs)))

(define (decode bits tree cur-branch)
  (define (choose-branch bit branch)
    (cond ((= 0 bit) (left-branch branch))
          ((= 1 bit) (right-branch branch))))
  (if (null? bits) (list)
      (let ((next-branch (choose-branch (car bits) cur-branch)))
        (if (is-leaf? next-branch) 
            (cons (symbol next-branch) (decode (cdr bits) tree tree))
            (decode (cdr bits) tree next-branch)))))

(let ((pairs `((A 3) (B 4) (C 4) (D 1) (E 5) (F 2) (G 3)))
      (bits `(1 1 1 1 1 1 1 0 0 1)))
  (define tree (huffman pairs))
  (decode bits tree tree))
  
;2.43
;most frequent: 1 bit. least frequent: N-1 bits
  