#lang racket
(require scheme/mpair)

;helpers
(define (adjoin-set s x)
  (cond ((null? s) (list x))
        ((>= (car s) x) (cons x s))
        (else (cons (car s) (adjoin-set (cdr s) x)))))

(define (element-in-set? e set)
  (cond ((null? set) #f)
        ((eq? (car set) e) #t)
        (else (element-in-set? e (cdr set)))))

;3.1
(define (make-accumulator initial)
  (lambda (x)
    (begin
      (set! initial (+ initial x))
      initial)))

;3.2 lol efix counter
(define (fun-counter f)
  (define count 0)
  (lambda (x)
    (cond ((eq? x 'how-many-calls?) count)
          ((eq? x 'reset-count)
           (begin (set! count 0) count))
          (else (begin
                  (set! count (+ count 1))
                  (f x))))))

;3.3 totally secure banking application
(define (make-account initial password)
  (define incorrect-times 0)
  (define (monitor-fraud)
    (let ((incorrect-limit 7))
      (begin (set! incorrect-times (+ incorrect-times 1))
             (if (>= incorrect-times incorrect-limit)
                 "cops comin'"
                 "get lost nub"))))
  (define (withdraw x)
    (if (>= initial x)
        (begin (set! initial (- initial x)) initial)
        "insufficient funds"))
  (define (deposit x)
    (begin (set! initial (+ initial x)) initial))
  (lambda (op x pass)
    (if (eq? pass password)
        (cond ((eq? op 'withdraw) (withdraw x))
              ((eq? op 'deposit) (deposit x))
              (else "undefined method"))
        (monitor-fraud))))

;3.4 integration via monte carlo trials
(define (monte-carlo trials experiment)
  (define (inner successes trials-left)
    (if (= trials-left 0) (/ successes trials)
        (inner (+ successes (if (experiment) 1 0)) (- trials-left 1))))
  (inner 0 trials))

(define (gcd a b)
  (if (= b 0) a (gcd b (remainder a b))))

(define (monte-carlo-integration trials pred x1 y1 x2 y2)
  (define width (abs (- x2 x1)))
  (define height (abs (- y2 y1)))
  (define (experiment)
    (let ((x (+ (min x1 x2) (random width)))
          (y (+ (min y1 y2) (random height))))
      (pred x y)))
  (* (monte-carlo trials experiment) (* width height)))

(define (approximate-pi trials)
  (define (unit-circle x y)
    (<= (+ (* x x) (* y y)) 1))
  (monte-carlo-integration trials unit-circle -1 -1 1 1))

;3.7 joint accounts
(define (make-joint-account acct pass newpass)
  (define (shared-acct op x newpassarg)
    (if (eq? newpassarg newpass) (acct op x pass)
        "get lost nub"))
  (if (number? (acct 'withdraw 0 pass)) shared-acct
      "get lost nub"))

;3.17 correctly counting number of (distinct) pairs
(define (count-pairs t)
  (define pair-set '())
  (define (loop subt)
    (if (not (pair? subt)) 0
          (let ((car-count 
                 (if (element-in-set? (car subt) pair-set) 0
                     (begin
                       (set! pair-set (cons (car subt) pair-set))
                       (loop (car subt)))))
                (cdr-count
                 (if (element-in-set? (cdr subt) pair-set) 0
                     (begin
                       (set! pair-set (cons (cdr subt) pair-set))
                       (loop (cdr subt))))))
            (+ 1 car-count cdr-count))))
  (loop t))

;3.18 & 3.19: finding a cycle in a linked list
;idea: have a slow and a fast pointer, check if fast ptr has passed slow
(define (cyclic-list? l)
  (define (inner i fast slow)
    (cond ((null? fast) #f)
          ((eq? (car fast) (car slow)) #t)
          ((= (remainder i 2) 0)
           (inner (+ i 1) (cdr fast) (cdr slow)))
          (else
           (inner (+ i 1) (cdr fast) slow))))
  (inner 0 (cdr l) l))

;3.22
(define (make-queue)
  (let ((front-ptr (mlist))
        (rear-ptr (mlist)))
    (define (empty-queue?) (null? front-ptr))
    (define (push e)
      (let ((el-pair (mcons e (mlist))))
        (if (empty-queue?)
            (begin
              (set! front-ptr el-pair)
              (set! rear-ptr el-pair))
            (begin
              (set-mcdr! rear-ptr el-pair)
              (set! rear-ptr el-pair)))))
    (define (pop)
      (if (empty-queue?) (mlist)
          (let ((el front-ptr))
            (set! front-ptr (mcdr front-ptr))
            (mcar el))))
    (lambda (op . args)
      (cond ((eq? op 'pop) (pop))
            ((eq? op 'push) (push (car args)))
            ((eq? op 'empty?) (empty-queue?))))))
      
;3.24 association lists/tables
;pred is a predicate used for key equality
(define (make-table pred)
  (list (list '*table* pred)))

(define get-pred cadar)

(define (is-table? t)
  (eq? (caar t) '*table*))

(define (assoc table key)
  (define (inner pred table)
    (cond ((null? table) #f)
          ((pred (caar table) key) (car table))
          (else (inner pred (cdr table)))))
  (inner (get-pred table) (cdr table)))

(define (lookup table key)
  (let ((pair (assoc key table)))
    (if pair (cadr pair) #f)))

(define (insert table value key)
  (define (inner pred table)
    (cond ((null? table) (cons (list key value) table))
          ((pred (caar table) key)
           (cons (list key value) (cdr table)))
          (else 
           (cons (car table) (inner pred (cdr table))))))
  (inner (get-pred table) table))

;generalized n-dimensional table, for key lists of all lengths
(define make-n-table make-table)

(define (lookup-n table keys)
  (define (foldf key acc)
    (if (not acc) #f
        (let ((next-tbl (assoc acc key)))
          (if next-tbl (cadr next-tbl) #f))))
  (foldl foldf table keys))
 
(define (insert-n table value keys)
  (define (foldf record acc)
    (display record)
    (newline)
    (display (cadr record))
    (if ((get-pred table) (car record) (car keys))
        (cons (cons (car record) 
                    (list (insert-n (cadr record) value (cdr keys)))) 
              acc)
        (cons record acc)))
  (if (null? (cdr keys)) (insert table value (car keys))
      (cons (car table) (foldl foldf '() (cdr table)))))

;test tables!
(define t3 (insert (make-table eq?) 5 'c))
(define t2 (insert (make-table eq?) t3 'b))
(define t1 (insert (make-table eq?) t2 'a))
(define t0 (insert-n t1 10 (list 'a 'b 'd)))

;streamssss
(define ones (stream-cons 1 ones))
(define twos (stream-cons 2 twos))

(define (stream-map-n f . streams)
  (if (stream-empty? (stream-first streams)) empty-stream
      (stream-cons 
       (apply f (map stream-first streams))
       (apply stream-map-n (cons f (map stream-rest streams))))))

(define (add-streams s1 s2)
  (stream-map-n + s1 s2))

(define (mult-streams s1 s2)
  (stream-map-n * s1 s2))

(define (div-streams s1 s2)
  (stream-map-n / s1 s2))

(define integers (stream-cons 1 (add-streams ones integers)))

;3.54
(define factorial (stream-cons 1 (mult-streams integers factorial)))

;3.55
(define (partial-sums s)
  (stream-cons (stream-first s)
               (add-streams (stream-rest s)
                            (partial-sums s))))

(define (merge s1 s2)
  (cond ((stream-empty? s1) s2)
        ((stream-empty? s2) s1)
        (else
         (let ((s1first (stream-first s1))
               (s2first (stream-first s2)))
           (cond ((< s1first s2first)
                  (stream-cons s1first (merge (stream-rest s1) s2)))
                 ((< s2first s1first)
                  (stream-cons s2first (merge (stream-rest s2) s1)))
                 (else
                  (stream-cons s1first
                               (merge (stream-rest s1)
                                      (stream-rest s2)))))))))

(define (scale-stream s c)
  (stream-map (lambda (x) (* x c)) s))

;3.56
(define S 
  (stream-cons 1
               (merge (merge (scale-stream S 2)
                             (scale-stream S 3))
                      (scale-stream S 5))))

;3.59a
(define (integrate-series s)
  (div-streams s integers))

(define negone (stream-cons -1 negone))
(define cosine-series
  (stream-cons
   1
   (mult-streams negone (integrate-series sin-series))))

(define sin-series
  (stream-cons 1 (integrate-series cosine-series)))

;3.64
(define (stream-limit s tolerance)
  (define (inner val rest)
    (if (< (abs (- val (stream-first rest))) tolerance)
        (stream-first rest)
        (inner (stream-first rest) (stream-rest rest))))
  (inner (stream-first s) (stream-rest s)))

(define (ln2-terms n)
  (stream-cons (/ 1 n)
               (stream-map - (ln2-terms (+ n 1)))))
;3.65 ln 2 estimation
(define ln2
  (stream-cons (stream-first (ln2-terms 1))
               (add-streams (ln2-terms 1) ln2)))

(define (interleave s1 s2)
  (stream-cons (stream-first s1)
               (interleave s2 (stream-rest s1))))

;3.69
(define (pairs s t)
  (stream-cons
   (list (stream-first s) (stream-first t))
   (interleave
    (stream-map (lambda (x) (list (stream-first s) x))
                (stream-rest t))
    (pairs (stream-rest s) (stream-rest t)))))

(define (triples s t u)
  (stream-cons
   (list (stream-first s) (stream-first t) (stream-first u))
   (interleave
    (stream-map (lambda (l) (cons (stream-first s) l))
                (pairs (stream-rest t) (stream-rest u)))
    (triples (stream-rest s) (stream-rest t) (stream-rest u)))))

(define pythagorean-triples
  (stream-filter
   (lambda (l) (and (<= (car l)(cadr l))
                    (= (+ (* (car l) (car l))
                          (* (cadr l) (cadr l)))
                       (* (caddr l) (caddr l)))))
   (triples integers integers integers)))

;3.70
;the cmp function must return -1, 0, or 1, per convention
(define (weighted-merge cmp s1 s2)
  (cond ((stream-empty? s1) s2)
        ((stream-empty? s2) s1)
        (else
         (let ((s1first (stream-first s1))
               (s2first (stream-first s2)))
           (cond ((= (cmp s1first s2first) 1)
                  (stream-cons s1first 
                               (weighted-merge cmp (stream-rest s1) s2)))
                 ((= (cmp s2first s1first) -1)
                  (stream-cons s2first 
                               (weighted-merge cmp (stream-rest s2) s1)))
                 (else
                  (stream-cons s1first
                               (weighted-merge cmp 
                                               (stream-rest s1)
                                               (stream-rest s2)))))))))

(define (pairs2 s t)
  (stream-cons
   (list (stream-first s) (stream-first t))
   (interleave
    (interleave
     (stream-map (lambda (x) (list (stream-first s) x))
                 (stream-rest t))
     (stream-map (lambda (x) (list x (stream-first t)))
                 (stream-rest s)))
    (pairs2 (stream-rest s) (stream-rest t)))))
   
(define (weighted-pairs cmp s t)
  (stream-cons
   (list (stream-first s) (stream-first t))
   (weighted-merge cmp
    (weighted-merge cmp
     (stream-map (lambda (x) (list (stream-first s) x))
                 (stream-rest t))
     (stream-map (lambda (x) (list x (stream-first t)))
                 (stream-rest s)))
    (weighted-pairs cmp (stream-rest s) (stream-rest t)))))
     
(define i-plus-j
  (weighted-pairs
   (lambda (p1 p2)
     (cond ((> (+ (car p1) (cadr p1))
               (+ (car p2) (cadr p2))) 1)
           ((< (+ (car p1) (cadr p1))
               (+ (car p2) (cadr p2))) -1)
           (else 0)))
   integers
   integers))

(define (twothreefive-sum p)
  (+ (* 2 (car p)) (* 3 (cadr p)) (* 5 (car p) (cadr p))))

;returns true if x is divisible by all y in l
(define (divisible-by x l)
  (foldl (lambda (acc b) (if (not acc) #f acc)) #t 
          (map (lambda (y) (remainder x y)) l)))

(define twothreefive
  (stream-filter
   (lambda (p)
     (and (divisible-by (car p) (list 2 3 5))
          (divisible-by (cadr p) (list 2 3 5))))
   (weighted-pairs
    (lambda (p1 p2)
      (cond ((> (twothreefive-sum p1) (twothreefive-sum p2)) 1)
            ((< (twothreefive-sum p1) (twothreefive-sum p2)) -1)
            (else 0)))
    integers integers)))

;3.81 - rand generator stream
;idea: carry w/ the stream at all times the value of the seed so that the
;stream of random numbers is able to be reset at any point; also carry
;the i in the stream so that the next number is able to be generated.
;this way the random number stream should really look like (seed, i, num),
;where num is the ith random number in the stream....
;this looks convoluted (it kinda is tbh) but this is supremely elegant
;if you imagine that what this function returns you is a STREAM of
;random numbers, seeded by seed and generating the next element
;via the rand-update function
(define (random-stream seed rand-update input-stream)
  (define random-numbers
    (stream-cons 
     (list 87 0 87)
     (stream-map 
      (lambda (triple)
        (list (car triple) (+ (cadr triple) 1) (rand-update (caddr triple))))
      random-numbers)))
  ;give inner a list of ((seed i num) (input-stream))
  ;which then gets mapped as the cdr part of the cons
  ;the map transforms the data into what you need
  (define (inner dbl-trpl)
    (stream-cons
     (list (car dbl-trpl) (stream-first (cadr dbl-trpl)))
     (stream-map
      (lambda (dbl-trpl)
        (let ((next-trpl
               (cond ((eq? (cadr dbl-trpl) 'next) 
                      (stream-ref random-numbers (+ (cadar dbl-trpl) 1)))
                     ((eq? (cadr dbl-trpl) 'reset) 
                      (stream-ref random-numbers 0)))))
          (list next-trpl (cadr dbl-trpl))))
      (inner (list (car dbl-trpl) (stream-rest input-stream))))))
  (let ((raw-out (inner (list (stream-ref random-numbers 0) input-stream))))
    (stream-map (lambda (dbl-trpl) (caddar dbl-trpl)) raw-out)))

(define nexts (stream-cons 'next nexts))
(define resets (stream-cons 'reset resets))
(define (update15 n)
  (remainder (* n 15) 37))
(define input
  (interleave
   (interleave
    (interleave nexts resets)
    nexts)
   nexts))
(define oscillate (random-stream 92 update15 nexts))

(define (monte-carlo-stream experiment)
  (define inner
    (stream-cons 
     (list 0 0)
     (stream-map
      (lambda (p)
        (if (experiment) 
            (list (+ (car p) 1) (+ 1 (cadr p)))
            (list (car p) (+ 1 (cadr p)))))
      inner)))
  (stream-map
   (lambda (p) (/ (car p) (cadr p)))
   inner))

(define (rand-stream lower upper)
  (stream-map
   (lambda (x) (+ lower (remainder x (- upper lower))))
   (random-stream (random 100) update15 nexts)))

(define (monte-carlo-integration-stream pred x1 y1 x2 y2)
  (define width (abs (- x2 x1)))
  (define height (abs (- y2 y1)))
  (define (experiment)
    (let ((x (+ (min x1 x2) (random width)))
          (y (+ (min y1 y2) (random height))))
      (pred x y)))
  (scale-stream (monte-carlo-stream experiment) (* width height)))

(define (unit-circle x y)
  (<= (+ (* x x) (* y y)) 1))

(define approximate-pi-stream
  (monte-carlo-integration-stream unit-circle -1 -1 1 1))

                 