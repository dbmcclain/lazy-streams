
(defpackage #:lstreams
  (:use #:common-lisp)
  (:nicknames #:lzs)
  (:export
   #:stream-cons
   #:stream-car
   #:stream-cdr
   #:stream-ref
   #:stream-nth
   #:stream-nthcdr
   #:stream-take
   #:stream-drop
   #:stream-empty?
   #:stream-map
   #:stream-filter

   #:within
   #:abserror
   #:relerror
   #:adjerror
   #:accelerate-series
   #:show-accel
   #:snd
   #:euler
   #:integrate
   #:integrate-mp
   #:differentiate

   #:accelerated-integrate
   #:accelerated-integrate-mp
   ))

(in-package #:lstreams)

;; ---------------------------------------------------------------------
;; LAZY Eval
;;
;; Fairly elaborate so that we can accommodate functions that return
;; recursively developed lazy values - i.e., lazy -> lazy -> ... -> value
;;
;; LAZY/FORCE can only accommodate single values, not multiple values.
;; If multiple values are desired, encapsulate them with MULTIPLE-VALUE-LIST and VALUES-LIST

;; internal definitions
#|
(defstruct memo expr)

(defun force-with-continuation (e k)
  (cond ((memo-p e) (funcall (memo-expr e) e k))
        (t          (funcall k e))
        ))

(defun make-lazy-memo (fn)
  (make-memo
   :expr (lambda (e k)
           (funcall fn
                    (lambda (val)
                      (force-with-continuation val
                                               (lambda (v)
                                                 (setf (memo-expr e) (lambda (e k)
                                                                       (declare (ignore e))
                                                                       (funcall k v)))
                                                 (funcall k v))
                                               ))
                    ))
   ))

;; user level interface LAZY/FORCE
(defun force (e)
  (force-with-continuation e #'identity))

(defmacro lazy (e)
  ;; we have to build a lambda closure to caputure escaped var bindings
  (um:with-gensyms (k)
    `(make-lazy-memo (lambda (,k)
                       (funcall ,k ,e))
                     )))
|#

;; ----------------------------------------------------------------------
;; Lazy Stream Operations

(declaim (inline stream-car stream-empty?))

(defmacro stream-cons (hd tl)
  `(cons ,hd (um:lazy ,tl)))
#|
(defmacro stream-cons (hd tl)
  `(cons ,hd (lazy:make ,tl)))
|#

(defun stream-car (s)
  (car s))

(defun stream-cdr (s)
  (um:force (cdr s)))
#|
(defun stream-cdr (s)
  (lazy:force (cdr s)))
|#

(defun stream-empty? (s)
  (null s))

#| |#
(defun stream-ref (s n)
  (if (and (plusp n)
           (not (stream-empty? s)))
      (stream-ref (stream-cdr s) (1- n))
    (stream-car s)
    ))
#| |#
#|
(defun stream-ref (s n)
  (loop for ix of-type fixnum from 0 to n
        for l = s then (stream-cdr l)
        until (stream-empty? l)
        finally (return (stream-car l))
        ))
|#

(defun stream-nth (s n)
  (stream-ref s n))

#| |#
(defun stream-nthcdr (s n)
  (if (and (plusp n)
           (not (stream-empty? s)))
      (stream-nthcdr (stream-cdr s) (1- n))
    s))
#| |#
#|
(defun stream-nthcdr (s n)
  (if (not (plusp n))
      s
    (loop for ix of-type fixnum from 0 below n
          for l = s then (stream-cdr l)
          until (stream-empty? l)
          finally (return (stream-cdr l)))
    ))
|#
  
(defun stream-map (f &rest streams)
  (if (notany #'stream-empty? streams)
      (stream-cons
       (apply f (mapcar #'stream-car streams))
       (apply #'stream-map f (mapcar #'stream-cdr streams)))
    ))

(defun stream-for-each (f s)
  (unless (stream-empty? s)
    (funcall f (stream-car s))
    (stream-for-each f (stream-cdr s))
    ))

(defun stream-filter (pred s)
  (cond ((stream-empty? s) nil)
        ((funcall pred (stream-car s))
         (stream-cons (stream-car s)
                      (stream-filter pred (stream-cdr s))))
        (t (stream-filter pred (stream-cdr s)))
        ))

(defun stream-take (s n &key (start 0))
  (let ((s (stream-nthcdr s start)))
    (loop for ix of-type fixnum from 0 below n
          for l = s then (stream-cdr l)
          until (stream-empty? l)
          collect (stream-car l))))

(defun stream-drop (s n)
  (stream-nthcdr s n))

#|
(defun stream-take (s n)
  (um:with-tail-pure-code
    (labels ((iter (n s ans)
               (if (or (not (plusp n))
                       (stream-empty? (force s)))
                   (nreverse ans)
                 (iter (1- n) (um:lazy (stream-cdr (force s)))
                       (cons (stream-car (force s)) ans)))))
      (iter n s nil))))
|#

(defun display-line (x)
  (terpri)
  (princ x))

(defun display-stream (s)
  (stream-for-each #'display-line s))

;; -------------------------------------------------------
;; Specific Lazy Streams
              
(defun stream-enumerate-interval (low high)
  (if (<= low high)
      (stream-cons low
                   (stream-enumerate-interval (+ low 1) high))
    ))

(defun integers-starting-from (n)
  (stream-cons n (integers-starting-from (+ n 1))))

(defparameter integers (integers-starting-from 1))

(defun divisible? (x y)
  (zerop (rem x y)))

(defparameter no-sevens
  (stream-filter (lambda (x) (not (divisible? x 7))) integers))

(defun fibgen (a b)
  (stream-cons a (fibgen b (+ a b))))

(defparameter fibs (fibgen 0 1))

(defun sieve (s)
  (stream-cons
   (stream-car s)
   (sieve (stream-filter
           (lambda (x)
             (not (divisible? x (stream-car s))))
           (stream-cdr s)))
   ))

(defparameter primes (sieve (integers-starting-from 2)))

;; ---------------------------------------------------
;; Alternate versions

(defparameter ones (stream-cons 1 ones))

(defun add-streams (s1 s2)
  (stream-map #'+ s1 s2))

(defparameter integers2 (stream-cons 1 (add-streams ones integers2)))

(defparameter fibs2
  (stream-cons 0
               (stream-cons 1
                            (add-streams (stream-cdr fibs2)
                                         fibs2))))

(defun scale-stream (s sf)
  (stream-map (lambda (x)
                (* x sf))
              s))

(defparameter double (stream-cons 1 (scale-stream double 2)))

;; -------------------------------------------------------------
;; Computation of Primes by Filtering

(defun square (x)
  (* x x))

(defun prime? (n)
  (labels ((iter (ps)
             (cond ((> (square (stream-car ps)) n) t)
                   ((divisible? n (stream-car ps)) nil)
                   (t (iter (stream-cdr ps))))
             ))
    (iter primes2)))

(defparameter primes2
  (stream-cons
   2
   (stream-filter #'prime? (integers-starting-from 3))))

;; -------------------------------------------------------------
;; Compuation of factorials

(defun mul-streams (s1 s2)
  (stream-map #'* s1 s2))

(defparameter factorials (stream-cons 1 (mul-streams integers factorials)))

;; --------------------------------------------------------
;; Partial Sums of Series

(defun partial-sums (s)
  (stream-cons (stream-car s)
               (partial-sums (add-streams integers (stream-cdr s)))))

(defparameter sums-of-integers (partial-sums integers))

;; -----------------------------------------------------------
;; Conversion of ratios to radix -- successive digits

(defun expand (num den radix)
  (stream-cons
   (floor (* num radix) den)
   (expand (rem (* num radix) den) den radix)))

;; ---------------------------------------------------------
;; Infinite Power Series

(defun integrate-series (s &optional (n 1))
  (stream-cons
   (/ (stream-car s) n)
   (integrate-series (stream-cdr s) (+ n 1))))

(defparameter exp-series (stream-cons 1 (integrate-series exp-series)))
(defparameter cos-series (stream-cons 1 (integrate-series (scale-stream sin-series -1))))
(defparameter sin-series (stream-cons 0 (integrate-series cos-series)))

(defun add-series (s1 s2)
  (add-streams s1 s2))

(defun scale-series (s sf)
  (scale-stream s sf))

(defun mul-series (s1 s2)
  (stream-cons (* (stream-car s1) (stream-car s2))
               (add-series (scale-stream (stream-cdr s2) (stream-car s1))
                           (mul-series (stream-cdr s1) s2))))


(defun invert-unit-series (s)
  (let ((inv nil))
    (setf inv (stream-cons 1 (scale-series (mul-series inv (stream-cdr s)) -1)))
    inv))

(defun div-series (s1 s2)
  (let ((norm (/ (stream-car s2))))
    (mul-series (scale-series s1 norm)
                (invert-unit-series
                 (scale-series s2 norm)))))

(defparameter tan-series (div-series sin-series cos-series))

;; -------------------------------------------------------
;; Successive Newton's iterations for SQRT

(defun average (&rest args)
  (/ (reduce #'+ args) (length args)))

(defun sqrt-improve (guess x)
  (average guess (/ x guess)))

(defun sqrt-stream (x)
  (let ((guesses nil))
    (setf guesses (stream-cons 1.0
                               (stream-map (lambda (guess)
                                             (sqrt-improve guess x))
                                           guesses)))
    guesses))


;; -----------------------------------------------------------
;; Solving differential equations

#|
(defun integral (delayed-integrand initial-value dt)
  (let ((int))
    (setf int (stream-cons initial-value
                           (let ((integrand (force delayed-integrand)))
                             (add-streams (scale-stream integrand dt)
                                          int))))
    int))

(defun solve (f y0 dt)
  (let ((y) (dy))
    (setf y  (integral (um:lazy dy) y0 dt)
          dy (stream-map f y))
    y))
|#

(defun integral (delayed-integrand initial-value dt)
  (let ((int))
    (setf int (stream-cons initial-value
                           (let ((integrand (um:force delayed-integrand)))
                             (add-streams (scale-stream integrand dt)
                                          int))))
    int))

(defun solve (f y0 dt)
  (let ((y) (dy))
    (setf y  (integral (um:lazy dy) y0 dt)
          dy (stream-map f y))
    y))

(defparameter sol (solve (lambda (x) x) 1.0d0 0.001d0))


;; ------------------------------------------------------
(defun easy-diff (f x h)
  (if (zerop x)
      (/ (- (funcall f (/ h 2)) (funcall f (/ (- h) 2))) h)
    (/ (- (funcall f (* x (+ 1 (/ h 2)))) (funcall f (* x (- 1 (/ h 2))))) (* x h))
    ))

(defun halve (x)
  (/ x 2))

(defun repeat (f a)
  (stream-cons a (repeat f (funcall f a))))

(defun differentiate (f x h0)
  (stream-map (lambda (h)
                (easy-diff f x h))
              (repeat #'halve h0)))

(defun integrate (f a b)
  ;; trapezoid rule
  (labels ((integ (a b fa fb)
             (let* ((m  (/ (+ a b) 2))
                    (fm (funcall f m)))
               (stream-cons (/ (* (+ fa fb) (- b a)) 2)
                            (stream-map #'+
                                        (integ a m fa fm)
                                        (integ m b fm fb))
                            ))
             ))
    (integ a b (funcall f a) (funcall f b))
    ))

(defun integrate-mp (f a b)
  ;; mid-point algorithm with interval tripling
  (labels ((integ (a b fm)
             (let* ((dx/3 (/ (- b a) 3))
                    (m1  (+ a dx/3))
                    (m2  (- b dx/3))
                    (fm1 (funcall f (/ (+ a m1) 2)))
                    (fm2 (funcall f (/ (+ m2 b) 2))))
               (stream-cons (* fm (- b a))
                            (stream-map #'+
                                        (integ a m1 fm1)
                                        (integ m1 m2 fm)
                                        (integ m2 b fm2)))
               )))
    (integ a b (funcall f (/ (+ a b) 2)))
    ))

(defun abserror (eps)
  (lambda (a b)
    (<= (abs (- a b)) eps)))

(defun relerror (eps)
  (let ((abse (abserror eps)))
    (lambda (a b)
      (if (zerop b)
          (funcall abse a b)
        (funcall abse (/ a b) 1)))))

(defun adjerror (eps)
  ;; use either abserror if 0 <= (abs val) <= 1
  ;; or relerror if (abs val) > 1
  (let ((abse (abserror eps))
        (rele (relerror eps)))
    (lambda (a b)
      (cond ((<= 0 (max (abs a) (abs b)) 1) (funcall abse a b))
            (t (funcall rele a b)))
      )))
   
(defun within (epsfn stream)
  (let ((a  (stream-ref stream 0))
        (b  (stream-ref stream 1)))
    (if (funcall epsfn a b)
        b
      (within epsfn (stream-cdr stream)))
    ))

(defun sqr (x)
  (* x x))

(defun euler (stream)
  (let* ((a (stream-ref stream 0))
         (b (stream-ref stream 1))
         (c (stream-ref stream 2))
         (den (- (- c b) (- b a)))
         (c-new (if (zerop den)
                    c
                  (- c (/ (sqr (- c b)) den)))))
    (stream-cons c-new (euler (stream-cdr stream)))
    ))

(defun snd (stream)
  (stream-ref stream 1))

(defun accelerate-series (xform stream)
  (stream-map #'snd (repeat xform stream)))

#|
;; Examples
(plt:fplot 'plt '(0 20)
           (lambda (x)
             (within (abserror 1.0d-8)
                     (accelerate-series #'euler
                                        (differentiate #'sin x 0.125)))))

(show-accel 10 (differentiate #'sin 3d0 0.125))

(defun show-derivative (dom fn)
  (plt:fplot 'plt dom
             (lambda (x)
               (within (abserror 1.0d-8)
                       (accelerate-series #'euler
                                          (differentiate fn x 0.125))
                       ))
             ))

|#

(defun accelerated-integrate (f a b &key (eps 1d-8) (errfn #'adjerror))
  (within (funcall errfn eps)
          (accelerate-series #'euler
                             (integrate f a b))))

(defun accelerated-integrate-mp (f a b &key (eps 1d-8) (errfn #'adjerror))
  (within (funcall errfn eps)
          (accelerate-series #'euler
                             (integrate-mp f a b))))

;; -----------------------------------------------------
;; insert spacers in large double-precision printouts so that
;; the digits can be more easily read in groups of 5
;;
(defun insert-spacers (str
                       &key
                       (grouping 5)
                       (spacer #\space)
                       &aux
                       (len (length str))
                       (pos (um:if-let (pos (position #\. str))
                                       (+ pos grouping 1)
                                       len)))
  (if (< pos len)
      (apply #'um:paste-strings spacer
             (subseq str 0 pos)
             (um:group (subseq str pos) grouping))
    str))

(defun format-fraction-with-spacers (stream fmt v
                                            &rest keyargs
                                            &key ;; these are here for documentation purposes
                                            (grouping 5)
                                            (spacer #\space))
  (declare (ignore grouping spacer))
  (let ((str (apply #'insert-spacers (format nil fmt v) keyargs)))
    (if stream
        (princ str stream)
      str)))

(defun fmt-f-grouped (stream val has-colon has-atsign
                             &optional
                             (wid      20)
                             (ndp      16)
                             (grouping  5)
                             (spacer   #\space))
  ;; format is ~W,D,G,C{@}F
  ;; where W is field width for ~F formatting
  ;;       D is nbr of decimal places
  ;;       G is nbr of digits per group following decimal point
  ;;       C is char for group separation
  ;;       @ is optional flag for explicit leading sign ({x} ::= zero or one instance of x)
  ;; The colon-flag is illegal here
  (let ((str (insert-spacers
              (format nil
                      (cond (has-colon  "~:F") ;illegal colon flag - force an error
                            (has-atsign "~V,V@F")
                            (t          "~V,VF"))
                      wid ndp val)
              :grouping grouping
              :spacer   spacer)))
    (if stream
        (princ str stream)
      str)))


(defun show-accel (n stream)
  (let* ((lsta (stream-take (accelerate-series #'euler stream) n))
         (lstb (stream-take stream n)))
    
    (labels ((diff-list (lst)
               (if (um:single lst)
                   :n/a
                 (- (second lst) (first lst))))

             (print-data (ix v1 dv1 v2 dv2)
               (format t "~%~2D~{  ~20,16,5,' /lzs::fmt-f-grouped/  ~10,2,2@E~}"
                       ix (list v1 dv1 v2 dv2))))
      (terpri)
      (princ " N       Accelerated Series   Fwd Delta           Nominal Series   Fwd Delta")
      (loop for ix of-type fixnum from 0
            for as on lsta ;bind as to successive cdrs of lsta
            for bs on lstb ;bind bs to successive cdrs of lstb
            do
            (let ((diffa (diff-list as))
                  (diffb (diff-list bs)))
              (print-data ix
                          (first as) diffa
                          (first bs) diffb)
              ))
      )))
    

