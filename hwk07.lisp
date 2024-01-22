#|

 CS 2800 Homework 7 - Fall 2023

 - Due on Friday, Nov. 3 by 11:00 PM.

 - You will have to work in groups. Groups should consist of 2-3
   people. Make sure you are in exactly 1 group!  Use the
   piazza "search for teammates" post to find teammates. Please give
   students who don't have a team a home. If you can't find a team ask
   Ankit for help on Piazza. 

 - You will submit your hwk via gradescope. Instructions on how to
   do that are on Piazza. If you need help, ask on Piazza.

 - Submit the homework file (this file) on Gradescope. After clicking
   on "Upload", you must add your group members to the submission by
   clicking on "Add Group Member" and then filling their names. Every
   group member can submit the homework and we will only grade the
   last submission. You are responsible for making sure that your
   group submits the right version of the homework for your final
   submission. We suggest you submit early and often. Also, you will
   get feedback on some problems when you submit. However, this
   feedback does not determine your final grade, as we will manually
   review submissions. Submission will be enabled a few days after the
   homework is released, but well before the deadline.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

 For this homework you will need to use ACL2s.

 Technical instructions:

 - Open this file in ACL2s.

 - Make sure you are in ACL2s mode. This is essential! Note that you can
   only change the mode when the session is not running, so set the correct
   mode before starting the session.

 - Insert your solutions into this file where indicated (usually as "XXX")

 - Only add to the file. Do not remove or comment out anything pre-existing.

 - Make sure the entire file is accepted by ACL2s. In particular, there must
   be no "XXX" left in the code. If you don't finish all problems, comment
   the unfinished ones out. Comments should also be used for any English
   text that you may add. This file already contains many comments, so you
   can see what the syntax is.

 - When done, save your file and submit it without changing the name
   of the file.

 - Do not submit the session file (which shows your interaction with
   the theorem prover). This is not part of your solution. Only submit
   the lisp file.

  In this homework, we will focus on proving termination using measure
  functions.

  Your goal is to come up measure functions, to state the proof
  obligations corresponding to the fourth condition for measure
  functions and to then use ACL2s to prove termination.

  Optional: If you want extra equational reasoning problems, prove the
  properties you specify below and use the proof checker to check your
  proofs. 

|#

; The following commands tell ACL2s to use measures as we initially
; defined them in class. That means that measure functions should
; return natural numbers. ACL2s is also instructed to show more output
; during the proof process.

(set-termination-method :measure)
(set-well-founded-relation n<)
(set-defunc-typed-undef nil)
(set-defunc-generalize-contract-thm nil)
(set-gag-mode nil)
(set-ignore-ok t)

; If you think that your properties are OK, but ACL2s can't prove
; them, then use then use the ":proofs? nil" form, as shown below. Any
; top-level counterexamples you get indicate an error that you should
; fix.

(property (x :int)
  :proofs? nil
  (intp x))

#|

 You are given functions f0-f7.

 Your job is to do the following: 

 (1) specify measure functions for these functions 

 (2) for each recursive call, write out the proof obligation for
     showing that the measure function applied to the arguments to
     that recursive call decreases. See condition 4 of the initial
     measure function definition in the lecture notes for the details.

 (3) use ACL2s to check that your measure function can be used to
     admit the function. This will catch errors you make in your
     properties.

 Here is a worked out example that explains the process.

 You are given the following problem:

(definec m-1 (x :tl) :nat
  XXX)

(property (x :tl)
  XXX)

(definec f-1 (x :tl) :tl
  (declare (xargs :measure (if (tlp x) (m-1 x) 0)))
  (if (endp x)
      nil
    (cons 1 (f-1 (cdr x)))))

 Here is the solution.

|#

; Fill in the XXX's by defining the measure function.
(definec m-1 (x :tl) :nat
  (len x))

; This is the required property corresponding to the only recursive
; call in f-1. You should be able to prove it using equational
; reasoning, so do that, if you want practice. Since we already
; covered equational reasoning, we leave this tedious work to ACL2s.
(property (x :tl)
  (=> (! (endp x))
      (< (m-1 (cdr x))
         (m-1 x))))

; If you did the above correctly, the definition should go through.
; If it doesn't you can comment out the definition and add a note.
; Note how a measure if given using the declaratioin below. Use an if
; where you test the input contract (types and explicit :ic) and if
; that holds, call the measure function, else return 0. I filled this
; in for you.

(definec f-1 (x :tl) :tl
  (declare (xargs :measure (if (tlp x) (m-1 x) 0)))
  (if (endp x)
      nil
    (cons 1 (f-1 (cdr x)))))

#|

If the definition does not go through and the definec fails, look at
the output from the failed proof attempt and you will see a form
starting of this form

(DEFUN F-1 (X)
  (DECLARE (XARGS :GUARD ...
                  :VERIFY-GUARDS NIL
                  :NORMALIZE NIL
                  :HINTS ...
                  :MEASURE ...))
  (MBE :LOGIC ...
       :EXEC ...))

You copy and paste that form into your .lisp file and can try
admitting it. That will now show you more information about why the
measure failed, which should help you fix your errors.

|#

(definec m0 (x :int) :nat
  (if (<= x -1000) 1
      (+ (floor (+ x 1000) 3) 2)))

"Property 0-1"

(property (x :int)
  (=> (> x -1000)
      (< (m0 (- x 3))
         (m0 x))))

(definec f0 (x :int) :int
  (declare (xargs :measure (if (intp x) (m0 x) 0)))
  (if (<= x -1000)
      1
    (1+ (f0 (- x 3)))))

(definec f-trace (a b :nat) :tl
  (declare (xargs :mode :program))
  (cond ((= a b) (list (list a b)))
        ((< b a) (cons (list a b)
                       (f-trace (1- a) (1+ b))))
        (t (cons (list a b)
                 (f-trace (1+ b) a)))))

(f-trace 4 4)
(f-trace 10 4)
(f-trace 11 4)
(f-trace 4 10)
(f-trace 4 11)

(definec m-a<=b (a b :nat) :nat
  :ic (<= b a)
  (if (evenp (- a b))
    (/ (- a b) 2)
    (+ 2 (/ (- (1+ a) b) 2))))

(definec m1 (a b :nat) :nat
  (if (<= b a)
    (m-a<=b a b)
    (1+ (m-a<=b (1+ b) a))))

"Property 1-1"
(property (a b :nat)
  :hyps (^ (!= a b) (< b a))
  (< (m1 (1- a) (1+ b)) (m1 a b)))

"Property 1-2"
(property (a b :nat)
  :hyps (^ (!= a b) (! (< b a)))
  (< (m1 (1+ b) a) (m1 a b)))

(definec f1 (a b :nat) :bool
  (declare (xargs :measure (if (and (natp a) (natp b)) (m1 a b) 0)))
  (v (= a b)
     (if (< b a)
         (f1 (1- a) (1+ b))
       (f1 (1+ b) a))))

(definec m2 (x :tl y :int) :nat
  (cond ((= y (len x)) 0)
        ((> y (len x)) (- y (len x)))
        (t (+ (- y) (* 2 (len x))))))

"Property 2-1"
(property (x :tl y :int)
  (=> (< y (len x))
      (< (m2 x (+ 1 y (len x)))
         (m2 x y))))

"Property 2-2"
(property (x :tl y :int)
  (=> (> y (len x))
      (< (m2 (cons y x) y)
         (m2 x y))))

(definec f2 (x :tl y :int) :nat
  (declare (xargs :measure (if (and (tlp x) (intp y)) (m2 x y) 0)))
  (cond ((= y (len x)) y)
        ((<= y (len x)) (f2 x (+ 1 y (len x))))
        (t (f2 (cons y x) y))))

(definec m3 (x y :pos) :nat
  :ic (< x y)
  (cond ((< (* 2 x) y) 0) 
        ((> (* 2 x) y) 1)
        ((= (* 2 x) y) 2)))

"Property 3-1"
(property (x y :pos)
  :hyps (< x y)
  (=> (= (* 2 x) y)
      (< (m3 (* 2 x) (+ y 1))
         (m3 x y))))

"Property 3-2"
(property (x y :pos)
  :hyps (< x y)
  (=> (> (* 2 x) y)
      (< (m3 (- y x) y)
         (m3 x y))))

(definec f3 (x y :pos) :all
  :ic (< x y)
  (declare (xargs :measure (if (and (posp x) (posp y) (< x y)) (m3 x y) 0)))
  (cond ((= (* 2 x) y) (f3 (* 2 x) (+ y 1)))
        ((> (* 2 x) y) (f3 (- y x) y))
        (t nil)))

(definec m4 (a :nat b :int c :tl) :nat
  (if (> (- b) 2) (+ a (* 2 (len c)))
    (+ a b (* 2 (len c)) 2)))

"Property 4-1"
(property (a :nat b :int c :tl)
  (=> (^ (! (zp a)) (< a b))
      (< (m4 a (- b 4) c)
         (m4 a b c))))

"Property 4-2"
(property (a :nat b :int c :tl)
  (=> (^ (! (zp a)) (>= a b) (> (- b) 2))
      (< (m4 (1- a) (1+ b) (rest c))
         (m4 a b c))))

"Property 4-3"
(property (a :nat b :int c :tl)
  (=> (^ (! (zp a)) (>= a b) (>= (- b) 2) (! (endp c)))
      (< (m4 a (1+ b) (rest c))
         (m4 a b c))))

(definec f4 (a :nat b :int c :tl) :int
  (declare (xargs :measure (if (and (natp a) (intp b) (tlp c)) (m4 a b c) 0)))
  (cond ((zp a)      (len c))
        ((< a b)     (f4 a (- b 4) c))
        ((> (- b) 2) (+ a (f4 (1- a) (1+ b) (rest c))))
        ((endp c)    (+ a b))
        (t           (f4 a (1+ b) (rest c)))))

(definec m5 (x :nat l :tl a :all) :nat
  (declare (ignorable a))
  (if (> x 0) (+ x (len l))
      (len l)))

"Property 5-1"
(property (x :nat l :tl a :all)
  (=> (^ (! (endp l)) (! (= x 0)) (not (natp (/ x 2))))
      (< (m5 (- x 1) l a)
         (m5 x l a))))

"Property 5-2"
(property (x :nat l :tl a :all)
  (=> (^ (! (endp l)) (! (= x 0)) (natp (/ x 2)) (> x (len l)))
      (< (m5 (/ x 2) l 2)
         (m5 x l a))))

"Property 5-3"
(property (x :nat l :tl a :all)
  (=> (^ (! (endp l)) (! (= x 0)) (natp (/ x 2)) (<= x (len l)))
      (< (m5 x (rest l) (first l))
         (m5 x l a))))

(definec f5 (x :nat l :tl a :all) :all
  (declare (xargs :measure (if (and (natp x) (tlp l)) (m5 x l a) 0)))
  (cond ((endp l) a)
        ((= x 0) 1)
        ((not (natp (/ x 2))) (f5 (- x 1) l a))
        ((> x (len l)) (f5 (/ x 2) l x))
        (t (f5 x (rest l) (first l)))))

(definec m6 (x :rational) :nat
  (if (> x 0) (1+ (floor (* 100 x) 1))
      0))

"Property 6-1"
(property (x :rational)
  (=> (^ (> x 0) (>= x 2))
      (< (m6 (/ x 2))
         (m6 x))))

"Property 6-2"
(property (x :rational)
  (=> (^ (> x 0) (< x 2) (>= x 1))
      (< (m6 (- x 1/100))
         (m6 x))))

"Property 6-3"
(property (x :rational)
  (=> (^ (> x 0) (< x 2) (< x 1))
      (< (m6 (- x))
         (m6 x))))

(definec f6 (x :rational) :rational
  (declare (xargs :measure (if (rationalp x) (m6 x) 0)))
  (cond ((<= x 0) x)
        ((>= x 2) (f6 (/ x 2)))
        ((>= x 1) (f6 (- x 1/100)))
        (t (f6 (- x)))))

; Read about l< and lex in the lecture notes and use it prove
; termination of the following.

(set-well-founded-relation l<)

(definec m7 (n m :nat) :lex
  (cons n (cons (+ (* 2 n) m) nil)))

"Property 7-1"
(property (n m :nat)
  (=> (^ (! (zp n)) (zp m))
      (l< (m7 (1- n) 1)
          (m7 n m))))

"Property 7-2"
(property (n m :nat)
  (=> (^ (! (zp n)) (! (zp m)))
      (l< (m7 n (1- m)) (m7 n m))))

"Property 7-3"
(property (n m :nat x :pos)
  :hyps (^ (! (zp n))
           (! (zp m)))
  (l< (m7 (1- n) x) (m7 n m)))

(definec f7 (n m :nat) :pos
  (declare (xargs :measure (if (and (natp n) (natp m)) (m7 n m) 0)))
  (cond ((zp n) (1+ m))
        ((zp m) (f7 (1- n) 1))
        (t (f7 (1- n) (f7 n (1- m))))))