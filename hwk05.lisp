#|

 CS 2800 Homework 5 - Fall 2023

 - Due on Tuesday, Oct 17 by 11:00 pm.

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

 Instructions for programming problems:

 For all function definitions you must:

 (1) Perform contract-based testing (see Lecture Notes) by adding
     appropriate check=/check tests.  You only have to do this for
     functions where you are responsible for at least some part of the
     definition.  This should be done before you define the function,
     as it is intended to make sure you understand the spec.

     We will use ACL2s' check= function for tests. This is a
     two-argument function that rejects two inputs that do not
     evaluate equal. You can think of check= roughly as defined like
     this:

     (definec check= (x y :all) :bool
       :input-contract (equal x y)
       :output-contract (== (check= x y) t)
       t)

     That is, check= only accepts two inputs with equal value. For
     such inputs, t (or "pass") is returned. For other inputs, you get
     an error. If any check= test in your file does not pass, your
     file will be rejected.

     We will also use ACL2's check function, which is a version of
     check= that checks if a single form evalutes to t, so you can
     think of

     (check X)

     as being equivalent to

     (check= X t)

 (2) For all functions you define provide enough check= tests so that
     you have 100% expression coverage (see Lecture Notes).  You can
     use whatever tests we provide and your contract-based tests to
     achieve expression coverage, e.g., if the union of the tests we
     gave you and your contract-based tests provide 100% expression
     coverage, there is nothing left to do.

 (3) Contract-based testing and expression coverage are the minimal
     testing requirements.  Feel free to add other tests as you see
     fit that capture interesing aspects of the function.

 (4) For all functions where you are responsible for at least some
     part of the definition, add at least two interesting property
     forms. The intent here is to reinforce property-based testing.

 You can use any types, functions and macros listed on the ACL2s
 Language Reference (from class Webpage, click on "Lectures and Notes"
 and then on "ACL2s Language Reference"). 

 Since we don't know how to control the theorem prover, we will
 simplify the interaction with ACL2s somewhat. Instead of requiring
 ACL2s to prove termination and contracts, we allow ACL2s to proceed
 even if a proof fails.  However, if a counterexample is found, ACL2s
 will report it.  See the lecture notes for more information.  This is
 achieved using the following directives (do not remove them):

|#

(set-defunc-termination-strictp nil)
(set-defunc-function-contract-strictp nil)
(set-defunc-body-contracts-strictp nil)
(set-defunc-generalize-contract-thm nil)

#|

 The next form tells ACL2s to not try proving properties, unless
 we explicitly ask. You explicitly ask by adding :proofs? t like this:
 (property (...) :proofs? t ...)

|#

(set-acl2s-property-table-proofs? nil)

#|

 The next form tells ACL2s to not check contracts. If ACL2s does not
 prove function contracts when defining functions, then the property
 form will generate errors if it then tries to reason about the
 contracts of these functions. Instead of asking you to add the
 :check-contracts?  keyword command, we are just turning this testing
 off, which means you may not get as much checking as would otherwise
 be the case, so make sure your properties pass contract checking. If
 you want, you can comment out the next line to get more checking
 from ACL2s and if you run into problems, use the keyword command
 ":check-contracts? nil". Here's an example.

 (property (x :all)
   :check-contracts? nil
   (== (car x) (car x)))

|#

(set-acl2s-property-table-check-contracts? nil)

#|

 Also, we don't want to limit the time definec and counterexample
 generation takes.
 
 You may see some warnings here and there. Just ignore them. As
 long as the output is green, you are good to go.

|#

(set-defunc-timeout 10)
(acl2s-defaults :set cgen-timeout 3)

#|

We use the following ASCII character combinations to represent the Boolean
connectives:

  NOT     !

  AND     ^
  OR      v
  NOR     !v
  NAND    !^

  IMPLIES =>

  EQUIV   =
  XOR     <>

The binding powers of these functions are listed from highest to lowest
in the above table. Within one group (no blank line), the binding powers
are equal. This is the same as in class.

The symbols for the operators are different than used in the homeworks
and the lecture notes. That is on purpose.  Different books use
different symbols, so it is good to get accustomed to that.

(p !v q) is equivalent to !(p v q).  It is called "NOR" because it 
is the Negation of an Or.

(p !^ q) is equivalent to !(p ^ q).  It is called "NAND" because it 
is the Negation of an And.

|#

; Since Nor and Nand are not built-in, we will define them now. Feel
; free to use them below.

(definec !v (p q :bool) :bool
  (! (v p q))) ; note v is a macro that expands into or

(definec !^ (p q :bool) :bool
  (! (^ p q))) ; note ^ is a macro that expands into and

(definec <> (p q :bool) :bool
  (! (iff p q)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Simplification of formulas
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

There are many ways to represent a formula. For example:

p v (p => q)

is equivalent to

true

Note that true is simpler than p v (p => q). You will be given a set
of formulas and asked to find the simplest equivalent formulas.  By
simplest, we mean the formulas with the least number of
connectives. You can use any unary or binary connectives shown above
in the propositional logic section.

Write out an equational proof. Such proofs provide more assurance that
you have not made mistakes. 

You should use ACL2s to check your answers, as follows. 

|#

(property (p q :bool)
  (== (or p (=> p q)) t))

;; note we can get rid of the equality above, i.e., we can write
;; this instead.

(property (p q :bool)
  (or p (=> p q)))

;; Make sure you understand why.

#|

Find the simplest equivalent formula corresponding to the formula
below and prove equivalence using an equational reasoning proof.

(1) p = q = !p = r

Equational Reasoning Proof:

p = q = !p = r
{ Associative and Communative Properties }
p = !p = q = r
{ (p = !p) = false }
false = q = r
{ (p = q) = (p ^ q) v (!p ^ !q) }
((false ^ q) v (!false ^ !q)) = r
{ true = !false}
((false ^ q) v (true ^ !q)) = r
{ Constant Propogation }
(false v !q) = r
{ Constant Propogation }
!q = r
{ (p = q) = (p ^ q) v (!p ^ !q) }
(!q ^ r) v (!!q ^ !r)
{ !!p = p }
(!q ^ r) v (q ^ !r)
{ (p <> q) = (p ^ !q) v (!p ^ q) }
q <> r

|#

; The simplest equivalent formula is?
;
; Plug in your answer below using ACL2s connectives. Your answer below
; should be a quoted expression, e.g., if you simplified the above to
; p => q, then your answer should be:
; (defconst *q1-fm* '(=> p q))

(defconst *q1-fm* '(<> q r))

; Check the correctness of your answer by using ACL2s to prove the
; equivalence of your answer with the given formula. Note that this
; does not mean you have the simplest formula.
"Property A1"
(property (p q r :bool)
  (== (<> q r) (iff (iff (iff p q) (! p)) r)))

#|

Find the simplest equivalent formula corresponding to the formula
below and prove equivalence using an equational reasoning proof.

(2) (!p => (q v r)) !^ p

Equational Reasoning Proof:

(!p => (q v r)) !^ p
{ p => q = !p v q }
(p v (q v r)) !^ p
{ DeMorgan's Law }
!(p v (q v r)) v !p
{ DeMorgan's Law }
(!p ^ !(q v r)) v !p
{ DeMorgan's Law }
(!p ^ !q ^ !r) v !p
{ Shannon Expansion }
!p v false
{ Constant Propogation }
!p


|#

; The simplest equivalent formula is? Plug in your answer below using
; ACL2s connectives.

(defconst *q2-fm* '(! p))

; Check the correctness of your answer by using ACL2s to prove the
; equivalence of your answer with the given formula. Note that this
; does not mean you have the simplest formula.
"Property A2"
(property (p q r :bool)
  (== (! p) (!^ (=> (! p) (v q r)) p)))

#|

Find the simplest equivalent formula corresponding to the formula
below and prove equivalence using an equational reasoning proof.

(3) p !^ (q => p !v q)

Equational Reasoning Proof:

p !^ (q => p !v q)
{ p => q = !p v q }
p !^ (!q v (p !v q))
{ DeMorgan's Law }
!p v !(!q v (!p ^ !q))
{ Absorbtion Law }
!p v !(!q)
{ !!p = p }
!p v q
{ p => q = !p v q }
p => q

|#

; The simplest equivalent formula is? Plug in your answer below using
; ACL2s connectives.

(defconst *q3-fm* '(=> p q))

; Check the correctness of your answer by using ACL2s to prove the
; equivalence of your answer with the given formula. Note that this
; does not mean you have the simplest formula.
"Property A3"
(property (p q :bool)
  (== (=> p q) (!^ p (=> q (!v p q)))))

#|

Find the simplest equivalent formula corresponding to the formula
below and prove equivalence using an equational reasoning proof.

(4) (a => b) ^ (c => a) <> (a !^ b) !v (!a ^ !c)

Equational Reasoning Proof:

(a => b) ^ (c => a) <> (a !^ b) !v (!a ^ !c)
{ DeMorgan's Law }
(a => b) ^ (c => a) <> (a !^ b) !v (a !v c)
{ DeMorgan's Law }
(a => b) ^ (c => a) <> (a ^ b) ^ (a v c)
{ Associative Property }
(a => b) ^ (c => a) <> (a ^ (a v c)) ^ b
{ Absorbtion Laws}
(a => b) ^ (c => a) <> a ^ b
{ p => q = !p v q }
(!a v b) ^ (!c v a) <> a ^ b
{ (p <> q) = (p ^ !q) v (!p ^ q) }
((!a v b) ^ (!c v a) ^ !(a ^ b)) v (!((!a v b) ^ (!c v a)) ^ a ^ b)
{ DeMorgan's Law }
((!a v b) ^ (!c v a) ^ (!a v !b)) v ((!(!a v b) v !(!c v a)) ^ a ^ b)
{ DeMorgan's Law }
((!a v b) ^ (!c v a) ^ (!a v !b)) v (((a ^ !b) v (c ^ !a)) ^ a ^ b)
{ Redundancy Law }
(!a ^ (!c v a)) v (((a ^ !b) v (c ^ !a)) ^ a ^ b)
{ Distributive Property }
((!a ^ !c) v (!a ^ a)) v (((a ^ !b) v (c ^ !a)) ^ a ^ b)
{ p ^ !p = false }
((!a ^ !c) v false) v (((a ^ !b) v (c ^ !a)) ^ a ^ b)
{ Constant Propogation }
(!a ^ !c) v (((a ^ !b) v (c ^ !a)) ^ a ^ b)
{ Distributive Property }
(!a ^ !c) v (((a ^ !b ^ a) v (c ^ !a ^ a)) ^ b)
{ p ^ p = p}
(!a ^ !c) v (((!b ^ a) v (c ^ !a ^ a)) ^ b)
{ p ^ !p = false }
(!a ^ !c) v (((!b ^ a) v (c ^ false)) ^ b)
{ Constant Propogation }
(!a ^ !c) v (((!b ^ a) v false) ^ b)
{ Constant Propogation }
(!a ^ !c) v (!b ^ a ^ b)
{ p ^ !p = false }
(!a ^ !c) v (a ^ false)
{ Constant Propogation }
(!a ^ !c) v false
{ Constant Propogation }
(!a ^ !c)
{ DeMorgan's Law }
(a !v c)

|#

; The simplest equivalent formula is? Plug in your answer below using
; ACL2s connectives.

(defconst *q4-fm* '(!v a c))

; (a => b) ^ (c => a) <> (a !^ b) !v (!a ^ !c)

; Check the correctness of your answer by using ACL2s to prove the
; equivalence of your answer with the given formula. Note that this
; does not mean you have the simplest formula.
"Property A4"
(property (a b c :bool)
  (== (!v a c) (<> (^ (=> a b) (=> c a)) (!v (!^ a b) (^ (! a) (! c))))))
  


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Complete Boolean Bases
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

 In class, we saw that {v, !} is a complete Boolean base.  We also saw
 that there are complete Boolean bases that consist of only one
 operator. One example is !v, the NOR operator. Another example is !^,
 the NAND operator.

 We will use ACL2s to define a little compiler that compiles arbitrary
 formulas into formulas using only !v and we will formalize that this
 compilation step preserves the semantics of formulas.

 Why might you want to do this? You are working as an co-op student at
 NASA, who wants to implement some functionality in a circuit using
 only NOR gates. The computer that supported guidance, navigation and
 control for NASA's human spaceflight Apollo program was made out of
 NOR gates and NASA wants to recreate a version of this system.

|#

; This is a data definition for the Boolean Formulas you hae to
; condsider.  The design team is going to define the circuit using
; such formulas and the tools team is going to compile such formulas
; into formulas only using NORs.
(defdata BoolFm 
  (oneof bool 
         var 
         (list '! BoolFm)
         (list BoolFm (enum '(^ v <> !v !^)) BoolFm)))

; We define an assignment to be a list of variables.  Variables
; appearing in the list are treated as being true (t), while variables
; not appearing in the list are treated as being false (nil)
(defdata assignment (listof var))

; This function, determines the value of a variable v in assignment
; a. The function "in" is builtin.
(definec lookup (v :var a :assignment) :bool
  (in v a))

(check (! (lookup 'a '())))
(check (lookup 'a '(b a c)))

; Define the function BfEval, a function that given a BoolFm, p, and an
; assignment, a, evaluates p using assignment a.
(definec BfEval (p :BoolFm a :assignment) :bool
  (match p
    (:bool p)
    (:var (lookup p a))
    (('! q) (! (BfEval q a)))
    ((q '^ r) (^ (BfEval q a) (BfEval r a)))
    ((q 'v r) (v (BfEval q a) (BfEval r a)))
    ((q '<> r) (<> (BfEval q a) (BfEval r a)))
    ((q '!v r) (!v (BfEval q a) (BfEval r a)))
    ((q '!^ r) (!^ (BfEval q a) (BfEval r a)))))

(check (BfEval 'a '(a)))

; This is a data definition for Boolean expressions consisting
; of only constants, variables and NORs.
(defdata NorFm
  (oneof bool 
         var 
         (list NorFm '!v NorFm)))

; The following form states that NorFm is a subtype of BoolFm
(defdata-subtype NorFm BoolFm)

; Stated as a property, the above is
(property (p :NorFm)
  (BoolFmp p))

; Before you joined, the tools team decided to build a multi-pass
; compiler that starts with a BoolFm and during each pass one of the
; connectives are removed. It must happen in this order:  !^, <>,
; v, ^, !. The tools team already built the first pass. Here it
; is.

; The first step is to define BoolFm1, the type corresponding to
; formulas coming out of pass 1. Remember that this is just like
; BoolFm, but with !^ removed.

(defdata BoolFm1
  (oneof bool 
         var 
         (list '! BoolFm1)
         (list BoolFm1 (enum '(^ v <> !v)) BoolFm1)))

; The second step is to define BoolFm->BoolFm1, a function that
; peforms pass 1 of the compiler.

; But, first an introduction to `, backquote.
;
; Backquote is similar to ' (quote), but it allows you to selectively
; evaluate (unquote) certain forms, which you do by using a comma.
; 
; For example, `(a 1 (+ 2 3)) is just the same as '(a 1 (+ 2 3)) which
; is (list 'a 1 '(+ 2 3)) Here are check= forms confirming this.

(check= `(a 1 (+ 2 3)) '(a 1 (+ 2 3)))
(check= `(a 1 (+ 2 3)) (list 'a 1 '(+ 2 3)))

; Here is an example of selectively unquoting.
;
; `(a 1 ,(+ 2 3)) is just '(a 1 5) because we evaluated (unquoted) (+ 2 3)

(check= `(a 1 ,(+ 2 3)) '(a 1 5))

; We use ` in the next definition but it isn't needed, as we could
; have written (list '! (list q '^ r)) instead of `(! (,q ^ ,r)), so
; feel free to not use `, if it seems confusing, but try using it
; because it helps make things clearer, once you get used to it and
; the pros use it.

(definec BoolFm->BoolFm1 (p :BoolFm) :BoolFm1
  (match p
    ((q '!^ r) `(! (,(BoolFm->BoolFm1 q) ^ ,(BoolFm->BoolFm1 r))))
    ((q r s) `(,(BoolFm->BoolFm1 q) ,r ,(BoolFm->BoolFm1 s)))
    (('! q) `(! ,(BoolFm->BoolFm1 q)))
    (& p)))

; Make sure you understand the definition of BoolFm->BoolFm1.  For
; example, why do we need the recursive call? Actually, the code isn't
; correct. Fix it. That is, modify it so that it does what it is
; supposed to and add check='s and properties as per the instructions. 

(check= (BoolFm->BoolFm1 '(p !^ q)) '(! (p ^ q)))
(check= (BoolFm->BoolFm1 '(p ^ (q !^ r))) '(p ^ (! (q  ^ r))))
(check= (BoolFm->BoolFm1 '(! (! p))) '(! (! p)))

; You added check= tests, but the tools team seems to be unaware of
; property-based testing, so you are going to earn your paycheck by
; just introducing this one idea.
;
; Write a property that characterizes the correctness of BoolFm->BoolFm1
; by formalizing the claim that the formula returned by BoolFm->BoolFm1
; is equivalent to its input formula. Equivalence here means semantic
; equivalence, as determined by BfEval. This is one of the two
; properties you have to write for BoolFm->BoolFm1.

"Property 1"
(property (p :BoolFm a :assignment)
  (== (BfEval p a) (BfEval (BoolFm->BoolFm1 p) a)))

; The tools lead is very happy with the above property, as it captures
; functional correctness. Expect a job offer once you graduate.

; Define the compiler passes 2-5 using the above recipe, i.e., start
; by defining BoolFMi, the type corresponding to the formulas coming
; out of pass i. (We were feeling generous and provided some of these
; definitions for you.) Then define a function that given a formula of
; type BoolFMi-1, returns an equivalent formula of type BoolFMi. Then,
; add a property capturing semantic equivalence.

(defdata BoolFm2
  (oneof bool 
         var 
         (list '! BoolFm2)
         (list BoolFm2 (enum '(^ v !v)) BoolFm2)))

(definec BoolFm1->BoolFm2 (p :BoolFm1) :BoolFm2
  (match p
    ((q '<> r) 
     (let ((s (BoolFm1->BoolFm2 q))
           (u (BoolFm1->BoolFm2 r)))
       `((,s v ,u) ^ ((! ,s) v (! ,u)))))
    ((q r s) `(,(BoolFm1->BoolFm2 q) ,r ,(BoolFm1->BoolFm2 s)))
    (('! q) `(! ,(BoolFm1->BoolFm2 q)))
    (& p)))

(check= (BoolFm1->BoolFm2 '(! (! ((p <> q) !v (p ^ r))))) '(! (! ( ((p v q) ^ ((! p) v (! q))) !v (p ^ r)))))

"Property 2"
(property (p :BoolFm1 a :assignment)
  (== (BfEval p a) (BfEval (BoolFm1->BoolFm2 p) a)))

(defdata BoolFm3 
  (oneof bool 
         var 
         (list '! BoolFm3)
         (list BoolFm3 (enum '(^ !v)) BoolFm3)))

(definec BoolFm2->BoolFm3 (p :BoolFm2) :BoolFm3
  (match p
    ((q 'v r) `(! (,(BoolFm2->BoolFm3 q) !v ,(BoolFm2->BoolFm3 r))))
    ((q r s) `(,(BoolFm2->BoolFm3 q) ,r ,(BoolFm2->BoolFm3 s)))
    (('! q) `(! ,(BoolFm2->BoolFm3 q)))
    (& p)))

"Property 3"
(property (p :BoolFm2 a :assignment)
  (== (BfEval p a) (BfEval (BoolFm2->BoolFm3 p) a)))

(defdata BoolFm4 
  (oneof bool 
         var 
         (list '! BoolFm4)
         (list BoolFm4 '!v BoolFm4)))

(definec BoolFm3->BoolFm4 (p :BoolFm3) :BoolFm4
  (match p
    ((q '^ r) `((! ,(BoolFm3->BoolFm4 q)) !v (! ,(BoolFm3->BoolFm4 r))))
    ((q r s) `(,(BoolFm3->BoolFm4 q) ,r ,(BoolFm3->BoolFm4 s)))
    (('! q) `(! ,(BoolFm3->BoolFm4 q)))
    (& p)))

"Property 4"
(property (p :BoolFm3 a :assignment)
  (== (BfEval p a) (BfEval (BoolFm3->BoolFm4 p) a)))

; We already defined NorFm, so no need to define BoolFm5.

(definec BoolFm4->NorFm (p :BoolFm4) :NorFm
  (match p
    ((q r s) `(,(BoolFm4->NorFm q) ,r ,(BoolFm4->NorFm s)))
    (('! q) `(,(BoolFm4->NorFm q) !v nil))
    (& p)))

"Property 5"
(property (p :BoolFm4 a :assignment)
  (== (BfEval p a) (BfEval (BoolFm4->NorFm p) a)))

; Put all the passes together to form our compiler, which is the
; function BoolFm->5NorFm, which given a BoolFm, p, returns a NorFm by
; combining all of the compiler passes we defined. If the returned
; formula is q, then p and q should be equivalent.
;
(definec BoolFm->5NorFm (p :BoolFm) :NorFm
  (BoolFm4->NorFm (BoolFm3->BoolFm4 (BoolFm2->BoolFm3 (BoolFm1->BoolFm2 (BoolFm->BoolFm1 p))))))

; Write a property that characterizes the correctness of BoolFm->5NorFm.
"Property 6"
(property (p :BoolFm a :assignment)
  (== (BfEval p a) (BfEval (BoolFm->5NorFm p) a)))

; The design team has performed a preliminary analysis of your
; compiler. They are not done analyzing it yet, but they are
; requesting that you do this in a single pass. Your job is to write a
; single-pass compiler, by which we mean a single recursive ACL2s
; function that starting with a BoolFm returns an equivalent NorFm.
; Your function can only use functions from the ACL2s Language
; Reference and recursive calls to itself.
(definec BoolFm->NorFm (p :BoolFm) :NorFm
  (match p
    (('! q) `(,(BoolFm->NorFm q) !v nil))
    ((q r s) (match r
               ('^ (BoolFm->NorFm `(! (,q !^ ,s))))
               ('v (BoolFm->NorFm `(! (,q !v ,s))))
               ('!^ (BoolFm->NorFm `((! ,q) v (! ,s))))
               ('!v `(,(BoolFm->NorFm q) !v ,(BoolFm->NorFm s)))
               ('<> (BoolFm->NorFm `((,q v ,s) ^ ((! ,q) v (! ,s)))))))
    (& p)))

; The design team really likes properties and wants you to also write
; the functional correctness property for you single-pass compiler.
; Write a property that characterizes the correctness of BoolFm->NorFm
; by formalizing the claim that the formula returned by BoolFm->NorFm
; is equivalent to its input formula. Equivalence here means semantic
; equivalence, as determined by BfEval.
"Property 7"
(property (p :BoolFm a :assignment)
  (== (BfEval p a) (BfEval (BoolFm->NorFm p) a)))

; The design team has found what they consider to be a show-stopping
; problem. They are not happy. They are complanining that the compiler
; is highly inefficient. They presented their analysis in a high-level
; meeting and management agrees.  By EOD Tuesday, they want a compiler
; that never includes constants in its output and don't try to be
; smart by replacing constants with something even more
; complicated. See the lecture notes on constant propagation.  Your
; job is to get this working.  After a compiler team meeting, here is
; the plan.
;
; You decide to start by defining the type of the output the compiler
; should generate. It is based on NorFm but it is more restrictive, as
; it does not allow constants nested in formulas. Here is the
; definition.

; Helper data type
(defdata NorNCFm
  (oneof var 
         (list NorNCFm '!v NorNCFm)))

; no nested constants.
(defdata NorCPFm
  (oneof bool NorNCFm))

; The first thing you decide to do is to see if you can come up with a
; formula of type NorFm such that the minimal formula of type NorCPFm
; is smaller (less operators).

(defconst *NorFM-large* '((p !v p) !v (p !v (q !v r))))
(check (NorFMp *NorFM-large*))

(defconst *NorCPFm-small* 'p)
(check (NorCPFmp *NorCPFm-small*))

; Use ACL2s to check that the above two formulas are logically
; equivalent by transforming them into equivalent ACL2s formulas
; manually. This is an example of reduction. See the example below.

"Property 8"
(property (p q r :bool)
  (iff (!v (!v p p) (!v p (!v q r))) p))

; For example, here is how you can check that (a !v b) is logically
; equivalent to (b !v a).  Notice that we are using ACL2s' decision
; procedure using the idea of reduction, but to do so, we turn NorFm
; formulas (or NorCPFm or BoolFm or ...) into ACL2s expressions.

(property (a b :bool)
  (iff (!v a b) (!v b a)))

; Next, you want to make sure what you are asked to do makes sense. To
; do that you think about the following question: is it always a good
; idea to get rid of constants in NorCPFm formulas? The constant
; propagation rules in RAP always seem to simplify the formula, so
; this seems promising. But, is that the case for NorCPFm formulas?
; Actually, it isn't always the case. Show this by coming up with a
; NorFM formula such that the minimal formula of type NorCPFm is
; larger.

(defconst *NorFM-small* nil)
(check (NorFMp *NorFM-small*))

(defconst *NorCPFm-large* '(p !v (p !v p)))
(check (NorCPFmp *NorCPFm-large*))

; Use ACL2s to check that the above two formulas are logically
; equivalent by transforming them into equivalent ACL2s formulas
; manually.

"Property 9"
(property (p :bool)
  (iff (!v p (!v p p)) nil))

; The compiler team is surprised, but your reductions are
; compelling. They have to come up with another plan.  They're working
; on in, but in the meanwhile, they want you to define some functions
; that will help evaluate a more efficient compiler.  These functions
; will help with the specification of performance properties. Usually,
; we only consider functional correctness properties, but performance
; properties are also very important. Define a function that counts
; the number of operators in a BoolFm. 

(definec NumOps (p :BoolFm) :nat
  (match p
    ((q & r) (+ (NumOps q) (NumOps r) 1))
    (('! q) (1+ (NumOps q)))
    (& 0)))

(check= (NumOps '(a v (b !v (c <> d)))) 3)
(check= (NumOps '(a v (b !v (c <> (! d))))) 4)
(check (< (NumOps *NorCPFm-small*) (NumOps *NorFM-large*)))
(check (< (NumOps *NorFM-small*) (NumOps *NorCPFm-large*)))

; The compiler team asked for you to do this for all the types you
; defined, but notice that the above function can work on any subtype,
; so no need to do any extra work!

; Next define a function to determine the size of a BoolFm, which
; includes the number of operators plus the number of variables and
; constants.

(definec Size (p :BoolFm) :pos
  (match p
    ((q & r) (+ (Size q) (Size r) 1))
    (('! q) (1+ (Size q)))
    (& 1)))

(check= (size '(a v (b !v (c <> d)))) 7)
(check= (size '(a v (b !v (c <> (! d))))) 8)
; Finally define a function to determine the depth of a BoolFm. If you
; think of a BoolFm as a circuit, where operators are gates, this
; corresponds to the depth of the circuit or the length of the longest
; path in the circuit, i.e., how many gates you have to go through.

(definec Depth (p :BoolFm) :nat
  (match p
    ((q & r) (1+ (max (Depth q) (Depth r))))
    (('! q) (1+ (Depth q)))
    (& 0)))

(check= (depth nil) 0)
(check= (depth '((a v b) <> ((! c) !^ (! d)))) 3)

; EXTRA CREDIT 
;
; The rest of this is optional.
;
; Define a compiler that generates as simple a NorFm formula as
; possible.  By simple we mean the least NumOps. The five teams that
; generate the best compilers will get 50 extra homework points. To be
; eligible, the compilers have to be correct and efficient enough to
; handle all of our evaluation examples (which are hidden).  Uncomment
; the following if you want to participate in the competition. You can
; define any helper functions you want. You do not need to provide
; proporties and tests, but you may find them useful.
;
; I encourage you to try this, even though you may wind up not getting
; any credit for your effort. Fortune favors the bold! And, formula
; minimization is a multi-billion dollar industry, so this is an
; interesting exercise.

(defData BoolFmNot
  (list '! BoolFm))

(defData BoolFmBasic
  (oneof bool
         var
         (list '! var)
         (list BoolFmBasic (enum '(^ v)) BoolFmBasic)))

(definec BoolFm->BoolFmBasic/aux (p :BoolFm) :BoolFm
  (match p
    (('! q) (match q
              (:bool (! q))
              (:var `(! ,q))
              (('! r) (BoolFm->BoolFmBasic/aux r))
              ((r '!^ s) (BoolFm->BoolFmBasic/aux `(,r ^ ,s)))
              ((r '!v s) (BoolFm->BoolFmBasic/aux `(,r v ,s)))
              ((r 'v s) (BoolFm->BoolFmBasic/aux `((! ,r) ^ (! ,s))))
              ((r '^ s) (BoolFm->BoolFmBasic/aux `((! ,r) v (! ,s))))
              ((r '<> s) (BoolFm->BoolFmBasic/aux `(! ((,r v ,s) ^ ((! ,r) v (! ,s))))))))
    ((q r s) (match r
               ('!^ (BoolFm->BoolFmBasic/aux `((! ,q) v (! ,s))))
               ('!v (BoolFm->BoolFmBasic/aux `((! ,q) ^ (! ,s))))
               ('<> (BoolFm->BoolFmBasic/aux `((,q v ,s) ^ ((! ,q) v (! ,s)))))
               (& `(,(BoolFm->BoolFmBasic/aux q) ,r ,(BoolFm->BoolFmBasic/aux s)))))
    (& p)))

(definec BoolFm->BoolFmBasic (p :BoolFm) :BoolFmBasic
  (BoolFm->BoolFmBasic/aux p))
     
(property (p :BoolFm a :assignment)
  (== (BfEval p a) (BfEval (BoolFm->BoolFmBasic p) a)))
  

; TODO implement 
(definec BoolFmBasic= (p :BoolFmBasic q :BoolFmBasic) :bool
  (== p q))

; TODO Implement
(definec EBoolFmBasic (p :BoolFmBasic) :BoolFmBasic
  p)

(definec BoolFm->ENorFm (p :BoolFm) :NorFm 
  (BoolFm->NorFm p))
