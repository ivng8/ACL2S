#|

CS 2800 Homework 4 - Fall 2023

 - Due on Tuesday, Oct 10 by 11:00 pm.

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
The Imitation Game Homework.

This homework is about encryption. Not the kind Turing had to deal
with, but with the kind we saw in class.

Consider a very old problem, secure communication.  This field is
called "cryptography" whose etymology originates from the Greek
words "crypto", meaning hidden, and "graphy", meaning writing.  For
example, various city-states in Ancient Greece were known to use
cryptographic methods to send secure messages in the presence of
adversaries.

We will formalize one-time pads, as described in Section of the
lecture notes entitled "The Power of Xor."  This involves writing code
for encrypting and decrypting messages, as well as formalizing and
testing properties that the code should enjoy.

One-time pads allow us to encrypt messages with "perfect" secrecy.
What this means is that if an adversary intercepts an encoded message,
they gain no information about the message, except for an upper bound
on the length of the message. 

If you look at most other types of encryption, e.g., RSA, then with
enough computational resources, an adversary can decrypt encoded
messages. The best known methods for breaking such encryption schemes
take time exponential in the size of the keys used. However, whether
this can be done in polynomial time is an open question.

Many movies have a red telephone that is used to connect the Pentagon
with the Kremlin. While there was no such red telephone, there was a
teletype-based encryption mechanism, the "Washington–Moscow Direct
Communications Link," in place between the US and USSR, which used
one-time pads. This connection was established in 1963, following the
Cuban missile crisis.

You can read more about the advantages and disadvantages of one-time
pads by searching online. We will see how to break one-time pads if
one is not careful. 

In fact, the ultimate goal of this exercise is for you to decrypt the
following intercepted secret message. 

|#

;; We intercepted this message and want to decode it. The message was
;; just a sequence of 0's and 1's but our human intelligence
;; determined the character encoding used and characters are encoded
;; using 5 bits, so we tranformed the message into a list of lists of
;; Booleans, each of length 5. 
(def-const *secret-message*
  '((0 1 0 1 0)
    (1 1 1 1 0)
    (1 1 1 0 1)
    (0 0 0 1 1)
    (0 1 0 0 1)
    (0 1 1 0 1)
    (1 0 0 0 1)
    (1 1 0 1 1)
    (1 0 0 1 1)
    (0 0 0 1 1)
    (1 1 0 0 0)
    (0 1 0 0 0)
    (1 0 1 1 1)
    (0 1 1 1 1)
    (1 0 1 0 0)
    (0 0 0 1 1)
    (1 1 1 0 0)
    (1 0 1 1 1)
    (0 1 1 1 0)
    (0 0 0 1 1)
    (1 0 0 0 0)
    (0 1 1 0 1)
    (1 0 1 0 1)
    (1 0 1 1 0)
    (1 1 1 0 1)
    (1 1 0 1 0)
    (0 0 0 1 1)
    (1 0 1 1 1)
    (0 1 1 0 0)
    (1 1 1 0 1)
    (0 1 0 0 0)
    (0 0 0 1 1)
    (0 1 0 1 0)
    (1 1 1 1 0)
    (1 1 1 0 1)
    (0 0 0 1 1)
    (1 0 0 1 0)
    (1 1 0 0 1)
    (0 0 0 0 0)
    (0 0 0 0 1)
    (0 0 0 1 1)
    (1 1 0 1 0)
    (1 0 1 1 1)
    (1 1 1 1 1)
    (0 0 1 0 0)
    (0 1 0 1 1)
    (0 0 0 1 1)
    (1 1 0 0 0)
    (1 1 0 0 1)
    (1 1 0 1 1)
    (1 0 0 1 1)))

#|

 How are we going to decode the encrypted message?

 Well, notice that each encrypted message consists of a list of lists
 of Bits, each of length 5. That is because each list of Bits
 corresponds to a character, as we'll explain shortly.

 But, first we start with some data definitions.

 Below is a data definition for a bit and a list of bits. The name bv
 is an abbreviation for BitVector.

 There is also a data definition for a list of exactly 5 bits.  The
 name bv5 is an abbreviation for BitVector5.

|#

(defdata bit (oneof 0 1))
(defdata bv (listof bit))
(defdata bv5 (list bit bit bit bit bit))

; Note that bv5 is a subtype of bv: every element of bv5 is also an
; element of bv. This is how you state this fact. Think of the form
; below as a kind of property involving data definitions.
(defdata-subtype bv5 bv)

; We define lobv5, a list of bv5's. Something of this type is a
; message.
(defdata lobv5 (listof bv5))

; We also define a list of bv's.
(defdata lobv (listof bv))

; Notice that lobv5 is a subtype of lobv.
(defdata-subtype lobv5 lobv)

;; Question 1
;; Use CHECK to check that *SECRET-MESSAGE* is of type lobv5.
;; Use PROPERTY to check that *SECRET-MESSAGE* is of type lobv5.
;;
;; Notice that PROPERTY is more general than CHECK and CHECK=, as we can always
;; turn a CHECK or CHECK= form into a PROPERTY form, eg given the form
;;     (CHECK exp1)
;; an equivalent PROPERTY form is:
;;     (PROPERTY () exp1)
;; Given the form
;;     (CHECK= exp1 exp2)
;; an equivalent PROPERTY form is:
;;     (PROPERTY () (== exp1 exp2))

(check (lobv5p *SECRET-MESSAGE*))

"Property 1"
(property ()
  (lobv5p *SECRET-MESSAGE*))

;; Luckily, our human intelligence has learned that the encrypted
;; message is comprised of letters from the following collection
;; of characters.

(def-const *chars*
  '(#\A #\B #\C #\D #\E #\F #\G #\H #\I #\J #\K #\L #\M #\N 
    #\O #\P #\Q #\R #\S #\T #\U #\V #\W #\X #\Y #\Z #\Space 
    #\: #\- #\' #\( #\)))

;; This is a data definition for the legal characters. 
(defdata char (enum *chars*)) 

;; Once decoded, a message will be a list of characters from 
;; *chars*. This is a data definition for a list whose elements are
;; legal characters.
(defdata lochar (listof char))

; We want a mapping (function) from chars to bv5s. Since char is
; finite, we will use an alist. An alist is a true list, whose
; elements are conses. Here is the data definition for the mapping.

(defdata char-bv5 (alistof char bv5))

; Here are some check forms.
(check (char-bv5p '((#\G . (0 0 0 0 1)))))

; #\g is not a char!
(check (! (char-bv5p '((#\g . (0 0 0 0 1))))))

; (0 0 0 1) is not a bv5!
(check (! (char-bv5p '((#\G . (0 0 0 1))))))

#|

 Here is the plan for creating this mapping. 

 One option is to just define the mapping directly with a form like
 this: 

 (def-const *bv-char-map*
   '((#\A . (0 0 0 0 0))
     (#\B . (1 0 0 0 0))
     ...))

 The option we will choose is to define the mapping algorithmically
 and in a way that can be used for bit vectors of arbitrary length,
 not just length 5. The company needs this to decrypt other messages 
 that use different encodings.

 Here is the plan.

 We will define a function, generate-bit-vectors, that given a
 natural number, n, will generate all bit vectors of length n.  It has
 to generate them in the following order

 0 ... 0 0 0
 0 ... 0 0 1
 0 ... 0 1 0
 0 ... 0 1 1
 0 ... 1 0 0
 ...

 which you can think of as corresponding to 0, 1, 2, 3, 4, ... .

 We will then use generate-bit-vectors to generate all bit vectors of
 length 5 and will pair them with the chars.
 
 Let's flesh this out some more.

 We start with the definition of generate-bit-vectors and here is
 the plan for doing that. generate-bit-vectors will be a
 non-recursive function that first creates a list of n 0s, using the
 function n-copies, and then calls a helper function,
 generate-bit-vectors-aux, with the list of n 0s and the number
 of bit vectors of length n. 

 So we have to now define n-copies and generate-bit-vectors-aux. 

 The function generate-bit-vectors-aux is given a bit vector, v,
 and a nat, n, as input and it generates a list of n bit vectors,
 starting with v, followed by the next bit vector in the ordering
 above, and so on.  If you get to the last bitvector (1 1 ... 1), wrap
 around and continue with (0 0 ... 0). 

 The function next-bv is responsible for computing the next bit
 vector.

|#

;; Question 2
;; Define next-bv, using the above specification.
;; Make sure to add tests and properties as described in the
;; instructions for all definitions, including for helper functions.
;; I used a helper function in my solution.

(definec next-bv/aux (b :bv) :tl
  (if (lendp b) (list '() t)
    (let*
      ((prev (next-bv/aux (tail b)))
       (prev-list (head prev))
       (carry-1? (second prev)))
      (if carry-1? 
        (list (cons (if (= (head b) 1) 0 1) prev-list) (= (head b) 1))
        (list (cons (head b) prev-list) nil)))))

(check= (next-bv/aux '(1)) '((0) t))
(check= (next-bv/aux '(0 1)) '((1 0) nil))
(check= (next-bv/aux '(0)) '((1) nil))
(check= (next-bv/aux '()) '(() t))

(property (b :bv)
  :hyps (and (not (lendp b)) 
             (= (tail (next-bv/aux (tail b))) t)
             (= (head b) 1))
  (== (tail (next-bv/aux b)) t))

(property (b :bv)
  :hyps (and (not (lendp b))
             (= (tail (next-bv/aux (tail b))) t))
  (not (= (head b) (head (head (next-bv/aux b))))))
      
(definec next-bv (b :bv) :bv
  (head (next-bv/aux b)))

(check= (next-bv '(0 0 0 0)) '(0 0 0 1))
(check= (next-bv '(1 1 1 1)) '(0 0 0 0))
(check= (next-bv '(1 0 0 0)) '(1 0 0 1))
(check= (next-bv '(0 0 0 1)) '(0 0 1 0))
(check= (next-bv '()) '())

(check= (next-bv '(1)) '(0))

(property (b :bv)
  :hyps (== b (next-bv b))
  (== b '()))

;; Question 3
;; Specify the property that the length (next-bv b) is the same as the
;; length of b

"Property 2"
(property (b :bv)
  (== (length (next-bv b)) (length b)))

;; Question 4
;; Define the function generate-bit-vectors-aux, as specified
;; above. 
(definecd generate-bit-vectors-aux (v :bv n :nat) :lobv
  (match n
    (0 '())
    (& (cons v (generate-bit-vectors-aux (next-bv v) (1- n))))))

(check= (generate-bit-vectors-aux '(0 0 0 1) 16) '((0 0 0 1) 
                                              (0 0 1 0) (0 0 1 1) 
                                              (0 1 0 0) (0 1 0 1)
                                              (0 1 1 0) (0 1 1 1)
                                              (1 0 0 0) (1 0 0 1) 
                                              (1 0 1 0) (1 0 1 1) 
                                              (1 1 0 0) (1 1 0 1)
                                              (1 1 1 0) (1 1 1 1)
                                              (0 0 0 0)))

(check= (generate-bit-vectors-aux '() 5) '(() () () () ()))
(check= (generate-bit-vectors-aux '() 0) '())
(check= (generate-bit-vectors-aux '(0 0 0 1) 0) '())

(defconst *b* '(0 0))

(property (b :bv)
  (let ((new-bv (generate-bit-vectors-aux b (1+ (expt 2 (len b))))))
    (== (first new-bv) (first (last new-bv)))))

(property (b :bv)
  (let ((b2 (generate-bit-vectors-aux b 2)))
    (== (second b2) (next-bv (first b2)))))

;; Question 5
;; Define the function n-copies, as specified above. 
(definec n-copies (x :all n :nat) :tl
  (match n
    (0 '())
    (& (cons x (n-copies x (1- n))))))

(check= (n-copies 3 0) '())
(check= (n-copies 3 5) '(3 3 3 3 3))

;; Here is a property showing that calling n-copies on a bit and a nat,
;; results in an bv.
(property (x :bit n :nat)
  (bvp (n-copies x n)))

(property (x :all n :pos)
  (== x (head (n-copies x n))))

;; Question 6
;; Define the function generate-bit-vectors, as specified above. 
(definec generate-bit-vectors (n :nat) :lobv
  (generate-bit-vectors-aux (n-copies 0 n) (expt 2 n)))

;; Here is a free test.
(check= (generate-bit-vectors 3)
        '((0 0 0)
          (0 0 1)
          (0 1 0)
          (0 1 1)
          (1 0 0)
          (1 0 1)
          (1 1 0)
          (1 1 1)))

(check= (generate-bit-vectors 0) '(()))

(property (n :nat)
  (== (len (generate-bit-vectors n)) (expt 2 n)))

(property (n :nat)
  :hyps (>= n 2)
  (== (next-bv (first n)) (second n)))

(def-const *bv5-values*
  (generate-bit-vectors 5))

;; Question 7
;; Define list-zip, a function that given two TL's zips them together,
;; eg, (list-zip '(a b c) '(1 2 3)) should return the alist
;; '((a . 1) (b . 2) (c . 3))
(definec list-zip (x y :tl) :alist
  :pre (= (len x) (len y))
  (cond
   ((or (lendp x) (lendp y)) '())
   ((cons (cons (head x) (head y)) (list-zip (tail x) (tail y))))))

(check= (list-zip '(a b c) '(1 2 3))
        '((a . 1) (b . 2) (c . 3)))

(check= (list-zip '() '()) '())

(property (x :lobv y :lochar)
  :hyps (and (= (len x) (len y)) (posp (len x)))
  (let* ((map (list-zip x y))
         (first (head map)))
    (and (bvp (car first)) (charp (cdr first)))))

(property (x :tl y :tl)
  :hyps (and (= (len x) (len y)) (posp (len x)))
  (let* ((map (list-zip x y))
         (first (head map)))
    (and (== (head x) (car first)) (== (head y) (cdr first)))))

; We now have the mapping from chars to bv5s. 
(def-const *bv5-char-map*
  (list-zip *char-values* *bv5-values*))

; Let's check that *bv5-char-map* is really a char-bv5p
(check= (char-bv5p *bv5-char-map*) t)

; Here are some checks.
(check= (nth 23 *bv5-char-map*)
        '(#\X 1 0 1 1 1)) ; which is equal to '(#\X . (1 0 1 1 1))

;; Question 8
;; Define a function that given an element a and an alist l returns
;; the cons that has a as its car or nil if no such cons exists.
;; You have to use match when defining find-car and you cannot use
;; helper functions.
(definec find-car (a :all l :alist) :list
  (match l
    (nil nil)
    (& (match (head l)
         ((!a . &) (head l))
         (& (find-car a (tail l))))))) 

(check= (find-car #\W *bv5-char-map*) '(#\W 1 0 1 1 0))
(check= (find-car #\A '()) '())

(property (a :all)
  (== (find-car a '()) nil))

(property (a :all l :alist)
  :hyps (not (endp (find-car a l)))
  (= (car (find-car a l)) a))

;; Question 9
;; Define a function that given an element a and an alist l returns
;; the cons that has a as its cdr or nil if no such pair exists.
;; You have to use match when defining find-cdr and you cannot use
;; helper functions.

(definec find-cdr (a :all l :alist) :list
  (match l
    (nil nil)
    (& (match (head l)
         ((& . !a) (head l))
         (& (find-cdr a (tail l)))))))

(check= (find-cdr '(0 1 1 0 1) *bv5-char-map*)
        '(#\N 0 1 1 0 1))
(check= (find-cdr #\A '()) '())

(property (a :all)
  (== (find-cdr a '()) nil))

(property (a :all l :alist)
  :hyps (not (endp (find-cdr a l)))
  (= (cdr (find-cdr a l)) a))

;; Question 10
;; Next we want to define functions that given a char return the
;; corresponding bv5 and the other way around. Define these
;; functions.
(definec char->bv5 (c :char) :bv5
  (tail (find-car c *bv5-char-map*)))
  
(check= (char->bv5 #\N) '(0 1 1 0 1))

(definec bv5->char (b :bv5) :char
  (head (find-cdr b *bv5-char-map*)))

(check= (bv5->char '(0 1 1 0 1)) #\N)

(property (c :char)
  (== (bv5->char (char->bv5 c)) c))

(property (b :bv5)
  (== (char->bv5 (bv5->char b)) b))

;; Question 11
;; Define a function that xor's bit vectors. Function XOR-BV takes
;; 2 BV's (b1 and b2) of the same length as input and returns a
;; BV as output. It works by xor'ing the nth bit of b1 with
;; the nth bit of b2. You have to first define bxor that given two
;; bits xors them together. This is just like xor, but we use 0
;; instead of nil (false) and 1 instead of t (true).

(definec bxor (x y :bit) :bit
  (match (= x y)
    (nil 1)
    (t 0)))

(check= (bxor 1 0) 1)
(check= (bxor 1 1) 0)
(check= (bxor 0 1) 1)
(check= (bxor 0 0) 0)

(definec xor-bv (b1 b2 :bv) :bv
  :ic (= (len b1) (len b2))
  :oc (= (len (xor-bv b1 b2)) (len b1))
  (cond
    ((or (lendp b1) (lendp b2)) '())
    ((cons (bxor (head b1) (head b2)) (xor-bv (tail b1) (tail b2))))))
     
(check= (xor-bv '(0 1 0 1) '(0 0 1 1)) '(0 1 1 0))
(check= (xor-bv '() '()) '())

; Specify a property stating that if we apply xor-bv to arguments of
; the type bv5 then we get a bv5 back.
"Property 3"
(property (x y :bv5)
  (bv5p (xor-bv x y)))

; Specify the property that the length of the output of xor-bv is
; equal to the length on the inputs. Remember you can only call xor-bv
; on inputs of the same length.
"Property 4"
(property (x y :bv)
  :hyps (= (len x) (len y))
  (= (len x) (len (xor-bv x y))))

; Specify the property that xor-bv is commutative.
"Property 5"
(property (x y :bv)
  :hyps (= (len x) (len y))
  (== (xor-bv x y) (xor-bv y x)))

; Specify the property that xor-bv is associative.
"Property 6"
(property (x y z :bv)
  :hyps (= (len x) (len y))
  (== (xor-bv x (xor-bv y z)) (xor-bv (xor-bv x y) z)))

; Specify the property that starting with b1, if you xor-bv it with b2
; and then xor-bv it with b2 again, you get b1, i.e., that you can
; invert the first xor-bv by just applying xor-bv with the same
; argument. 
"Property 7"
(property (x y :bv)
  :hyps (= (len x) (len y))
  (== x (xor-bv (xor-bv x y) y)))

; You can ignore this
(in-theory (disable charp bv5p xor-bv-definition-rule
                    bv5->char-definition-rule
                    char->bv5-definition-rule))

;; Question 12
;; Define a function to encrypt a single character, given a BV5.
;; Function ENCRYPT-CHAR, given a char C, and a bv5 B, which you can
;; think of as the secret, returns the bv5 obtained by turning C into
;; a bitvector and xor'ing it with B.

(definec encrypt-char (c :char b :bv5) :bv5
  (xor-bv (char->bv5 c) b))

(check= (encrypt-char #\B '(1 0 1 0 1)) '(1 0 1 0 0))

; Ignore this
(in-theory (disable encrypt-char-definition-rule))

;; Question 13

;; We will now define a function that given a lochar M (a message) and
;; a lobv5 S (a secret key, i.e., a "one-time pad" represented as a
;; list of bv5s), returns a lobv5, the result of encrypting every
;; character in the message with the corresponing bit vector in S.  We
;; will require that S, the secret key, is at least as long as M, the
;; message. See the definition of xor-bv to see how to specify extra
;; constraints on the inputs.

(definec encrypt (m :lochar s :lobv5) :lobv5
  :ic (>= (len s) (len m))
  (match m
    (nil '())
    (& (cons (encrypt-char (head m) (head s)) (encrypt (tail m) (tail s))))))

(check= (encrypt '() '()) '())
(check= (encrypt '(#\A) '((1 1 1 1 1))) '((1 1 1 1 1)))
(check= (encrypt '(#\A #\B #\C) '((1 1 1 1 1) (1 1 1 1 1) (1 1 1 1 1))) '((1 1 1 1 1) (1 1 1 1 0) (1 1 1 0 1)))
(check= (encrypt '() '((0 0 0 0 0))) '())
(check= (encrypt '(#\A #\B #\C) '((1 1 1 1 1) (1 1 1 1 1) (1 1 1 1 1) (1 1 1 1 1))) '((1 1 1 1 1) (1 1 1 1 0) (1 1 1 0 1)))

; Make sure that this property passes.
(property (m :lochar s :lobv5)
  :hyps (<= (len m) (len s))
  (= (len (encrypt m s)) (len m)))

; Here are our (really bad!) keys.
; They are really bad because they should be a random sequence
; of bit vectors!
(def-const *secret-keys* (n-copies '(1 0 0 1 1) (len *secret-message*)))

;; Question 14
;; 
;; Now let's define the DECRYPT-BV5, that given a bv5 B, and a secret
;; bv5 S, returns the char obtained by xor'ing B with S and turning
;; that into a char.
(definec decrypt-bv5 (b :bv5 s :bv5) :char
  (bv5->char (xor-bv b s)))

(check= (decrypt-bv5 '(1 0 1 0 0) '(1 0 1 0 1)) #\B)

;; Question 15
;; 
;; We will now define a function that given a lobv5 e (think of e
;; as the encrypted message, which is a list of bv5's) and a lobv5
;; s (think of s as our shared secret key, a list of bv5s), returns
;; a list of characters, the result of decrypting every element in
;; the message with the corresponing bit vector in s. We will
;; require that s, the secret key, is at least as long as e, the
;; encrypted message. The output contract should state that what we
;; return is of type lochar.

(definec decrypt (e :lobv5 s :lobv5) :lochar
  :ic (>= (len s) (len e))
  (match e
    (nil '())
    (& (cons (decrypt-bv5 (head e) (head s)) (decrypt (tail e) (tail s))))))

(check= (decrypt '() '()) '())
(check= (decrypt '((1 1 1 1 1)) '((1 1 1 1 1))) '(#\A))
(check= (decrypt '((1 1 1 1 1) (1 1 1 1 0) (1 1 1 0 1)) '((1 1 1 1 1) (1 1 1 1 1) (1 1 1 1 1))) '(#\A #\B #\C))
(check= (decrypt '() '((0 0 0 0 0))) '())
(check= (decrypt '((1 1 1 1 1) (1 1 1 1 0) (1 1 1 0 1)) '((1 1 1 1 1) (1 1 1 1 1) (1 1 1 1 1) (1 1 1 1 1))) '(#\A #\B #\C))

;; Question 16
;;
;; Write a PROPERTY to make sure ENCRYPT and DECRYPT work as expected:
;; if we encrypt lochar m (the message) with lobv5 s (the secret),
;; and then use s to decrypt that, we get the original message back.
;; Add any other hypotheses you may need.

"Property 8"
(property (m :lochar s :lobv5)
  :hyps (>= (len s) (len m))
  (== (decrypt (encrypt m s) s) m))

;; Question 17
;; 
;; Write a PROPERTY to see that one-time pads provide "perfect" secrecy:
;; if we have an lobv5, e, which is an encrypted message, then for every
;; lochar m, an arbitrary message of the same length, there is some
;; secret s that when used to decode e gives us m. That is, without the
;; secret, we have no information about the contents of the message.
;; We haven't seen how to say "there exists", so instead, construct
;; the secret using existing functions.
"Property 9"
(property (e :lobv5 m :lochar)
  :hyps (= (len e) (len m))
  (let ((s (encrypt m e)))
    (== (decrypt e s) m)))

;; The above shows that even though we know that the hostile actors
;; are using one-time pads and that each sequence of 5 bits
;; corresponds to a character, then without the secret, we cannot
;; determine what the message says.
;; 
;; However... all hope is not lost, if we are the codebreakers.  Human
;; intelligence tells us that the hostile actors did not take CS 2800,
;; and weren't trained to think carefully about the correctness of
;; their code, so they did not recognize that their secret should not
;; be reused. What they are doing is using the same 5 bit secret to
;; encrypt all the characters in their message.
;;
;; Human intelligence tried, but was not able to determine what the
;; secret is, so you have to figure out how to break their encyption.

;; To make it easier to read the messages, we will convert them to
;; strings. Here is an example of how you can do that in ACL2s.

(coerce '(#\H #\e #\l #\l #\o #\, #\space #\w #\o #\r #\l #\d #\.)
    'string)

;; Question 19
;;
;; Here's the plan for breaking the encryption. You are going to
;; generate all possible secret keys (there are 2^5=32 of
;; them). Luckily, you already wrote code to do that. Then, you will
;; decode *SECRET-MESSAGE* with each of these keys. To do that, you
;; will create a list containing (LEN *SECRET-MESSAGE*) copies of the
;; potential secret and use it to decrypt the message. When you do
;; this, you'll produce gibberish 31 times, but *one* of your decrypts
;; will make sense.

;; Define GAME-OVER, a function that decrypts *SECRET-MESSAGE* using
;; all possible values for the secret key. It should return a list of
;; 32 strings. Hint: define a helper function.

(defdata lostring (listof string))

(definec game-over/aux (keys :lobv5) :lostring
  (match keys
    (nil '())
    (& (cons (coerce (decrypt *secret-message* (n-copies (head keys) (len *secret-message*))) 'string) (game-over/aux (tail keys))))))

(definec game-over () :lostring
  (game-over/aux *bv5-values*))


;; Question 20
;;
;; Well, what is the secret message?  (The answer is the one string
;; out of the 32 strings returned by game-over that makes any sense.)

(defconst *the-secret-message-is*
  "THE QUICK BROWN FOX JUMPED OVER THE LAZY DOG'S BACK")

;; This is a historically relevant message. Look it up and explain
;; why it is historically relevant in the string below.

"
It's relevant because it contains all letters in the English alphabet
"

;; Extra Credit 
;;
;; It is easy enough to look at all of the potential secret messages,
;; since there are only 32 of them, in order to figure out what the
;; most likely message is. But, you are a perfectionist and came up
;; with a plan to facilitate the process. Your plan is to order the
;; messages by counting the number of spaces, E's and T's in the
;; message since these are the most common characters in English text,
;; statistically speaking. So, define a function that returns the list
;; generated by game-over, but ordered as described above.  This
;; requires that you do some investigation, using the ACL2s
;; documentation, to figure out how to access characters in strings,
;; etc. You can use any ACL2s functions you want here, not just the
;; ones in the reference guide.

(definec count-common-chars (s :string) :int
  (+ (count #\E s) (count #\T s) (count #\Space s)))

(check= (count-common-chars "THIS IS A SENTENCE") 8)
(check= (count-common-chars "ASDFSADFGSDFSA") 0)

(definec compare-common-chars (x :string y :string) :bool
  (< (count-common-chars y) (count-common-chars x)))

(check (compare-common-chars "THIS IS A SENTENCE" "ET E"))

(definec first-n (l :tl n :nat) :tl
  (if (lendp l) nil
    (if (= n 0) nil
      (cons (head l) (first-n (tail l) (1- n))))))

(check= (first-n '(1 2 3 4 5 6 7 8 9) 3) '(1 2 3))


(definec exclude-first-n (l :tl n :nat) :tl
  (if (or (= n 0) (lendp l)) l
    (exclude-first-n (tail l) (1- n))))

(check= (exclude-first-n '(1 2 3 4 5 6 7 8 9) 3) '(4 5 6 7 8 9))

(definec cc-merge (a :lostring b :lostring) :tl
  (cond
   ((lendp a) b)
   ((lendp b) a)
   ((compare-common-chars (first a) (first b)) (cons (first a) (cc-merge (rest a) b)))
   (t (cons (first b) (cc-merge a (rest b))))))

(check= (cc-merge '("EEEEEE" "EEE" "E") '("EEEEE" "EEEE" "EE")) '("EEEEEE" "EEEEE" "EEEE" "EEE" "EE" "E"))

(definec cc-merge-sort (l :lostring) :tl
  (let* ((l-len (len l))
         (mid (floor l-len 2)))
    (match l-len
      (0 '())
      (1 l)
      (& (cc-merge (cc-merge-sort (first-n l mid)) (cc-merge-sort (exclude-first-n l mid)))))))

(check= (cc-merge-sort '("E" "EEEEE" "EEE" "EEEEEE" "EEEE" "EE")) '("EEEEEE" "EEEEE" "EEEE" "EEE" "EE" "E"))
(check= *the-secret-message-is* (head (cc-merge-sort (game-over))))