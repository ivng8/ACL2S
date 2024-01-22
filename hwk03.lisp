#|

CS 2800 Homework 3 - Fall 2023

 - Due on Tuesday, Oct 3 by 11:00 pm.

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

 In this assignment, you will use ACL2s to build an executable model
 of how the virtual memory hardware in a modern CPU (the RISC-V) works. 
 You'll need to read a bit of the *actual* documentation for the CPU 
 architecture (we'll tell you where to find it) to understand what
 you are modelling. Note that this kind of task is part of what goes
 on at actual hardware-design companies, in order to verify that the
 designed chip does what the specification says it ought to do.

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

     (definec check= (x :all y :all) :bool
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
     you have 100% expression coverage (read the Lecture Notes, as we
     did not go over this in class and you are expected to read about
     it on your own).  You can use whatever tests we provide and your
     contract-based tests to achieve expression coverage, e.g., if the
     union of the tests we gave you and your contract-based tests
     provide 100% expression coverage, there is nothing left to do.

 (3) Contract-based testing and expression coverage are the minimal
     testing requirements.  Feel free to add other tests as you see
     fit that capture interesing aspects of the function.

 (4) For all functions where you are responsible for at least some
     part of the definition, add at least two interesting property
     forms. The intent here is to reinforce property-based testing.

 You can use any types, functions and macros listed on the ACL2s
 Language Reference (from class Webpage, click on "Lectures and Notes"
 and then on "ACL2s Language Reference"). 

 Since we don't know how to control the theorem prover, we will allow
 you to simplify the interaction with ACL2s somewhat.

 Instead of requiring ACL2s to prove termination and contracts, we
 allow ACL2s to proceed even if a proof fails.  However, if a
 counterexample is found, ACL2s will report it.  See the lecture notes
 for more information.  This is achieved using the following
 directives. You can add any of these directives to any point in your
 file, if the need arises. 

 (set-defunc-termination-strictp nil)
 (set-defunc-function-contract-strictp nil)
 (set-defunc-body-contracts-strictp nil)
 (set-defunc-generalize-contract-thm nil)

 You can turn this behavior back on by replacing nil by t. Again,
 add such forms to your file as you see fit. The stricter ACL2s is,
 the more checking it can do for you.

 You can also tell ACL2s to not try proving properties, unless by
 adding ":proofs? nil" to properties, as discussed in class, whenever
 needed.

 You can also tell ACL2s to not check contracts by using
 ":check-contracts? nil". In more detail, if ACL2s does not prove
 function contracts when defining functions, then properties
 will generate errors if it then tries to reason about the contracts
 of these functions. In such cases, add the
 :check-contracts? keyword command. Here's an example.

 (property (x :all)
   :check-contracts? nil
   (== (car x) (car x)))

|#

#|

 Part 1: Fun with bitvectors

 Here are data some data definitions for bits and bitvectors.

|#

(defdata bit (oneof 0 1))
(defdata bitvector (listof bit))

; Here are some examples.

(check (bitvectorp '(0 1 0 0 1 0 0)))
(check (! (bitvectorp '(1 a 1 0))))          
(check (bitvectorp nil))

#|

 We can use bitvectors to represent natural numbers as follows.
 The list

 (1 0 0)

 corresponds to the number 4 because the last 0 is the "low-order"
 bit of the number which means it corresponds to 2^0=1 if the bit is 1
 and 0 otherwise. The next bit corresponds to 2^1=2 if 1 and 0
 otherwise and so on. So the above number is:

 0 + 0 + 2^2 = 4.

 As another example, 31 is

 (1 1 1 1 1)

 31 can also be represented as follows

 (0 0 1 1 1 1 1)

 and we can add as many 0's at the front of the list as we like. 

 Below we provide the function n-to-bv, which given a natural number,
 returns a bitvector list of minimal length, corresponding to that
 number.

|#

(definec n-to-bv/slow (n :nat) :bitvector
  (match n
    (0 '())
    (& (app (n-to-bv/slow (floor n 2))
        (list (mod n 2))))))

(check= (n-to-bv/slow 0)  '())
(check= (n-to-bv/slow 1)  '(1))
(check= (n-to-bv/slow 12) '(1 1 0 0))
(check= (n-to-bv/slow 13) '(1 1 0 1))

;; What is the complexity of n-to-bv/slow in terms of the number of
;; bits used to represent n? You can assume that floor and mod take
;; constant time.  Uncomment the correct option.

; (defconst *cmplxty* "constant")
; (defconst *cmplxty* "linear")
(defconst *cmplxty* "quadratic")
; (defconst *cmplxty* "cubic")
; (defconst *cmplxty* "exponential")

;; Define a linear complexity (in terms of the number of bits used to
;; represent n) function, n-to-bv. Start by defining a helper function
;; that uses an accumulator (hint: use the accumulator to avoid using
;; app).
(definec n-to-bv/aux (n :nat bv :bitvector) :bitvector
  (match n
    (0 bv)
    (& (n-to-bv/aux (floor n 2) (cons (mod n 2) bv)))))

(check= (n-to-bv/aux 0  '(1 0 1 0)) '(  1 0 1 0))
(check= (n-to-bv/aux 1  '(1 0 1 0)) '(1 1 0 1 0))

(check= (n-to-bv/aux 12 '(1 0 1 0))
    '(1 1 0 0   1 0 1 0))

;; Make sure that the following property is satisfied.
(property (msbs :nat lsb :bit bv :bitvector)
  :proofs? nil
  (let ((n (+ (* 2 msbs) lsb)))
    (== (n-to-bv/aux n bv)
    (if (zp n)
            bv
      (n-to-bv/aux msbs (cons lsb bv))))))

;; Don't forget to add two intersting properties (see instructions).
;; You have to do this for ALL the functions where you provide some
;; part of the definition.

(definec n-to-bv (n :nat) :bitvector
  (n-to-bv/aux n '()))

(check= (n-to-bv 0)  '())
(check= (n-to-bv 6)  '(1 1 0))
(check= (n-to-bv 10) '(1 0 1 0))
  

;;; Make sure that the following property is satisfied.

(property n-to-bv/equiv (n :nat)
  :proofs? nil
  (== (n-to-bv/slow n)
      (n-to-bv n)))

#|

 Define the function bv-to-n that given a bitvector, returns the
 corresponding natural number. Start with a helper function that uses
 an accumulator.

|#

(definec bv-to-n/aux (bv :bitvector msbs :nat) :nat
  (match bv
    (nil msbs)
    (& (bv-to-n/aux (tail bv) (+ (* 2 msbs) (head bv))))))

(check= (bv-to-n/aux '(1 1 0) 1000) 8006)
(check= (bv-to-n/aux '()      1000) 1000)

(property (n :nat bv :bitvector)
  :proofs? nil
  (= (bv-to-n/aux (n-to-bv n) 0) n))

(definec bv-to-n (bv :bitvector) :nat
  (bv-to-n/aux bv 0))

(check= (bv-to-n '(1 0 1 0)) 10)  
(check= (bv-to-n '(1 1 1)) 7) 
(check= (bv-to-n '(1 0 0)) 4) 
(check= (bv-to-n '(1 1 1 1 1)) 31) 
(check= (bv-to-n ()) 0)

; State the property that bv-to-n is the inverse of n-to-bv. That is,
; given a natural number n, if we convert it to a bitvector and then
; back to a number, we get n.

"Property 11"

(property (n :nat)
  :proofs? nil
  (= (bv-to-n (n-to-bv n)) n))

; We can't prove that n-to-bv is the inverse of bv-to-n. Show this by
; constructing a value that passes the following check form.

(check (let ((bv '(0)))
         (!= (n-to-bv (bv-to-n bv))
             bv)))

;;; We can prove that for some bitvectors, n-to-bv is the inverse of
;;; bv-to-n. Construct such a bv1 (not necessarily equal to bv) in the
;;; following property. Try to make bv1 as general as possible.

"Property 12"

(property (bv :bitvector)
  :proofs? nil
  (let ((bv1 (match bv
               ((0 . &) '())
               (& bv))))
    (== bv1 (n-to-bv (bv-to-n bv1)))))

; But, there is a sense in which n-to-bv is the inverse of bv-to-n.
; This should work as long as there are no leading 0's, so let's write
; a function to get rid of leading 0's.

(definec remove-leading-0s (bv :bitvector) :bitvector
  (match bv
    ((0 . &) (remove-leading-0s (tail bv)))
    (& bv)))

(check= (remove-leading-0s '(0 0 0 0 1 0 1)) '(1 0 1))

; State the property that n-to-bv returns a bitvector with no leading
; 0's, using the function remove-leading-0s. Hint applying
; remove-leading-0s to n-to-bv doesn't do anything.

"Property 13"

(property (n :nat)
  :proofs? nil
  (let ((bv (n-to-bv n)))
    (== bv (remove-leading-0s bv))))

"Property 14"

;;; Here's a spec for remove-leading-0s
(property (bv :bitvector)
  (let ((shortened-bv (remove-leading-0s bv)))
    (and (or (lendp shortened-bv)
         (= 1 (first shortened-bv)))
     (= (bv-to-n bv) (bv-to-n shortened-bv)))))
       
; State the property that n-to-bv is the inverse of bv-to-n, modulo 
; leading 0's, i.e., given a bitvector bv, if we convert it to a
; natural number and then convert that back to a bitvector, we get bv
; with the leading 0s removed.

"Property 15"

(property (bv :bitvector)
  :proofs? nil
  (== (remove-leading-0s bv) (n-to-bv (bv-to-n bv))))


#|

 Part 2: Fun with Virtual Memory Addressing

 Computer processes require access to memory which contains
 instructions and data to be run. Since memory is a shared resource,
 there needs to be a way for processes to utilize it efficiently. An
 early solution was to reload the memory each time a new
 process (program) needed to run.

 A better alternative is Virtual Memory, first implemented on an Atlas
 computer at the University of Manchester in the early 60s. Virtual
 memory systems present an illusion of a large, contiguous and
 exclusive memory for each running process. How? By letting processes
 work with virtual addresses, and mapping those virtual addresses to
 physical addresses available on the machine, as shown in the
 following figure:

                                             Main Memory
                                           ┌─────────────┐
                                           │  P5 mem     │
                                           ├─────────────┤
                                           │  P6 mem     │
                                           ├─────────────┤
                                    ┌─────►│  P1 mem     │
                                    ▲      │             │
                                    │      ├─────────────┤
Virtual Memory for 1 process (P1)   │      │             │
     ┌──────────────┐               │      ├─────────────┤
     │              │               │      │             │
     │              ├───────────────┘      │  P10 mem    │
     ├──────────────┤                      ├─────────────┤
     │              │                      │             │
     │              ├─────────────────────►│  P1 mem     │
     ├──────────────┤                      ├─────────────┤
     │              │                      │             │
     │              │                      │             │
     │              │                      ├─────────────┤
     │              ├─────────────────────►│  P1 mem     │
     │              │                      │             │
     ├──────────────┤                      │             │
     │              │                      │             │
     │              │                      ├─────────────┤
     │              ├───────────────┐      │             │
     └──────────────┘               │      ├─────────────┤
                                    │      │             │
                                    │      ├─────────────┤
                                    │      │             │
                                    │      ├─────────────┤
                                    │      │             │
                                    ▼─────►│  P1 mem     │
                                           └─────────────┘

 This abstraction allows us to think of virtual memories as
 mappings. A memory management unit (MMU), maps the addresses from
 each program into separate areas in physical memory. Most modern
 operating systems (OS) work in concert with the MMU to provide
 virtual memory support.

 In this part, we are going to model a memory management unit (MMU)
 running on a RISC-V sv32 Architecture machine. More details about
 this machine can be found here:
 https://riscv.org/wp-content/uploads/2016/11/riscv-privileged-v1.9.1.pdf

 The MMU is responsible for translating virtual addresses to physical
 addresses.

 In this homework, we will consider the RISC-V based sv32 machine and
 assume word-addressable memory. A word-addressable memory is one
 where each address can be used to fetch a word of memory (4
 bytes). Contrast this with a byte-addressable memory, where the
 lowest granularity of memory access is a single byte.

 In sv32, memory is divided into pages of size 2^12 bytes.  Consider
 that we have 2^34 bytes of addressable memory. Then, there are
 2^(34-12) = 2^22 pages. In order to have a mapping, the first stage
 page table will require 2^22 page table entries (PTEs). If each entry
 is the size of a word, the total size taken by the page table amounts
 to 2^22 * 2^2 = 16MB.

 This is too big, especially when considering that this page table
 will reside in the main memory. We can improve space usage by having
 multi-level page tables. In a 2-stage page table, the PTE in the
 first page table points to another page table. A PTE in the second
 page table will then point to the actual physical address. Let's
 calculate the space usage. Let the first level page table be a single
 page, and hence it will consist of 2^12 Bytes / 2^2 Bytes = 2^10
 entries, occupying 4KB of space. These 2^10 entries point to 2^10
 second stage page tables, but we need only one of them, which will
 contain the PTE that points to the actual physical address. The size
 of the second stage page table can be limited to a single page as
 well, hence its size = 4KB. Hence, the total memory required for a
 2-stage page table will be 8KB.

|#

;; For the Sv32 architecture, we have word length = 32 bits
(defconst *WORD-LENGTH* 32)

;; Virtual Memory is 32 bit addressable.
(defdata u32 (range integer (0 <= _ < (expt 2 *WORD-LENGTH*))))

;; Physical Memory is 34 bit addressable.
(defconst *WORD+2* (+ *WORD-LENGTH* 2))

(defdata u34 (range integer (0 <= _ < (expt 2 *WORD+2*))))

;; The following form proves that u32 is a subtype of u34.
(defdata-subtype u32 u34)

;; bitvectors of length upto *WORD-LENGTH* represent values of type u32.
(property bv-len-u32 (bv :bitvector)
  :proofs? nil
  :hyps (<= (len bv) *WORD-LENGTH*)
  (u32p (bv-to-n bv)))

;; bitvectors of length upto *WORD+2* represent values of type u34.
(property bv-len-u34 (bv :bitvector)
  :proofs? nil
  :hyps (<= (len bv) *WORD+2*)
  (u34p (bv-to-n bv)))

;; We model a word addressable memory as a map. A map is a dictionary
;; (represented as a list of pairs of keys and values in ACL2s) with sorted
;; keys. In our memory, we use physical memory address locations (unsigned 34
;; bits) as keys while the values are word size (*WORD-LENGTH* bit) values.
(defdata memory (map u34 u32))

;; Here are some checks for our map:
;; memory can't have unsorted (in ascending order) keys
(check (! (memoryp '((1024 . 42)
                     (1020 . 255)))))

;; address can not point to a non-word value. 
(check (! (memoryp '((1024 . "X")))))

;; We can get/set values of keys in a map using the mget/mset functions.
;;; mset sets a value for some key. It has the following signature:
;;; (mset <key> <newval> <map>) -> <map>
;;; mget retrieves the value of a given key in a map. If said value is not
;;; found it returns nil
;;; (mget <key> <map>) -> (or <val> nil)

(check= (let ((mem '((1024 . 1)
                     (1025 . 32)
                     (1032 . 255))))
          (mget 1025 mem))
        32)

(check= (let* ((mem '((1024 . 1)
                      (1025 . 32)
                      (1032 . 255)))
               (updated-mem (mset 1024 2 mem)))
          (list (mget 1024 mem)
                (mget 1024 updated-mem)))
        '(1 2))

;; null is a recognizer for nil (another one without a trailing p).
;; mget on an unavailable memory location evaluates to nil
(check (null
        (let ((mem '((1024 . 1)
                     (1025 . 32)
                     (1032 . 255))))
          (mget 1026 mem))))

;; Not all of the memory is accessible, and attempting to load the
;; inaccessible memory may cause an error called ACCESS FAULT (AF).
(defdata access-fault 'AF)

;; So the result of a memory access can either be a 32bit value or access-fault.

(defdata mem-ret (or u32 access-fault))

;; Complete the memory lookup function below 
(definec memory-lookup (addr :u34 m :memory) :mem-ret
  (let ((memaddr (mget addr m)))
    (match memaddr
      (nil 'AF)
      (& memaddr))))

(check= (let ((mem '((1024 . 1)
                     (1025 . 64)
                     (1032 . 255))))
          (memory-lookup 1024 mem))
        1)

(check= (let ((mem '((1024 . 1)
                     (1025 . 64)
                     (1032 . 255))))
          (memory-lookup 1026 mem))
        'AF)

;; Sv32 implementations support a 32-bit virtual address space, divided into 4
;; KB pages. We need a page table that maps virtual memory addresses (used by
;; processes) to physical memory addresses.

;; A Page Table Entry (PTE) in a table looks like this:
;; 31     20 19      10 9      8 7 6 5 4 3 2 1 0   <--- bit indices
;;|  PPN[1] |  PPN[0]  |   RSW  |D|A|G|U|X|W|R|V|  <--- fields

;; PTE is 4 bytes in size
(defconst *PTESIZE* 4)

;; A Page is 4096 bytes in size
(defconst *PAGESIZE* 4096)

;; How many PTEs are in a page?
(defconst *num-pte-entries* 1024)

;; A page-table entry (PTE) is "valid" if its V bit is set to 1. (See diagram
;; above to determine which of the bits is the V bit.)  Write a predicate
;; valid-ptep that takes a PTE (represented as u32, not as a bit vector) and
;; determines if it is valid.

(definec valid-ptep (pte :u32) :boolean
  (= (mod pte 2) 1))

(check (valid-ptep 1))
(check (valid-ptep 43))
(check (! (valid-ptep 0)))

;; Since we are constructing a 2 stage page-table, we need to be able to
;; determine whether a valid PTE points to a memory address or the next level page
;; table. A valid PTE is called a leaf-pte if atleast one of R, W or X bits is
;; set to 1.  Write a function leaf-ptep that determines if a PTE points to an
;; actual memory address

(definec leaf-ptep (x :u32) :boolean
  :ic (valid-ptep x)
  (or (= (mod x 4) 3)
      (= (mod x 8) 5)
      (= (mod x 16) 9)))

(check (! (leaf-ptep 1)))
(check (leaf-ptep 3))


;; Define the function bitfield to extract bits from n, starting at
;; bit position lo and going up to, but not including bit position hi.
;; n, lo and hi are natural numbers.
;;
;; To help you in testing the code, we note that in ACL2s, you can
;; write numbers in binary. For example, the number 14 can be written
;; in binary as #b1110. So, (bitfield 14 0 2) should return the two
;; low-order bits of 14, which are #b10 (in binary) and 2 in our
;; normal decimal notation.

(definec bitfield (n lo hi :nat) :nat
  :ic (<= lo hi)
  (mod (floor n (expt 2 lo)) (expt 2 (- hi lo))))
  
(check= (bitfield #b1110 0 2) #b10) 
(check= (bitfield #b1110 1 4) #b111) 
(check= (bitfield #b1110 0 4) #b1110)

(check= (bitfield #b11010 1 4) #b101) 

;; A virtual address looks like the following
;; 31     22 21      12 11      0   
;;|  VPN[1] |  VPN[0]  | offset |   
;; That is:
;; - offset: The low 12 bits say where the addressed byte occurs in
;;           its 4KB page.
;; - VPN[0]: The next 10 bits (bits 12 through 21) give the Virtual Page
;;           Number in page table 0.
;; - VPN[1]: The last 10 bits (bits 22 through 31) give the Virtual Page
;;           Number in page table 1.
;; We do the lookup by
;; - first indexing into page table 1 with VPN[1] to get page table 0,
;; - then indexing into that with VPN[0] to get the address of a physical page,
;; - then indexing into that with the offset.
;; ...if we run into a dead-end (an invalid entry), then we are addressing
;; a virtual page that does *not* have a corresponding physical page in
;; RAM -- that's a "page fault," and the operating system will have to
;; - stop the process,
;; - load the missing page in from the "swap area" on a hard drive
;;   into an unused page of physical memory,
;; - Fix up the page tables to point to the chosen physical page, and finally
;; - resume the process and retry the memory operation.

;; Write a function va->vpni, which given a virtual address va and 0 <= i <= 1,
;; returns vpn[i], a Virtual Page Number (nat) in a page table ,which is a
;; natural number. Recall that VPN[0] and VPN[1] are just bit fields in
;; VA. (Again, see the diagram for a virtual address)

(definec va->vpni (va :u32 i :nat) :nat
  :ic (or (= 0 i) (= 1 i))
  (match i
    (0 (bitfield va 12 22))
    (1 (bitfield va 22 32))))

(check= (va->vpni 1 0) 0)
(check= (va->vpni 12623875 1) 3)
(check= (va->vpni 12623875 0) 10)

;; A PTE has its own ppn fields, which store the page number in memory where
;; page tables are stored. 
;; Write a function pte->ppni, which given a PTE pte and 0 <= i <= 1,
;; returns ppn[i], a nat. (Again, see the diagram for a PTE below)

(definec pte->ppni (pte :u32 i :nat) :nat
  :ic (or (= 0 i) (= 1 i))
  (match i
    (0 (bitfield pte 10 20))
    (1 (bitfield pte 20 32))))

;;31      20 19      10 9      8 7 6 5 4 3 2 1 0
;;|  PPN[1] |  PPN[0]  |   RSW  |D|A|G|U|X|W|R|V|

(check= (pte->ppni (bv-to-n '(0 0 0 0 0 0 0 0 0 0 0 1 ;; ppn[1]
                                0 0 0 0 0 0 0 0 1 1
                                0 0 0 0 0 0 0 0 0 1))
                   1)
        1)

(check= (pte->ppni (bv-to-n '(0 0 0 0 0 0 0 0 0 0 0 1
                                0 0 0 0 0 0 0 0 1 1   ;; ppn[0]
                                0 0 0 0 0 0 0 0 0 1))
                   0)
        3)


#|

Here is a graphical presentation of 2-stage virtual address (va)
to physical address (pa) translation.

                root.ppn                               a := pte.ppn[1] * PAGESIZE
                ┌──────────────┐           ▲─────────►┌─────────────┐
va     ────────►│              │           │          │             │
                │              │           │          │             │
                ├──────────────┤           │          ├─────────────┤
                │              │           │          │             │
                │              │           │          │             │
                ├──────────────┤           │          ├─────────────┤
                │              │           │   vpn[0] │   leaf      ├──────────► pa
                │              │           │          │             │
                ├──────────────┤           │          ├─────────────┤
                │              │           │          │             │
         vpn[1] │   not leaf   ├──────────►┘          │             │
                ├──────────────┤                      ├─────────────┤
                │              │                      │             │
                ├──────────────┤                      ├─────────────┤
                │              │                      │             │
                └──────────────┘                      └─────────────┘

|#


;; We have a simplified Algorithm 4.3.2 (Virtual Address Translation Process)
;; given in https://riscv.org/wp-content/uploads/2016/11/riscv-privileged-v1.9.1.pdf
;; Assume that the only page size possible is (expt 2 12) bytes. So, a 32 bit
;; virtual address will be translated to a 34 bit physical address only after
;; looking up two page tables.

;; Following is the simplified Algorithm you need to write:
;; 1. Let pte be the value of the PTE at address a+va.vpn[i]×PTESIZE.
;; 2. If no pte at this address in memory is found, return Access Fault.
;; 3. If pte is not valid, return Access Fault.
;; 4. If pte is a leaf-pte at level i = 1, return Access Fault.
;; 5. Otherwise, this PTE is a pointer to the next level of the page
;; table. Recurse with  a := pte.ppn[i] * PAGESIZE, and i := 1-1.
;; 6. If pte is not a leaf at level i = 0, return Access Fault.
;; 7. Otherwise, calculate the Physical Address as follows : Append the Most
;; Significant 22 bits (PPN bits) from the leaf PTE to the Least Significant 12
;; bits (Offset) of the va to get a 34 bit physical address.

;; 2 level page walk
(defconst *LEVELS* 2)

;; Address of the first level Page Table is stored in the SATP register
(defconst *SATP.PPN* 24)

;; Translating a va to pa should return either a u34 or an Access Fault
(defdata pa-ret (v u34 access-fault))

;; Based on the algorithm provided, fill in the blanks in the page walk algorithm below.
(definec va-to-pa-helper (va :u32 i :nat a :u34 m :memory) :pa-ret
  :ic (or (= 0 i) (= 1 i))
  :function-contract-strictp nil
  :body-contracts-strictp nil
  (let* ((vpni (va->vpni va i))
         (pte-addr (+ a (* vpni *PTESIZE*)))
         (pte (memory-lookup pte-addr m)))
    (cond ((== pte 'AF) 'AF)
          ((! (valid-ptep pte)) 'AF)
          ((! (leaf-ptep pte))
           (match i
             (1 (va-to-pa-helper va (1- i) (* (pte->ppni pte i) *PAGESIZE*) m))
             (0 'AF))) ;; can't be at level 0 and not be leaf
          (t (match i
               (1 'AF) ;; we don't have leaf PTEs at level 1
               (0 (+ (* (bitfield pte 10 32) (expt 2 12)) (bitfield va 0 12))))))))

(defconst *mem-offset* 24)
(defconst *vpn-offset* #b110)
(defconst *vpn-0* #b101)
(defconst *vpn-1* #b10)
(defconst *ppn-1* 7)
(defconst *pte-addr-1* (+ *mem-offset* (* *vpn-1* *PTESIZE*)))
(defconst *pte-addr-0* (+ (* *ppn-1* *PAGESIZE*) (* *vpn-0* *PTESIZE*)))
(defconst *va* (+ (* *vpn-1* (expt 2 22)) (* *vpn-0* (expt 2 12)) *vpn-offset*))
(defconst *leaf-suffix* #b1001)
(defconst *valid-suffix* #b1)
(defconst *pte-1* (+ (* *ppn-1* (expt 2 20)) *valid-suffix*))
(defconst *pte-0/mib* #b1010011101)
(defconst *pte-0* (+ (* *pte-0/mib* (expt 2 10)) *leaf-suffix*))
(defconst *target* (+ (* *pte-0/mib* (expt 2 12)) *vpn-offset*))
(defconst *memory* (mset *pte-addr-1* *pte-1* (mset *pte-addr-0* *pte-0* '((0 . 0)))))

(check= (va-to-pa-helper *va* 1 *mem-offset* *memory*) *target*)

(definec va-to-pa (va :u32 m :memory) :pa-ret
  :function-contract-strictp nil
  :body-contracts-strictp nil
  (va-to-pa-helper va (1- *LEVELS*) *SATP.PPN* m))

;; Test
(defconst *Mem*
  '((36 . 10488833)
    (40 . 10498833)
    (44 . 11498833)
    (48 . 11598853)
    (52 . 11688853)
    (41000 . 1084361731)
    (41100 . 1084362731)
    (41200 . 1084363731)
    (41300 . 1084364731)
    (44400 . 1084365731)
    (4337446915 . 842543152)
    (4337447015 . 832543152)
    (4337447115 . 836943152)))

(check= (va-to-pa-helper 12623875 1 24 *Mem*) 4337446915)
(check= (va-to-pa-helper 12623975 1 24 *Mem*) 4337447015)

; Make sure *pt-walk-res* is correct. It should be one of the values
; an address in *Mem* maps to, i.e., (va-to-pa-helper ...) should
; return an address appearing in *Mem*.
(defconst *pt-walk-res* (memory-lookup (va-to-pa 12623875 *Mem*) *Mem*))
