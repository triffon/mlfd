;; Unbounded (Infinite) Pigeonhole Principle, adapted by Hernest from
;; Trifonov's incomplete solution. We here follow the methodic approach,
;; exposed in Trifonov's PhD thesis, but with the optimization brought
;; by the Hernest-Trifonov modal Dialectica, impnc rather than allnc
(load "C:\\minlog\\initDan.scm") ;; init for Windows pathnames
(load "C:\\minlog\\etsmdA.scm") ;; modal Dialectica extraction module
(set! COMENTARIU #f)
(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "list.scm")
(set! COMMENT-FLAG #f)
(av "b" (py "nat")) ;; no "q" "r" 
(av "f" (py "nat=>nat"))
(av "l" (py "list nat"))
; there are at most k colors on the tape f
(define FC
  (pf " all n. f n < k "))
(define notFC
  (pf " (all n. f n < k) -> F "))
; the color b occurs infinitely often in f
(define INFCb
  (pf "all n. all m (n <= m -> f m = b -> F) -> F"))
(define notINFC
  (pf "all b. (all n. all m (n <= m -> f m = b -> F) -> F) -> F"))
; infinite pigeon hole principle
(define IPH (make-all (pv "f") (make-imp notINFC notFC)))
; there is a list of length n containing different indices
; of occurrence of the same color
(define STLZ (pf "(all l . Lh l = Succ n ->
        (all m . m < n -> (Succ m thof l) < (m thof l)) -->
        (all m . m < n -> f(m thof l) = f(Succ m thof l)) --> F) -> F "))
(define notSTLZ (pf "all l . Lh l = Succ n ->
        (all m . m < n -> (Succ m thof l) < (m thof l)) -->
        (all m . m < n -> f(m thof l) = f(Succ m thof l)) --> F "))
(define STLZb (pf "all n. (all l . Lh l = Succ n ->
        (all m . m < n -> (Succ m thof l) < (m thof l)) -->
        (all m . m < Succ n -> f(m thof l) = b) --> F) -> F "))
(define Goal (mk-imp INFCb STLZb))
(define FinalGoal (mk-all (pv "k") (pv "n") (pv "f") (mk-imp notSTLZ notFC)))

(add-rewrite-rule (pt "NegConst (NegConst boole^)") (pt "boole^"))
(add-rewrite-rule (pt "ImpConst boole^ False") (pt "NegConst boole^"))

(set-goal IPH)
(ind) ; induction on the number of colors
(strip) ; (search) produces a proof with free variable `n'
(use 2 (pt "0")) ; this is a bug-fix for program extraction
; simple base case, now to the step case
(assume "k" "IH" "f" "NotINFC" "FCSucck")
(use "NotINFC" (pt "k"))
(assume "n" "nIsLastForK")
(use "IH" (pt "[n1]f(n max n1)"))
;-------------------------------------
(ng)
(assume "b" "u")
(use "NotINFC" (pt "b"))
(assume "n1" "u1")
(use "u" (pt "n1"))
(assume "m" "n1<=m" "f(n max m)=b")
(use "u1" (pt "n max m"))
(use "NatLeTrans" (pt "m"))
(use "n1<=m")
(use "NatMaxUB2")
(use "f(n max m)=b")
;---------------------------------------
(ng)
(assume "n1")
(use "NatLtSuccCases" (pt "f(n max n1)") (pt "k"))
(use "FCSucck")
(search)
(assume "f(n max n1)=k")
(use "Efq")
(use "nIsLastForK" (pt "n max n1"))
(use "NatMaxUB1")
(use "f(n max n1)=k")
;-------------------------------------
(save "IPH")
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;---------------------------------------------
(set! COMMENT-FLAG #t)
(set! ETSMD-LET-ENABLED #t)
(define extr_term-iph
  (proof-to-extracted-md-term
   (np (expand-theorems (theorem-name-to-proof "IPH")))))
;; (av "y" (py "nat@@(nat=>nat)"))
;; (av "x" (py "(nat=>(nat=>nat)=>nat)"))
;; (av "Ta"(py "(nat=>(nat=>nat)=>nat)=>nat"))
;; (av "TaG"(py "(nat=>(nat=>nat)=>nat)=>nat@@(nat=>nat)"))
;; (av "TaTaG" (py "((nat=>(nat=>nat)=>nat)=>nat)@@((nat=>(nat=>nat)=>nat)=>nat@@(nat=>nat))"))
;; (av "BiG" (py "(nat=>nat)=>((nat=>(nat=>nat)=>nat)=>nat)@@((nat=>(nat=>nat)=>nat)=>nat@@(nat=>nat))"))
(define nterm-iph (nt extr_term-iph))
; (pp nterm-iph) ; 115 lines
(add-program-constant "mdIPH" (term-to-type nterm-iph))
(define (animate-iph)
  (add-computation-rule "mdIPH k f"
    (nt (mk-term-in-app-form nterm-iph (pt "k") (pt "f")))))
(define (deanimate-iph)
  (remove-computation-rules-for (pt "mdIPH k f")))
(set! COMMENT-FLAG #f)
;---------------------------------------------
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(set-goal Goal)
(assume "f" "b" "Infb")
(ind) ; base case 
(assume "NotSTLZero")
(use "Infb" (pt "0"))
(assume "m" "0<=m" "f m=b")
(use "NotSTLZero" (pt "m:"))
(use "Truth-Axiom")
(ng)
(assume "m1")
(use "Efq")
(cases)
(strip)
(use "f m=b")
(ng)
(assume "m1")
(use "Efq") ; step case
(assume "n" "IH" "NotSTLZ")
(use "IH")
(cases)
(ng)
(use "Efq")
(assume "m" "l")
(assume "Lh l=n")
(assume "lIsDecreasing")
(assume "lIsMonochrome")
(use "Infb" (pt "Succ m"))
(assume "m1" "m<m1" "f m1=b")
(use "NotSTLZ" (pt "m1::m::l"))
(use "Lh l=n")
(cases)
(assume "0 < Succ n")
(use "NatSuccLeToLt")
(use "m<m1")
(use "lIsDecreasing")
(cases)
(assume "0 < Succ(Succ n)")
(use "f m1=b")
(use "lIsMonochrome")
(save "Goal")
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;---------------------------------------------
(set! COMMENT-FLAG #t)
(set! ETSMD-LET-ENABLED #t)
(define extr_term-g (proof-to-extracted-md-term (np
	  (expand-theorems (theorem-name-to-proof "Goal")))))
(add-program-constant "mdGoal" (term-to-type extr_term-g))
; (pp extr_term-g) ; 38 lines
; (define nterm-g (nt extr_term-g))
; (pp nterm-g) ; 13 lines
(define (animate-goal) (add-computation-rule "mdGoal f k" (nt
     (mk-term-in-app-form extr_term-g (pt "f") (pt "k")))))
(define (deanimate-goal)
  (remove-computation-rules-for (pt "mdGoal f k")))
(set! COMMENT-FLAG #f)
;---------------------------------------------
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(set-goal FinalGoal)
(assume "k" "n" "f" "NotSTLZ" "FC")
(use "IPH" (pt "k") (pt "f"))
;-------------------------------------------------
(assume "b" "Infb")
(use "Goal" (pt "f") (pt "b") (pt "n"))
(use "Infb")
(assume "l" "Lh l=Succ n" "lIsDecreasing" "lIsMonochrome")
(use "NotSTLZ" (pt "l"))
(use "Lh l=Succ n")
(use "lIsDecreasing")
(assume "m" "m<n")
(use "NatEqTrans" (pt "b"))
(use "lIsMonochrome")
(use "NatLtTrans" (pt "Succ m"))
(use "Truth-Axiom")
(use "m<n")
(use "NatEqSym")
(use "lIsMonochrome")
(use "m<n")
;-------------------------------------------------
(use "FC")
;-------------------------------------------------
(save "FinalGoal")

(set! COMMENT-FLAG #t)
(set! ETSMD-LET-ENABLED #t)
(define extr_term-km
  (proof-to-extracted-md-term (theorem-name-to-proof "FinalGoal")))
(cmdisplay "Type of term extracted by Modal Dialectica from UPP is "
    (type-to-string (term-to-type extr_term-km)) " ")
; (pp extr_term-km) ; 5 lines

;===============================
; Trifon's TEST and Dan's Random
;===============================

; generate a list of 2^n infinite sequences
; starting with all possible variations of n booleans
; and continuing with #f
(define (generate-seq n)
  (if (= n 0)
      (list (lambda (n) 0))
      (foldr (lambda (x l)
	       (cons (lambda (n) (if (= n 0) 0 (x (- n 1))))
		     (cons (lambda (n) (if (= n 0) 1 (x (- n 1))))
			   l)))
	     '()
	     (generate-seq (- n 1)))))

; generate one sequence of colors 0 .. (k-1) with initial k^n 
; elements randomly generated and continuing with color 0
(define (grand-itm k) (if (and (fxpositive? k) (> k 1))
   (rand-itm k) (myerror "grand-itm: not exact positive arg or k=1")))
(define (rand-itm k) (fxmodulo (random (most-positive-fixnum)) k))
(define (grand-seq k n) (if (and (fxpositive? k) (> k 1) (fxpositive? n))
	(rand-seq k (expt k n))
	(myerror "grand-seq: not exact positive args or k=1")))
(define (rand-seq k e) (first (lambda (m) (rand-itm k)) e))
(define (seq-fn seq) (let*((fxv (list->fxvector seq))
			   (len (fxvector-length fxv)))
		       (lambda (m) (if (< m len)
				(fxvector-ref fxv m) 0))))
	 
; return a list of (f 0),(f 1),...,(f n-1)
(define (first f n)
  (if (= n 0)
      '()
       (cons (f 0)
	     (first (lambda (n) (f (+ n 1))) (- n 1)))))

; (for-each (lambda (x) (display (first x 7)) (newline)) (generate-seq 4))

; test a Scheme program on a list of infinite binary sequences
(define (test-bseq program . l)
  (let ((len (if (null? l) 4 (car l))))
    (map (lambda (seq)
	   (display "Testing on: ") (display (first seq len))
	   (let ((p (program seq))) (cmdisplay  "Result:"
		    (car p) "." (cdr p))))
	 (generate-seq len)))
  *the-non-printing-object*)

; test the Scheme program on one infinite sequence of random colors 
(define (test-rseq p k n l)
  (let* ((len (fxmax 4 l))
	 (lseq (rand-seq k len))
	 (fseq (seq-fn lseq))
	 (res (((p k) n) fseq )))
	   (display "Testing on: ") (display lseq)
	   (cmdisplay  "Result:"
		    (car res) "." (cdr res))))

; definitions needed for term-to-expr

(define (|ListAppend| l1)
  (lambda (l2)
    (append l1 l2)))

(define (|listrec| l)
  (lambda (base)
    (lambda (step)
      (if (null? l)
	  base
	  (((step (car l)) (cdr l))
	   (((|listrec| (cdr l)) base) step))))))

(define (|NatMax| n1)
  (lambda (n2)
    (max n1 n2)))

(define |ListLength| length)

(define (|ListProj| n)
  (lambda (l)
    (if (< n (length l))
	(list-ref l n)
	0)))

; prepare a Scheme program for modal Dialectica translation
(define (prepare-a term k n)
  (let ((prog (ev (term-to-expr term))))
      ((prog k) n)))

; animate subprograms for modular modal Dialectica
(define |mdGoal| (ev (term-to-expr extr_term-g)))
(define |mdIPH|  (ev (term-to-expr nterm-iph)))

; test modular modal Dialectica translation
(newline)
(test-bseq (prepare-a extr_term-km 2 1))
(define prog (ev (term-to-expr extr_term-km)))
(newline)
(time (test-rseq prog 2 9 1024))
;; (time (test-rseq prog 3 3 81))
;; 33 minutes [worst case!] runtime for 3 colors and 4 indexes
;; > Testing on: (0 1 1 2 0 1 2 2 1 1 1 2 1 2 0 1 0 1 0 2 0 2 1 0 2 0 0 0 0 1 1 2 1 0 2 0 0 1 2 1 0 0 0 0 0 2 1 1 0 2 2 0 1 2 2 1 1 1 1 2 2 1 0 1 2 2 0 0 2 1 0 2 0 0 1 2 1 0 2 0 1)
;; ; (Result: 41 . (44 43 42 41))
;; - the color is 0, the last 4 of the 5 zeros in the middle of the 81-length sequence
;; (time (test-rseq prog ...))
;;     114842 collections
;;     1940934 ms elapsed cpu time, including 21405 ms collecting
;;     1940874 ms elapsed real time, including 20796 ms collecting
;;     483706748128 bytes allocated, including 483704052400 bytes reclaimed


