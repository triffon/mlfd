;; $Id: init.scm 2673 2014-01-08 10:00:19Z schwicht $

(define minlogpath "C:\\minlog")
;; will be substituted by the correct path

;; Globally defined functions

(define (ev x)
  (eval x))
;;   (eval x (the-environment)))

(define (global-eval expr)
  (eval expr))
;;  (eval expr user-initial-environment))

(define (number-to-string n)
  (number->string n))

;; (define call/cc call-with-current-continuation)

;; Adaptable comment

;; comment yields complete one-line comments composed from multiple
;; strings, beginning with COMMENT-STRING and ending with a newline
;; command.  Complete comments can be switched off using COMMENT-FLAG.

(define COMMENT-STRING "")
(define COMMENT-FLAG #t)
(define OLD-COMMENT-FLAG #t)

(define (comment . x)
  (if COMMENT-FLAG
      (begin
	(display COMMENT-STRING)
	(for-each display x)
	(newline))))

(define (multiline-comment . x)
  (if COMMENT-FLAG
      (for-each comment (map error-object-to-string x))))

;; display-comment is used for building complex displays with
;; COMMENT-STRING inserted in front, e.g. to display goals or proofs.

(define (display-comment . x)
  (if COMMENT-FLAG
      (let ((xs (apply string-append x)))
	(display COMMENT-STRING)
	(do ((pos 0 (+ pos 1)))
	    ((= pos (string-length xs)) (display xs))
	  (if (eq? (string-ref xs pos) #\newline)
	      (begin
		(display (substring xs 0 pos))
		(newline)
		(display COMMENT-STRING)
		(set! xs (substring xs (+ pos 1) (string-length xs)))
		(set! pos -1)))))))

(define (error-object-to-string x)
  (cond
   ((string? x) x)
   ((number? x) (number->string x))
   ((symbol? x) (symbol->string x))
   ((null? x) "Null")
   ((type? x) (type-to-string x))
   ((var? x) (var-to-string x))
   ((term? x) (term-to-string x))
   ((formula? x) (formula-to-string x))
   ((avar? x) (string-append (avar-to-string x) ": "
			     (formula-to-string (avar-to-formula x))))
   ((proof-form? x) (string-append "Proof with tag " (symbol->string (tag x))))
   ((list? x) (string-append
	       "("
	       (error-object-to-string (car x))
	       (apply string-append
		      (map (lambda (y)
			     (string-append " " (error-object-to-string y)))
			   (cdr x)))
	       ")"))
   ((pair? x) (string-append "("
			     (error-object-to-string (car x))
			     " . "
			     (error-object-to-string (cdr x))
			     ")"))
   (else "Unknown error object encountered")))

(define (myerror . x)
  (if COMMENT-FLAG
      (do ((l x (cdr l)))
	  ((null? l) (newline) (display-comment) (error "Minlog" "sorry"))
	(newline) (display-comment (error-object-to-string (car l))))
      (begin
	(set! COMMENT-FLAG #t)
	(do ((l x (cdr l)))
	    ((null? l) (newline) (display-comment) (set! COMMENT-FLAG #f)
	     (error "Minlog" "sorry"))
	  (newline) (display-comment (error-object-to-string (car l)))))))

(define (eval-once lambda-expr)
  ;; Evaluate an expression only once
  ;; Assumes: lambda-expr is a function of no argument
  ;; Returns: a function of no argument, that, when evaluated for the first
  ;;          time calls lambda-expr and returns the result. When called again
  ;;          it returns the previously cached value
  (let ((cached-result '())
	(already-evaluated #f))
    (lambda ()
      (if already-evaluated
	  cached-result
	  (let ((result (lambda-expr)))
	    (set! already-evaluated #t)
	    (set! cached-result result)
	    result)))))

(define *the-non-printing-object* (display ""))

(define (foldr bin-op initial-value list)
  ;; fold right:
  ;; fold a list with bin-op
  ;; starting from the end of the list
  (cond ((null? list) initial-value)
	(else (bin-op (car list) (foldr bin-op initial-value (cdr list))))))

;; map-2 maps a binary operator over two lists of input data (of possibly
;; distinct lengths), collecting the results in a single list of output.
;; Difference to ordinary map: the lists may have different lengths.

(define (map-2 bin-op list1 list2)
  (cond ((null? list1) '())
	((null? list2) '())
	(else (cons (bin-op (car list1) (car list2))
		    (map-2 bin-op (cdr list1) (cdr list2))))))

;; (define (bin-and a b)
;;   ;; and as binary function rather than as a macro
;;   ;; (sometimes also called the ``strict and''
;;   (cond (a #t)
;; 	(b #t)
;; 	(else #f)))
;; ?: (bin-and #t #f)  => #t

;; 2004-07-12 define functions particular to petite, but not in R5RS

(define last-pair
  (lambda (x)
    (cond ((pair? (cdr x)) (last-pair (cdr x))) (else x))))

(define make-list
  (lambda x
    (if (= (car x) 0)
	'()
        (cons (if (null? (cdr x))
		  '()
		  (car (cdr x)))
	      (apply make-list (cons (- (car x) 1) (cdr x)))))))

(define string-list=?
  (lambda (strs)
    (if (null? strs) #t
        (if (null? (cdr strs)) #t
            (if (string=? (car strs) (cadr strs))
                (string-list=? (cdr strs))
                #f)))))

(define tab #\	)

;; Loading the system

(define LOADED-FILES '("initDan.scm"))

(define (display-loaded-files)
  (do ((strs LOADED-FILES (cdr strs))
       (i (- (length LOADED-FILES) 1) (- i 1)))
      ((null? strs) (newline))
    (newline)
    (display (string-append (number->string i) ": " (car strs)))))


(define (minlog-load dir path)
  (let ((pfad (string-append dir path)))
    (if (member pfad LOADED-FILES)
        (display
         (string-append "minlog-load WARNING: file " pfad " already loaded !"))
        (begin (set! LOADED-FILES (append (list pfad) LOADED-FILES))
               (load (string-append minlogpath "/" pfad))))))

(define (exload path)
  (minlog-load "examples/" path))

(define (libload path)
  (minlog-load "lib/" path))

(define (mload path)
  (minlog-load "src/" path))

(define (srcload path)
  (minlog-load "src/" path))

;; (srcload "ea.scm")
;; (srcload "prologue.scm")
;; (srcload "compat.scm")
(srcload "gen-app.scm")
(srcload "list.scm")
(srcload "typ.scm")
(srcload "var.scm")
(srcload "pconst.scm")
(srcload "psym.scm")
(srcload "term.scm")
(srcload "pp.scm")
(srcload "pp-sexp.scm")
(srcload "lr-dvr.scm")
(srcload "formula.scm")
(srcload "minitab.scm")
(srcload "boole.scm")
(srcload "axiom.scm")
(srcload "proof.scm")
(srcload "pproof.scm")
(srcload "prop.scm")
;; (srcload "type-inf.scm") ;transferred into modules
(srcload "ets.scm")
(srcload "atr.scm") ;moved back from modules
;; (srcload "mysfa.scm")
(srcload "etsd.scm")
(srcload "lnf.scm")


(newline)
(display "Minlog loaded successfully")
(newline)
*the-non-printing-object*
