;;;; match.scm -- portable hygienic pattern matcher -*- coding: utf-8 -*-
;;
;; This code is written by Alex Shinn and placed in the
;; Public Domain.  All warranties are disclaimed.

;; This file has all the user documentation removed, but still contains
;; all the comments that explain the code. It also has condensed function
;; names. The idea is to make refactoring easier by reducing the size of
;; of the code. So this file isn't intended to be used directly but
;; possibly to make re-implementation easier.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Notes

;; The implementation is a simple generative pattern matcher - each
;; pattern is expanded into the required tests, calling a failure
;; continuation if the tests fail.  This makes the logic easy to
;; follow and extend, but produces sub-optimal code in cases where you
;; have many similar clauses due to repeating the same tests.
;; Nonetheless a smart compiler should be able to remove the redundant
;; tests.  For MATCH-LET and DESTRUCTURING-BIND type uses there is no
;; performance hit.

;; The original version was written on 2006/11/29 and described in the
;; following Usenet post:
;;   http://groups.google.com/group/comp.lang.scheme/msg/0941234de7112ffd
;; and is still available at
;;   http://synthcode.com/scheme/match-simple.scm
;; It's just 80 lines for the core MATCH, and an extra 40 lines for
;; MATCH-LET, MATCH-LAMBDA and other syntactic sugar.
;;
;; A variant of this file which uses COND-EXPAND in a few places for
;; performance can be found at
;;   http://synthcode.com/scheme/match-cond-expand.scm
;; Changes marked FT at end were part of SRFI process, not in original
;; match library.
;;
;; 2021/01/12 - add var,
;; 2020/09/04 - perf fix for `not`
;; 2020/08/24 - convert ..= ..* ..1 to =.. *.. **1, remove @ FT
;; 2020/08/21 - handle underscores separately, not as literals FT
;; 2020/08/21 - fixing match-letrec with unhygienic insertion
;; 2020/08/03 - added bindings for auxiliary syntax FT
;; 2020/07/06 - adding `=..' and `*..' patterns; fixing ,@ patterns
;; 2016/10/05 - treat keywords as literals, not identifiers, in Chicken
;; 2016/03/06 - fixing named match-let (thanks to Stefan Israelsson Tampe)
;; 2015/05/09 - fixing bug in var extraction of quasiquote patterns
;; 2014/11/24 - adding Gauche's `@' pattern for named record field matching
;; 2012/12/26 - wrapping match-let&co body in lexical closure
;; 2012/11/28 - fixing typo s/vetor/vector in largely unused set! code
;; 2012/05/23 - fixing combinatorial explosion of code in certain or patterns
;; 2011/09/25 - fixing bug when directly matching an identifier repeated in
;;              the pattern (thanks to Stefan Israelsson Tampe)
;; 2011/01/27 - fixing bug when matching tail patterns against improper lists
;; 2010/09/26 - adding `**1' patterns (thanks to Ludovic Courtès)
;; 2010/09/07 - fixing identifier extraction in some `...' and `***' patterns
;; 2009/11/25 - adding `***' tree search patterns
;; 2008/03/20 - fixing bug where (a ...) matched non-lists
;; 2008/03/15 - removing redundant check in vector patterns
;; 2008/03/06 - you can use `...' portably now (thanks to Taylor Campbell)
;; 2007/09/04 - fixing quasiquote patterns
;; 2007/07/21 - allowing ellipsis patterns in non-final list positions
;; 2007/04/10 - fixing potential hygiene issue in m?...
;;              (thanks to Taylor Campbell)
;; 2007/04/08 - clean up, commenting
;; 2006/12/24 - bugfixes
;; 2006/12/01 - non-linear patterns, shared variables in OR, get!/set!

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; force compile-time syntax errors with useful messages

(define-syntax match-syntax-error
  (syntax-rules ()
    ((_) (syntax-error "invalid match-syntax-error usage"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The basic interface.  MATCH just performs some basic syntax
;; validation, binds the match expression to a temporary variable `v',
;; and passes it on to MATCH-NEXT.  It's a constant throughout the
;; code below that the binding `v' is a direct variable reference, not
;; an expression.

(define-syntax match
  (syntax-rules ()
    ((match)
     (match-syntax-error "missing match expression"))
    ((match atom)
     (match-syntax-error "no match clauses"))
    ((match (app ...) (pat . body) ...)
     (let ((v (app ...)))
       (m+1 v ((app ...) (set! (app ...))) (pat . body) ...)))
    ((match #(vec ...) (pat . body) ...)
     (let ((v #(vec ...)))
       (m+1 v (v (set! v)) (pat . body) ...)))
    ((match atom (pat . body) ...)
     (let ((v atom))
       (m+1 v (atom (set! atom)) (pat . body) ...)))
    ))

;; MATCH-NEXT passes each clause to MATCH-ONE in turn with its failure
;; thunk, which is expanded by recursing MATCH-NEXT on the remaining
;; clauses.  `g+s' is a list of two elements, the get! and set!
;; expressions respectively.
;; NOTE MATCH-NEXT condensed to M+1, MATCH-ONE condesed to M1
;; all occurences of FAILURE are replaced with FAIL, all occurences
;; of MATCH-DROP-IDS to M-IDS "match minus ids".

(define-syntax m+1
  (syntax-rules (=>)
    ;; no more clauses, the match failed
    ((m+1 v g+s)
     (error 'match "no matching pattern"))
    ;; named fail continuation
    ((m+1 v g+s (pat (=> fail) . body) . rest)
     (let ((fail (lambda () (m+1 v g+s . rest))))
       ;; m1 analyzes the pattern for us
       (m1 v pat g+s (m-ids (begin . body)) (fail) ())))
    ;; anonymous fail continuation, give it a dummy name
    ((m+1 v g+s (pat . body) . rest)
     (m+1 v g+s (pat (=> fail) . body) . rest))))

;; MATCH-ONE first checks for ellipsis patterns, otherwise passes on to
;; MATCH-UNDERSCORE.
;; NOTE changes: MATCH-UNDERSCORE M_, MATCH-CHECK-IDENTIFIER M?ID,
;; MATCH-CHECK-ELLIPSIS M?..., MATCH-EXTRACT-UNDERSCORE M<-_,
;; MATCH-GEN-ELLIPSIS M<...>:

(define-syntax m1
  (syntax-rules (var)
    ;; catch var here in case the identifier is an ellipsis
    ((m1 v (var x) g+s (sk ...) fk (id ...))
     (m?id
      x
      (let-syntax
          ((new-sym?
            (syntax-rules (id ...)
              ((new-sym? x sk2 fk2) sk2)
              ((new-sym? y sk2 fk2) fk2))))
        (new-sym? random-sym-to-match
                  (let ((x v)) (sk ... (id ... x)))
                  (if (equal? v x) (sk ... (id ...)) fk)))
      (if (equal? v x) (sk ... (id ...)) fk)))
    ;; If it's a list of two or more values, check to see if the
    ;; second one is an ellipsis and handle accordingly, otherwise go
    ;; to MATCH-TWO.
    ((m1 v (p q . r) g+s sk fk i)
     (m?...
      q
      (m<-_ p (m<...> v p r  g+s sk fk i) i ())
      (m_ v (p q . r) g+s sk fk i)))
    ;; Go directly to MATCH-TWO.
    ((m1 . x)
     (m_ . x))))

;; Helper functions
;; this may need to be changed, I've had trouble with cond-expand and
;; R6RS
;; NOTE chaged UNDERSCORE to _?
(cond-expand
  (r7rs
    (define-syntax _?
      (syntax-rules (_)
	((_ _ kt kf) kt)
	((_ x kt kf) kf))))
  (r6rs
    ;some r7rs's don't like #' syntax
    (define-syntax _?
      (lambda (stx)
	(syntax-case stx ()
		     ((_ x kt kf)
		      (if (and (identifier? (syntax x))
			       (free-identifier=? (syntax x) (syntax _)))
			  (syntax kt)
			  (syntax kf)))))))
  (else
    (define-syntax _?
      (syntax-rules (_)
	((_ _ kt kf) kt)
	((_ x kt kf) kf)))))

;; MATCH-UNDERSCORE first checks for underscore patterns, otherwise passes
;; on to MATCH-TWO. NOTE MATCH-TWO changed to M2.

(define-syntax m_
  (syntax-rules ()
    ((m_ v p g+s (sk ...) fk i)
     (_? p
		  (sk ... i)
		  (m2 v p g+s (sk ...) fk i)))))

;; This is the guts of the pattern matcher.  We are passed a lot of
;; information in the form:
;;
;;   (m2 var pattern getter setter success-k fail-k (ids ...))
;;
;; usually abbreviated
;;
;;   (m2 v p g+s sk fk i)
;;
;; where VAR is the symbol name of the current variable we are
;; matching, PATTERN is the current pattern, getter and setter are the
;; corresponding accessors (e.g. CAR and SET-CAR! of the pair holding
;; VAR), SUCCESS-K is the success continuation, FAIL-K is the fail
;; continuation (which is just a thunk call and is thus safe to expand
;; multiple times) and IDS are the list of identifiers bound in the
;; pattern so far.
;; NOTE MATCH-QUASIQUOTE mqq, MATCH-GEN-OR M<OR>, MATCH-GEN-SEARCH M<***>
;; MATCH-GEN-ELLIPSIS/RANGE M<...>/RANGE, MATCH-RECORD-REFS M<R>I (R actually
;; captital), MATCH-RECORD-NAMED-REFS m<R>id,

(define-syntax m2
  (syntax-rules (___ **1 =.. *.. *** quote quasiquote ? $ struct object = and or not set! get!)
    ((m2 v () g+s (sk ...) fk i) (if (null? v) (sk ... i) fk))
    ((m2 v (quote p) g+s (sk ...) fk i) (if (equal? v 'p) (sk ... i) fk))
    ((m2 v (quasiquote p) . x) (mqq v p . x))
    ((m2 v (and) g+s (sk ...) fk i) (sk ... i))
    ((m2 v (and p q ...) g+s sk fk i) (m1 v p g+s (m1 v (and q ...) g+s sk fk) fk i))
    ((m2 v (or) g+s sk fk i) fk)
    ((m2 v (or p) . x) (m1 v p . x))
    ((m2 v (or p ...) g+s sk fk i) (m<-_ (or p ...) (m<or> v (p ...) g+s sk fk i) i ()))
    ((m2 v (not p) g+s (sk ...) fk i)
     (let ((fk2 (lambda () (sk ... i))))
       (m1 v p g+s (m-ids fk) (fk2) i)))
    ((m2 v (get! getter) (g s) (sk ...) fk i) (let ((getter (lambda () g))) (sk ... i)))
    ((m2 v (set! setter) (g (s ...)) (sk ...) fk i) (let ((setter (lambda (x) (s ... x)))) (sk ... i)))
    ((m2 v (? pred . p) g+s sk fk i) (if (pred v) (m1 v (and . p) g+s sk fk i) fk))
    ((m2 v (= proc p) . x) (let ((w (proc v))) (m1 w p . x)))
    ((m2 v (p ___ . r) g+s sk fk i) (m<-_ p (m<...> v p r g+s sk fk i) i ()))
    ((m2 v (p) g+s sk fk i)
     (if (and (pair? v) (null? (cdr v)))
         (let ((w (car v)))
           (m1 w p ((car v) (set-car! v)) sk fk i))
         fk))
    ((m2 v (p *** q) g+s sk fk i) (m<-_ p (m<***> v p q g+s sk fk i) i ()))
    ((m2 v (p *** . q) g+s sk fk i) (match-syntax-error "invalid use of ***" (p *** . q)))
    ((m2 v (p **1) g+s sk fk i) (if (pair? v) (m1 v (p ___) g+s sk fk i) fk))
    ((m2 v (p =.. n . r) g+s sk fk i) (m<-_ p (m<...>/range n n v p r g+s sk fk i) i ()))
    ((m2 v (p *.. n m . r) g+s sk fk i) (m<-_ p (m<...>/range n m v p r g+s sk fk i) i ()))
    ((m2 v ($ rec p ...) g+s sk fk i) (if (is-a? v rec) (m<R>n v rec 0 (p ...) g+s sk fk i) fk))
    ((m2 v (struct rec p ...) g+s sk fk i) (if (is-a? v rec) (m<R>n v rec 0 (p ...) g+s sk fk i) fk))
    ((m2 v (object rec p ...) g+s sk fk i) (if (is-a? v rec) (m<R>id v rec (p ...) g+s sk fk i) fk))
    ((m2 v (p . q) g+s sk fk i)
     (if (pair? v)
         (let ((w (car v)) (x (cdr v)))
           (m1 w p ((car v) (set-car! v))
                      (m1 x q ((cdr v) (set-cdr! v)) sk fk)
                      fk
                      i))
         fk))
    ((m2 v #(p ...) g+s . x)
     (mvec v 0 () (p ...) . x))
    ;; Not a pair or vector or special literal, test to see if it's a
    ;; new symbol, in which case we just bind it, or if it's an
    ;; already bound symbol or some other literal, in which case we
    ;; compare it with EQUAL?.
    ((m2 v x g+s (sk ...) fk (id ...))
     ;; This extra m?id is optional in general, but
     ;; can serve as a fast path, and is needed to distinguish
     ;; keywords in Chicken.
     (m?id
      x
      (let-syntax
          ((new-sym?
            (syntax-rules (id ...)
              ((new-sym? x sk2 fk2) sk2)
              ((new-sym? y sk2 fk2) fk2))))
        (new-sym? random-sym-to-match
                  (let ((x v)) (sk ... (id ... x)))
                  (if (equal? v x) (sk ... (id ...)) fk)))
      (if (equal? v x) (sk ... (id ...)) fk)))
    ))

;; QUASIQUOTE patterns

(define-syntax mqq
  (syntax-rules (unquote unquote-splicing quasiquote or)
    ((_ v (unquote p) g+s sk fk i)
     (m1 v p g+s sk fk i))
    ((_ v ((unquote-splicing p) . rest) g+s sk fk i)
     ;; TODO: it is an error to have another unquote-splicing in rest,
     ;; check this and signal explicitly
     (m<-_
      p
      (m<...>/qq v p rest g+s sk fk i) i ()))
    ((_ v (quasiquote p) g+s sk fk i . depth)
     (mqq v p g+s sk fk i #f . depth))
    ((_ v (unquote p) g+s sk fk i x . depth)
     (mqq v p g+s sk fk i . depth))
    ((_ v (unquote-splicing p) g+s sk fk i x . depth)
     (mqq v p g+s sk fk i . depth))
    ((_ v (p . q) g+s sk fk i . depth)
     (if (pair? v)
       (let ((w (car v)) (x (cdr v)))
         (mqq
          w p g+s
          (mqqstep x q g+s sk fk depth)
          fk i . depth))
       fk))
    ((_ v #(elt ...) g+s sk fk i . depth)
     (if (vector? v)
       (let ((ls (vector->list v)))
         (mqq ls (elt ...) g+s sk fk i . depth))
       fk))
    ((_ v x g+s sk fk i . depth)
     (m1 v 'x g+s sk fk i))))

(define-syntax mqqstep
  (syntax-rules ()
    ((mqqstep x q g+s sk fk depth i)
     (mqq x q g+s sk fk i . depth))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Utilities

;; Takes two values and just expands into the first.
(define-syntax m-ids
  (syntax-rules ()
    ((_ expr ids ...) expr)))

(define-syntax m:ids:
  (syntax-rules ()
    ((_ (letish args (expr ...)) ids ...)
     (letish args (expr ... ids ...)))))

(define-syntax m-1st
  (syntax-rules ()
    ((_ arg expr) expr)))

;; To expand an OR group we try each clause in succession, passing the
;; first that succeeds to the success continuation.  On fail for
;; any clause, we just try the next clause, finally resorting to the
;; fail continuation fk if all clauses fail.  The only trick is
;; that we want to unify the identifiers, so that the success
;; continuation can refer to a variable from any of the OR clauses.

(define-syntax m<or>
  (syntax-rules ()
    ((_ v p g+s (sk ...) fk (i ...) ((id id-ls) ...))
     (let ((sk2 (lambda (id ...) (sk ... (i ... id ...))))
           (id (if #f #f)) ...)
       (m<or>step v p g+s (m-ids (sk2 id ...)) fk (i ...))))))

(define-syntax m<or>step
  (syntax-rules ()
    ((_ v () g+s sk fk . x)
     ;; no OR clauses, call the fail continuation
     fk)
    ((_ v (p) . x)
     ;; last (or only) OR clause, just expand normally
     (m1 v p . x))
    ((_ v (p . q) g+s sk fk i)
     ;; match one and try the remaining on fail
     (let ((fk2 (lambda () (m<or>step v q g+s sk fk i))))
       (m1 v p g+s sk (fk2) i)))
    ))

;; We match a pattern (p ...) by matching the pattern p in a loop on
;; each element of the variable, accumulating the bound ids into lists.

;; Look at the body of the simple case - it's just a named let loop,
;; matching each element in turn to the same pattern.  The only trick
;; is that we want to keep track of the lists of each extracted id, so
;; when the loop recurses we cons the ids onto their respective list
;; variables, and on success we bind the ids (what the user input and
;; expects to see in the success body) to the reversed accumulated
;; list IDs.

(define-syntax m<...>
  (syntax-rules ()
    ;; TODO: restore fast path when p is not already bound
    ;; ((_ v p () g+s (sk ...) fk i ((id id-ls) ...))
    ;;  (m?id p
    ;;    ;; simplest case equivalent to (p ...), just bind the list
    ;;    (let ((p v))
    ;;      (if (list? p)
    ;;          (sk ... i)
    ;;          fk))
    ;;    ;; simple case, match all elements of the list
    ;;    (let loop ((ls v) (id-ls '()) ...)
    ;;      (cond
    ;;        ((null? ls)
    ;;         (let ((id (reverse id-ls)) ...) (sk ... i)))
    ;;        ((pair? ls)
    ;;         (let ((w (car ls)))
    ;;           (m1 w p ((car ls) (set-car! ls))
    ;;                      (m-ids (loop (cdr ls) (cons id id-ls) ...))
    ;;                      fk i)))
    ;;        (else
    ;;         fk)))))
    ((_ v p r g+s sk fk (i ...) ((id id-ls) ...))
     ;; general case, trailing patterns to match, keep track of the
     ;; remaining list length so we don't need any backtracking
     (m?0...
      r
      (let* ((tail-len (length 'r))
             (ls v)
             (len (and (list? ls) (length ls))))
        (if (or (not len) (< len tail-len))
            fk
            (let loop ((ls ls) (n len) (id-ls '()) ...)
              (cond
                ((= n tail-len)
                 (let ((id (reverse id-ls)) ...)
                   (m1 ls r (#f #f) sk fk (i ... id ...))))
                ((pair? ls)
                 (let ((w (car ls)))
                   (m1 w p ((car ls) (set-car! ls))
                              (m-ids
                               (loop (cdr ls) (- n 1) (cons id id-ls) ...))
                              fk
                              (i ...))))
                (else
                 fk)))))))))

;; Variant of the above where the rest pattern is in a quasiquote.

(define-syntax m<...>/qq
  (syntax-rules ()
    ((_ v p r g+s (sk ...) fk (i ...) ((id id-ls) ...))
     (m?0...
      r
      (let* ((tail-len (length 'r))
             (ls v)
             (len (and (list? ls) (length ls))))
        (if (or (not len) (< len tail-len))
            fk
            (let loop ((ls ls) (n len) (id-ls '()) ...)
              (cond
               ((= n tail-len)
                (let ((id (reverse id-ls)) ...)
                  (mqq ls r g+s (sk ...) fk (i ... id ...))))
               ((pair? ls)
                (let ((w (car ls)))
                  (m1 w p ((car ls) (set-car! ls))
                             (m-ids
                              (loop (cdr ls) (- n 1) (cons id id-ls) ...))
                             fk
                             (i ...))))
               (else
                fk)))))))))

;; Variant of above which takes an n/m range for the number of
;; repetitions.  At least n elements much match, and up to m elements
;; are greedily consumed.

(define-syntax m<...>/range
  (syntax-rules ()
    ((_ %lo %hi v p r g+s (sk ...) fk (i ...) ((id id-ls) ...))
     ;; general case, trailing patterns to match, keep track of the
     ;; remaining list length so we don't need any backtracking
     (m?0...
      r
      (let* ((lo %lo)
             (hi %hi)
             (tail-len (length 'r))
             (ls v)
             (len (and (list? ls) (- (length ls) tail-len))))
        (if (and len (<= lo len hi))
            (let loop ((ls ls) (j 0) (id-ls '()) ...)
              (cond
                ((= j len)
                 (let ((id (reverse id-ls)) ...)
                   (m1 ls r (#f #f) (sk ...) fk (i ... id ...))))
                ((pair? ls)
                 (let ((w (car ls)))
                   (m1 w p ((car ls) (set-car! ls))
                              (m-ids
                               (loop (cdr ls) (+ j 1) (cons id id-ls) ...))
                              fk
                              (i ...))))
                (else
                 fk)))
            fk))))))

;; This is just a safety check.  Although unlike syntax-rules we allow
;; trailing patterns after an ellipsis, we explicitly disable multiple
;; ellipsis at the same level.  This is because in the general case
;; such patterns are exponential in the number of ellipsis, and we
;; don't want to make it easy to construct very expensive operations
;; with simple looking patterns.  For example, it would be O(n^2) for
;; patterns like (a ... b ...) because we must consider every trailing
;; element for every possible break for the leading "a ...".

(define-syntax m?0...
  (syntax-rules ()
    ((_ (x . y) sk)
     (m?...
      x
      (match-syntax-error
       "multiple ellipsis patterns not allowed at same level")
      (m?0... y sk)))
    ((_ () sk)
     sk)
    ((_ x sk)
     (match-syntax-error "dotted tail not allowed after ellipsis" x))))

;; To implement the tree search, we use two recursive procedures.  TRY
;; attempts to match Y once, and on success it calls the normal SK on
;; the accumulated list ids as in MATCH-GEN-ELLIPSIS.  On fail, we
;; call NEXT which first checks if the current value is a list
;; beginning with X, then calls TRY on each remaining element of the
;; list.  Since TRY will recursively call NEXT again on fail, this
;; effects a full depth-first search.
;;
;; The fail continuation throughout is a jump to the next step in
;; the tree search, initialized with the original fail continuation
;; FK.

(define-syntax m<***>
  (syntax-rules ()
    ((m<***> v p q g+s sk fk i ((id id-ls) ...))
     (letrec ((try (lambda (w fail id-ls ...)
                     (m1 w q g+s
                                (m:ids:
                                 (let ((id (reverse id-ls)) ...)
                                   sk))
                                (next w fail id-ls ...) i)))
              (next (lambda (w fail id-ls ...)
                      (if (not (pair? w))
                          (fail)
                          (let ((u (car w)))
                            (m1
                             u p ((car w) (set-car! w))
                             (m-ids
                              ;; accumulate the head variables from
                              ;; the p pattern, and loop over the tail
                              (let ((id-ls (cons id id-ls)) ...)
                                (let lp ((ls (cdr w)))
                                  (if (pair? ls)
                                      (try (car ls)
                                           (lambda () (lp (cdr ls)))
                                           id-ls ...)
                                      (fail)))))
                             (fail) i))))))
       ;; the initial id-ls binding here is a dummy to get the right
       ;; number of '()s
       (let ((id-ls '()) ...)
         (try v (lambda () fk) id-ls ...))))))

;; Vector patterns are just more of the same, with the slight
;; exception that we pass around the current vector index being
;; matched.

(define-syntax mvec
  (syntax-rules (___)
    ((_ v n pats (p q) . x)
     (m?... q
                          (m<vec...> v n pats p . x)
                          (mvec2 v n pats (p q) . x)))
    ((_ v n pats (p ___) sk fk i)
     (m<vec...> v n pats p sk fk i))
    ((_ . x)
     (mvec2 . x))))

;; Check the exact vector length, then check each element in turn.

(define-syntax mvec2
  (syntax-rules ()
    ((_ v n ((pat index) ...) () sk fk i)
     (if (vector? v)
         (let ((len (vector-length v)))
           (if (= len n)
               (mvecstep v ((pat index) ...) sk fk i)
               fk))
         fk))
    ((_ v n (pats ...) (p . q) . x)
     (mvec v (+ n 1) (pats ... (p n)) q . x))))

(define-syntax mvecstep
  (syntax-rules ()
    ((_ v () (sk ...) fk i) (sk ... i))
    ((_ v ((pat index) . rest) sk fk i)
     (let ((w (vector-ref v index)))
       (m1 w pat ((vector-ref v index) (vector-set! v index))
                  (mvecstep v rest sk fk)
                  fk i)))))

;; With a vector ellipsis pattern we first check to see if the vector
;; length is at least the required length.

(define-syntax m<vec...>
  (syntax-rules ()
    ((_ v n ((pat index) ...) p sk fk i)
     (if (vector? v)
       (let ((len (vector-length v)))
         (if (>= len n)
           (mvecstep v ((pat index) ...)
                              (mvectail v p n len sk fk)
                              fk i)
           fk))
       fk))))

(define-syntax mvectail
  (syntax-rules ()
    ((_ v p n len sk fk i)
     (m<-_ p (mvectail2 v p n len sk fk i) i ()))))

(define-syntax mvectail2
  (syntax-rules ()
    ((_ v p n len (sk ...) fk i ((id id-ls) ...))
     (let loop ((j n) (id-ls '()) ...)
       (if (>= j len)
         (let ((id (reverse id-ls)) ...) (sk ... i))
         (let ((w (vector-ref v j)))
           (m1 w p ((vector-ref v j) (vector-set! v j))
                      (m-ids (loop (+ j 1) (cons id id-ls) ...))
                      fk i)))))))

(define-syntax m<R>n
  (syntax-rules ()
    ((_ v rec n (p . q) g+s sk fk i)
     (let ((w (slot-ref rec v n)))
       (m1 w p ((slot-ref rec v n) (slot-set! rec v n))
                  (m<R>n v rec (+ n 1) q g+s sk fk) fk i)))
    ((_ v rec n () g+s (sk ...) fk i)
     (sk ... i))))

(define-syntax m<R>id
  (syntax-rules ()
    ((_ v rec ((f p) . q) g+s sk fk i)
     (let ((w (slot-ref rec v 'f)))
       (m1 w p ((slot-ref rec v 'f) (slot-set! rec v 'f))
                  (m<R>id v rec q g+s sk fk) fk i)))
    ((_ v rec () g+s (sk ...) fk i)
     (sk ... i))))

;; Extract underscore in a pattern, otherwise pass on to
;; MATCH-EXTRACT-VARS

(define-syntax m<-_
  (syntax-rules ()
    ((m<-_ p (k ...) i v)
     (_? p
		  (k ... v)
		  (m<-vars p (k ...) i v)))))

;; Extract all identifiers in a pattern.  A little more complicated
;; than just looking for symbols, we need to ignore special keywords
;; and non-pattern forms (such as the predicate expression in ?
;; patterns), and also ignore previously bound identifiers.
;;
;; Calls the continuation with all new vars as a list of the form
;; ((orig-var tmp-name) ...), where tmp-name can be used to uniquely
;; pair with the original variable (e.g. it's used in the ellipsis
;; generation for list variables).
;;
;; (m<-vars pattern continuation (ids ...) (new-vars ...))

(define-syntax m<-vars
  (syntax-rules (___ **1 =.. *.. *** ? $ struct object = quote quasiquote and or not get! set! var)
    ((m<-vars (? pred . p) . x)
     (m<-_ p . x))
    ((m<-vars ($ rec . p) . x)
     (m<-_ p . x))
    ((m<-vars (struct rec . p) . x)
     (m<-_ p . x))
    ((m<-vars (object rec (f p) ...) . x)
     (m<-_ (p ...) . x))
    ((m<-vars (= proc p) . x)
     (m<-_ p . x))
    ((m<-vars (quote x) (k ...) i v)
     (k ... v))
    ((m<-vars (quasiquote x) k i v)
     (m<-qqvars x k i v (#t)))
    ((m<-vars (and . p) . x)
     (m<-_ p . x))
    ((m<-vars (or . p) . x)
     (m<-_ p . x))
    ((m<-vars (not . p) . x)
     (m<-_ p . x))
    ((m<-vars (var p) (k ...) (i ...) v)
     (let-syntax
         ((new-sym?
           (syntax-rules (i ...)
             ((new-sym? p sk fk) sk)
             ((new-sym? any sk fk) fk))))
       (new-sym? random-sym-to-match
                 (k ... ((p p-ls) . v))
                 (k ... v))))
    ;; A non-keyword pair, expand the CAR with a continuation to
    ;; expand the CDR.
    ((m<-vars (p q . r) k i v)
     (m?...
      q
      (m<-_ (p . r) k i v)
      (m<-_ p (m<-vars-step (q . r) k i v) i ())))
    ((m<-vars (p . q) k i v)
     (m<-_ p (m<-vars-step q k i v) i ()))
    ((m<-vars #(p ...) . x)
     (m<-_ (p ...) . x))
    ((m<-vars ___ (k ...) i v)  (k ... v))
    ((m<-vars *** (k ...) i v)  (k ... v))
    ((m<-vars **1 (k ...) i v)  (k ... v))
    ((m<-vars =.. (k ...) i v)  (k ... v))
    ((m<-vars *.. (k ...) i v)  (k ... v))
    ;; This is the main part, the only place where we might add a new
    ;; var if it's an unbound symbol.
    ((m<-vars p (k ...) (i ...) v)
     (let-syntax
         ((new-sym?
           (syntax-rules (i ...)
             ((new-sym? p sk fk) sk)
             ((new-sym? any sk fk) fk))))
       (new-sym? random-sym-to-match
                 (k ... ((p p-ls) . v))
                 (k ... v))))
    ))

;; Stepper used in the above so it can expand the CAR and CDR
;; separately.

(define-syntax m<-vars-step
  (syntax-rules ()
    ((_ p k i v ((v2 v2-ls) ...))
     (m<-_ p k (v2 ... . i) ((v2 v2-ls) ... . v)))
    ))

(define-syntax m<-qqvars
  (syntax-rules (quasiquote unquote unquote-splicing)
    ((m<-qqvars (quasiquote x) k i v d)
     (m<-qqvars x k i v (#t . d)))
    ((m<-qqvars (unquote-splicing x) k i v d)
     (m<-qqvars (unquote x) k i v d))
    ((m<-qqvars (unquote x) k i v (#t))
     (m<-_ x k i v))
    ((m<-qqvars (unquote x) k i v (#t . d))
     (m<-qqvars x k i v d))
    ((m<-qqvars (x . y) k i v d)
     (m<-qqvars
      x
      (m<-qqvars-step y k i v d) i () d))
    ((m<-qqvars #(x ...) k i v d)
     (m<-qqvars (x ...) k i v d))
    ((m<-qqvars x (k ...) i v d)
     (k ... v))
    ))

(define-syntax m<-qqvars-step
  (syntax-rules ()
    ((_ x k i v d ((v2 v2-ls) ...))
     (m<-qqvars x k (v2 ... . i) ((v2 v2-ls) ... . v) d))
    ))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Gimme some sugar baby.

;;> Shortcut for \scheme{lambda} + \scheme{match}.  Creates a
;;> procedure of one argument, and matches that argument against each
;;> clause.

(define-syntax match-lambda
  (syntax-rules ()
    ((_ (pattern . body) ...) (lambda (expr) (match expr (pattern . body) ...)))))

;;> Similar to \scheme{match-lambda}.  Creates a procedure of any
;;> number of arguments, and matches the argument list against each
;;> clause.

(define-syntax match-lambda*
  (syntax-rules ()
    ((_ (pattern . body) ...) (lambda expr (match expr (pattern . body) ...)))))

;;> Matches each var to the corresponding expression, and evaluates
;;> the body with all match variables in scope.  Raises an error if
;;> any of the expressions fail to match.  Syntax analogous to named
;;> let can also be used for recursive functions which match on their
;;> arguments as in \scheme{match-lambda*}.

(define-syntax match-let
  (syntax-rules ()
    ((_ ((var value) ...) . body)
     (match-let/aux () () ((var value) ...) . body))
    ((_ loop ((var init) ...) . body)
     (match-named-let loop () ((var init) ...) . body))))

(define-syntax match-let/aux
  (syntax-rules ()
    ((_ ((var expr) ...) () () . body)
     (let ((var expr) ...) . body))
    ((_ ((var expr) ...) ((pat tmp) ...) () . body)
     (let ((var expr) ...)
       (match-let* ((pat tmp) ...)
         . body)))
    ((_ (v ...) (p ...) (((a . b) expr) . rest) . body)
     (match-let/aux (v ... (tmp expr)) (p ... ((a . b) tmp)) rest . body))
    ((_ (v ...) (p ...) ((#(a ...) expr) . rest) . body)
     (match-let/aux (v ... (tmp expr)) (p ... (#(a ...) tmp)) rest . body))
    ((_ (v ...) (p ...) ((a expr) . rest) . body)
     (match-let/aux (v ... (a expr)) (p ...) rest . body))))

(define-syntax match-named-let
  (syntax-rules ()
    ((_ loop ((pat expr var) ...) () . body)
     (let loop ((var expr) ...)
       (match-let ((pat var) ...)
         . body)))
    ((_ loop (v ...) ((pat expr) . rest) . body)
     (match-named-let loop (v ... (pat expr tmp)) rest . body))))

;;> \macro{(match-let* ((var value) ...) body ...)}

;;> Similar to \scheme{match-let}, but analogously to \scheme{let*}
;;> matches and binds the variables in sequence, with preceding match
;;> variables in scope.

(define-syntax match-let*
  (syntax-rules ()
    ((_ () . body)
     (let () . body))
    ((_ ((pat expr) . rest) . body)
     (match expr (pat (match-let* rest . body))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Challenge stage - unhygienic insertion.
;;
;; It's possible to implement match-letrec without unhygienic
;; insertion by building the let+set! logic directly into the match
;; code above (passing a parameter to distinguish let vs letrec).
;; However, it makes the code much more complicated, so we religate
;; the complexity here.

;;> Similar to \scheme{match-let}, but analogously to \scheme{letrec}
;;> matches and binds the variables with all match variables in scope.

(define-syntax match-letrec
  (syntax-rules ()
    ((_ ((pat val) ...) . body)
     (match-letrec-one (pat ...) (((pat val) ...) . body) ()))))

;; 1: extract all ids in all patterns
(define-syntax match-letrec-one
  (syntax-rules ()
    ((_ (pat . rest) expr ((id tmp) ...))
     (m<-_
      pat (match-letrec-one rest expr) (id ...) ((id tmp) ...)))
    ((_ () expr ((id tmp) ...))
     (match-letrec-two expr () ((id tmp) ...)))))

;; 2: rewrite ids
(define-syntax match-letrec-two
  (syntax-rules ()
    ((_ (() . body) ((var2 val2) ...) ((id tmp) ...))
     ;; We know the ids, their tmp names, and the renamed patterns
     ;; with the tmp names - expand to the classic letrec pattern of
     ;; let+set!.  That is, we bind the original identifiers written
     ;; in the source with let, run match on their renamed versions,
     ;; then set! the originals to the matched values.
     (let ((id (if #f #f)) ...)
       (match-let ((var2 val2) ...)
          (set! id tmp) ...
          . body)))
    ((_ (((var val) . rest) . body) ((var2 val2) ...) ids)
     (match-rewrite
      var
      ids
      (match-letrec-two-step (rest . body) ((var2 val2) ...) ids val)))))

(define-syntax match-letrec-two-step
  (syntax-rules ()
    ((_ next (rewrites ...) ids val var)
     (match-letrec-two next (rewrites ... (var val)) ids))))

;; This is where the work is done.  To rewrite all occurrences of any
;; id with its tmp, we need to walk the expression, using CPS to
;; restore the original structure.  We also need to be careful to pass
;; the tmp directly to the macro doing the insertion so that it
;; doesn't get renamed.  This trick was originally found by Al*
;; Petrofsky in a message titled "How to write seemingly unhygienic
;; macros using syntax-rules" sent to comp.lang.scheme in Nov 2001.

(define-syntax match-rewrite
  (syntax-rules (quote)
    ((match-rewrite (quote x) ids (k ...))
     (k ... (quote x)))
    ((match-rewrite (p . q) ids k)
     (match-rewrite p ids (match-rewrite2 q ids (match-cons k))))
    ((match-rewrite () ids (k ...))
     (k ... ()))
    ((match-rewrite p () (k ...))
     (k ... p))
    ((match-rewrite p ((id tmp) . rest) (k ...))
     (match-bound-identifier=? p id (k ... tmp) (match-rewrite p rest (k ...))))
    ))

(define-syntax match-rewrite2
  (syntax-rules ()
    ((match-rewrite2 q ids (k ...) p)
     (match-rewrite q ids (k ... p)))))

(define-syntax match-cons
  (syntax-rules ()
    ((match-cons (k ...) p q)
     (k ... (p . q)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Otherwise COND-EXPANDed bits.

(cond-expand
 (chibi
  (define-syntax m?...
    (er-macro-transformer
     (lambda (expr rename compare)
       (if (compare '... (cadr expr))
           (car (cddr expr))
           (cadr (cddr expr))))))
  (define-syntax m?id
    (er-macro-transformer
     (lambda (expr rename compare)
       (if (identifier? (cadr expr))
           (car (cddr expr))
           (cadr (cddr expr))))))
  (define-syntax match-bound-identifier=?
    (er-macro-transformer
     (lambda (expr rename compare)
       (if (eq? (cadr expr) (car (cddr expr)))
           (cadr (cddr expr))
           (car (cddr (cddr expr))))))))

 (chicken
  (define-syntax m?...
    (er-macro-transformer
     (lambda (expr rename compare)
       (if (compare '... (cadr expr))
           (car (cddr expr))
           (cadr (cddr expr))))))
  (define-syntax m?id
    (er-macro-transformer
     (lambda (expr rename compare)
       (if (and (symbol? (cadr expr)) (not (keyword? (cadr expr))))
           (car (cddr expr))
           (cadr (cddr expr))))))
  (define-syntax match-bound-identifier=?
    (er-macro-transformer
     (lambda (expr rename compare)
       (if (eq? (cadr expr) (car (cddr expr)))
           (cadr (cddr expr))
           (car (cddr (cddr expr))))))))

 (else
  ;; Portable versions
  ;;
  ;; This is the R7RS version.  For other standards, and
  ;; implementations not yet up-to-spec we have to use some tricks.
  ;;
  ;;   (define-syntax m?...
  ;;     (syntax-rules (...)
  ;;       ((_ ... sk fk) sk)
  ;;       ((_ x sk fk) fk)))
  ;;
  ;; This is a little more complicated, and introduces a new let-syntax,
  ;; but should work portably in any R[56]RS Scheme.  Taylor Campbell
  ;; originally came up with the idea.
  (define-syntax m?...
    (syntax-rules ()
      ;; these two aren't necessary but provide fast-case fails
      ((m?... (a . b) success-k fail-k) fail-k)
      ((m?... #(a ...) success-k fail-k) fail-k)
      ;; matching an atom
      ((m?... id success-k fail-k)
       (let-syntax ((ellipsis? (syntax-rules ()
                                 ;; iff `id' is `...' here then this will
                                 ;; match a list of any length
                                 ((ellipsis? (foo id) sk fk) sk)
                                 ((ellipsis? other sk fk) fk))))
         ;; this list of three elements will only match the (foo id) list
         ;; above if `id' is `...'
         (ellipsis? (a b c) success-k fail-k)))))

  ;; This is portable but can be more efficient with non-portable
  ;; extensions.  This trick was originally discovered by Oleg Kiselyov.
  (define-syntax m?id
    (syntax-rules ()
      ;; fast-case fails, lists and vectors are not identifiers
      ((_ (x . y) success-k fail-k) fail-k)
      ((_ #(x ...) success-k fail-k) fail-k)
      ;; x is an atom
      ((_ x success-k fail-k)
       (let-syntax
           ((sym?
             (syntax-rules ()
               ;; if the symbol `abracadabra' matches x, then x is a
               ;; symbol
               ((sym? x sk fk) sk)
               ;; otherwise x is a non-symbol datum
               ((sym? y sk fk) fk))))
         (sym? abracadabra success-k fail-k)))))

  ;; This check is inlined in some cases above, but included here for
  ;; the convenience of match-rewrite.
  (define-syntax match-bound-identifier=?
    (syntax-rules ()
      ((match-bound-identifier=? a b sk fk)
       (let-syntax ((b (syntax-rules ())))
         (let-syntax ((eq (syntax-rules (b)
                            ((eq b) sk)
                            ((eq _) fk))))
           (eq a))))))
  ))
