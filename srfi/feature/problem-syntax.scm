;;; problem-syntax.scm handle the rest of the problematic syntax
;;; portably in r6rs and r7rs: specifically:
;;; ..1 ..= ..* @

(cond-expand
  (r7rs
    (define-syntax dot-dot-one?
      (syntax-rules (..1)
	((_ ..1 kt kf) kt)
	((_ x kt kf) kf))))
  (r6rs
    (define-syntax dot-dot-one?
      (lambda (stx)
	(syntax-case stx ()
		     ((_ x kt kf)
		      (if (and (identifier? #'x)
			       (free-identifier=? #'x #'..1))
			  #'kt
			  #'kf)))))))i
(cond-expand
  (r7rs
    (define-syntax dot-dot-equal?
      (syntax-rules (..=)
	((_ ..= kt kf) kt)
	((_ x kt kf) kf))))
  (r6rs
    (define-syntax dot-dot-equal?
      (lambda (stx)
	(syntax-case stx ()
		     ((_ x kt kf)
		      (if (and (identifier? #'x)
			       (free-identifier=? #'x #'..=))
			  #'kt
			  #'kf)))))))
(cond-expand
  (r7rs
    (define-syntax dot-dot-star?
      (syntax-rules (..*)
	((_ ..* kt kf) kt)
	((_ x kt kf) kf))))
  (r6rs
    (define-syntax dot-dot-star?
      (lambda (stx)
	(syntax-case stx ()
		     ((_ x kt kf)
		      (if (and (identifier? #'x)
			       (free-identifier=? #'x #'..*))
			  #'kt
			  #'kf)))))))
(cond-expand
  (r7rs
    (define-syntax at-sign?
      (syntax-rules (@)
	((_ @ kt kf) kt)
	((_ x kt kf) kf))))
  (r6rs
    (define-syntax at-sign?
      (lambda (stx)
	(syntax-case stx ()
		     ((_ x kt kf)
		      (if (and (identifier? #'x)
			       (free-identifier=? #'x #'@))
			  #'kt
			  #'kf)))))))

;;;and those macros would be used by these macros

(define-syntax match-underscore
  (syntax-rules ()
    ((match-underscore v p g+s (sk ...) fk i)
     (underscore? p
		  (sk ... i)
		  (match-dot-dot-one v p g+s (sk ...) fk i)))))

(define-syntax match-dot-dot-one
  (syntax-rules ()
    ((match-dot-dot-one v (p q) g+s sk fk i)
     (dot-dot-one? q
		  (if (pair? v)
		      (match-one v (p ___) g+s sk fk i)
		      fk)
		  ; all the others match (p q n . r) so we can go
		  ; from here to match-two
		  (match-two v (p q) g+s sk fk i)))
    ((match-dot-dot-one . x)
     (match-dot-dot-equal . x))))

(define-syntax match-dot-dot-equal
  (syntax-rules ()
    ((match-dot-dot-equal v (p q n . r) g+s sk fk i)
     (dot-dot-equal? q
		  (match-extract-underscore
		    p
		    (match-gen-ellipsis/range n n v p r g+s sk fk i) i ())
		  (match-dot-dot-star v (p q n .r) g+s sk fk i)))
    ((match-dot-dot-equal . x)
     ;since all the others match (p q n . r) we can go to match-two
     (match-two . x))))

(define-syntax match-dot-dot-star
  (syntax-rules ()
    ((match-dot-dot-star v (p q n m . r) g+s sk fk i)
     (dot-dot-star? q
		  (match-extract-underscore
		    p
		    (match-gen-ellipsis/range n m v p r g+s sk fk i) i ())
		  (match-at-sign v (p q n m . r) g+s sk fk i)))
    ((match-dot-dot-star . x)
     (match-at-sign . x))))

(define-syntax match-at-sign
  (syntax-rules ()
    ((match-at-sign v (q rec p ...) g+s sk fk i)
     (at-sign? q
		  (if (is-a? v rec)
		      (match-record-named-refs v rec (p ...) g+s sk fk i)
		      fk)
		  (match-two v p g+s sk fk i)))
    ((match-at-sign . x)
     (match-two . x))))
