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
			  #'kf)))))))
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
		  (match-two v (q rec p ...) g+s sk fk i)))
    ((match-at-sign . x)
     (match-two . x))))

;;; ok, after a good night's sleep it occurs to me how to integrate these.
;;; using Adam's technique (I had a feeling...)
(cond-expand
  (r7rs)
  (r6rs
    (define (underscore? x )
      (and (identifier? x) (free-identifier=? x #'_)))

    (define (dot-dot-one? x )
      (and (identifier? x) (free-identifier=? x #'..1)))

    (define (dot-dot-equal? x )
      (and (identifier? x) (free-identifier=? x #'..=)))

    (define (dot-dot-star? x )
      (and (identifier? x) (free-identifier=? x #'..*)))

    (define (at-sign? x )
      (and (identifier? x) (free-identifier=? x #'@)))))

(cond-expand
  (r7rs
    (define-syntax match-prob
      (syntax-rules (_ ..1 ..* ..= @)
	((match-prob v _ g+s (sk ...) fk i)
	 (sk ... i))
	((match-prob v (p ..1) g+s sk fk i)
	 (if (pair? v)
	     (match-one v (p ___) g+s sk fk i)
	     fk))
	((match-prob v (p ..= n . r) g+s sk fk i)
	 (match-extract-underscore
	   p
	   (match-gen-ellipsis/range n n v p r g+s sk fk i) i ()))
	((match-prob v (p ..* n m . r) g+s sk fk i)
	 (match-extract-underscore
	   p
	   (match-gen-ellipsis/range n m v p r g+s sk fk i) i ()))
	((match-prob v (@ rec p ...) g+s sk fk i)
	 (if (is-a? v rec)
	     (match-record-named-refs v rec (p ...) g+s sk fk i)
	     fk))
	((match-prob . x)
	 (match-two . x)))))
  (r6rs
    (define-syntax match-prob
      (lambda (stx)
	(syntax-case stx ()
	  ((match-prob v p g+s (sk ...) fk i)
	   (underscore? #'p)
	   #'(sk ... i))
	  ((match-prob v (p q) g+s sk fk i)
	   (dot-dot-one? #'q)
	   #'(if (pair? v)
	         (match-one v (p ___) g+s sk fk i)
	         fk))
	  ((match-prob v (p q n . r) g+s sk fk i)
	   (dot-dot-equal? #'q)
	   #'(match-extract-underscore
	       p
	       (match-gen-ellipsis/range n n v p r g+s sk fk i) i ()))
	  ((match-prob v (p q n m . r) g+s sk fk i)
	   (dot-dot-star? #'q)
	   #'(match-extract-underscore
	       p
	       (match-gen-ellipsis/range n m v p r g+s sk fk i) i ()))
	 ((match-prob v (q rec p ...) g+s sk fk i) 
	  (at-sign? #'q)
	  #'(if (is-a? v rec)
	        (match-record-named-refs v rec (p ...) g+s sk fk i)
	        fk))
	  ((match-prob . x)
	   #'(match-two . x)))))))

;;; now to do the same with match-extract-vars / -underscore

(cond-expand
  (r7rs
    (define-syntax match-extract-prob
      (syntax-rules (_ ..1 ..= ..* @)
	((match-extract-prob (@ rec (f p) ...) . x)
	 (match-extract-prob (p ...) . x))
	((match-extract-prob _ (k ...) i v) (k ... v))
	((match-extract-prob ..1 (k ...) i v)  (k ... v))
	((match-extract-prob ..= (k ...) i v)  (k ... v))
	((match-extract-prob ..* (k ...) i v)  (k ... v))
	((match-extract-prob . x)
	 (match-extract-vars . x)))))
  (r6rs
    (define-syntax match-extract-prob
      (lambda (stx)
	(syntax-case stx ()
	((match-extract-prob (q rec (f p) ...) . x)
	 (at-sign? #'q)
	 #'(match-extract-prob (p ...) . x))
	((match-extract-prob q (k ...) i v)
	 (underscore? #'q)
	 #'(k ... v)) 
	((match-extract-prob q (k ...) i v)  
	 (dot-dot-one? q)
	 #'(k ... v))
	((match-extract-prob q (k ...) i v)  
	 (dot-dot-equal? #'q)
	 #'(k ... v))
	((match-extract-prob q (k ...) i v)  
	 (dot-dot-star? #'q)
	 #'(k ... v))
	((match-extract-prob . x)
	 #'(match-extract-vars . x)))))))

;;; well my second idea didn't work so it's back to the first
(define-syntax match-extract-prob 
  (syntax-rules ()
	((match-extract-prob (q rec (f p) ...) . x)
	 (at-sign? q
		   (match-extract-prob (p ...) . x)
		   (match-extract-vars (q rec (f p) ...) . x)))
	 ((match-extract-prob . x)
	  (match-extract-under . x))))

(define-syntax match-extract-under 
  (syntax-rules ()
	((match-extract-under p (k ...) i v)
	 (underscore? p
		   (k ... v)
		   (match-extract-d-d-1 p (k ...) i v)))
	 ((match-extract-under . x)
	  (match-extract-vars . x))))

(define-syntax match-extract-d-d-1 
  (syntax-rules ()
	((match-extract-d-d-1 p (k ...) i v)
	 (dot-dot-one? p
		   (k ... v)
		   (match-extract-d-d-= p (k ...) i v)))))

(define-syntax match-extract-d-d-= 
  (syntax-rules ()
	((match-extract-d-d-= p (k ...) i v)
	 (dot-dot-equal? p
		   (k ... v)
		   (match-extract-d-d-* p (k ...) i v)))))

(define-syntax match-extract-d-d-* 
  (syntax-rules ()
	((match-extract-d-d-* p (k ...) i v)
	 (dot-dot-equal? p
		   (k ... v)
		   (match-extract-vars p (k ...) i v)))))
