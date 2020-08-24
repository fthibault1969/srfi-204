;;; example for problem with srfi-204-r6rs-2.scm
(define (underscore? x )
  (and (identifier? x) (free-identifier=? x #'_)))

(define-syntax match-underscore
  (lambda (stx)
    (syntax-case stx ()
       ((match-underscore p sk fk)
	(underscore? #'p)
	#'sk)
       ((match-underscore p sk fk)
	#'fk))))
