(library 
  (feature guards)
  (export underscore?
	  dot-dot-one?
	  dot-dot-equal?
	  dot-dot-star?
	  at-sign?
	  ..1
	  ..=
	  ..*
	  @)
    (import (loko))
    (begin
      (include "../auxiliary-syntax.scm")
      (define-auxiliary-keywords ..1 ..= ..* @))
    (define (underscore? x )
      (and (identifier? x) (free-identifier=? x #'_)))

    (define (dot-dot-one? x )
      (and (identifier? x) (free-identifier=? x #'..1)))

    (define (dot-dot-equal? x )
      (and (identifier? x) (free-identifier=? x #'..=)))

    (define (dot-dot-star? x )
      (and (identifier? x) (free-identifier=? x #'..*)))

    (define (at-sign? x )
      (and (identifier? x) (free-identifier=? x #'@))))
