(import (srfi :204)
	(srfi :64)
	(srfi :0)
	(only (srfi :1) iota)
	(loko))
(define non-linear-pattern #t)
(define non-linear-pred #t)
(define non-linear-field #t)
(define record-implemented #t)
(define scheme-version-name (string-append "loko" (loko-version)))
(define test-name "srfi-test")
(include "r6rs-srfi-common.scm")

;;; set library directories via environment
