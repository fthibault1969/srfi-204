(import (srfi :204)
	(srfi :64)
	(srfi :0)
	(loko))
(define scheme-version-name (string-append "loko" (loko-version)))
(define test-name "loko-match-test")
(include "match-common.scm")

;;; set library directories via environment