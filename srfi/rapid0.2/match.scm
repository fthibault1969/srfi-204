(import (rapid))
(define-library (rapid0.2 match)
  (import (rapid))
  (export match match-lambda match-lambda* match-let match-letrec match-let*
	  ___ ..1 ..= ..* *** ? $ struct object get!)
  (include "auxiliary-syntax.scm")
  (begin
    (define-auxiliary-keywords ___ ..1 ..= ..* *** ? $ struct object get!))
  (include "srfi-204/srfi-204.scm"))

(display '(match '(mom dad sis bro)
       ((date night . kids-stay-home) (list date night))))
(newline)

(display (match '(mom dad sis bro)
       ((date night . kids-stay-home) (list date night))))
(newline)
;;should be (mom dad) 
