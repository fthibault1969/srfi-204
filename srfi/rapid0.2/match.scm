(import (scheme base))
(define-library (rapid0.2 match)
  (import (rapid))
  (export match match-lambda match-lambda* match-let match-letrec match-let*)
  (include "match/match.scm"))

(display '(match '(mom dad sis bro)
       ((date night . kids-stay-home) (list date night))))
(newline)

(display (match '(mom dad sis bro)
       ((date night . kids-stay-home) (list date night))))
(newline)
;;should be (mom dad) 