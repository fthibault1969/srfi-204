(define-library (foment0.4  match)
		(export match match-lambda match-lambda* match-let match-letrec match-let*
			___ ..1 ..= ..* *** ? $ struct object get!)
		(import (scheme base))
		(include "../match/match.scm"))
;;foment -I ..
