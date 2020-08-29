(define *counter* 0)

(define-syntax define-record-type/id
  (syntax-rules ()
    ((_ rtd (cname . name*) pred? get get-id . field*)
     (begin
       (define-record-type rtd
	 (%cname id . name*)
	 pred?
	 (id get-id) . field*)
       (define (cname . arg*)
	 (let ((id *counter*))
	   (set! *counter* (+ 1 *counter*))
	   (apply %cname id arg*)))))))

;; Haven't got to work[Guile, Chibi], notified Marc, will do more
;; when I have a working program.
