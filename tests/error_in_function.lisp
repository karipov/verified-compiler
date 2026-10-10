; the error happens deep inside some calls, after building a pair on the heap
(define (f n) (if (zero? n) (left n) (pair n (f (sub1 n)))))
(f 50)
