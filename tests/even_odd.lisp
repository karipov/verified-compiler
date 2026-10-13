; mutual recursion
(define (even? n) (if (zero? n) true (odd? (sub1 n))))
(define (odd? n) (if (zero? n) false (even? (sub1 n))))

(pair (even? 1000) (odd? 777))
