; factorial, with multiplication written in terms of addition
(define (mul a b)
  (if (zero? a) 0 (+ b (mul (sub1 a) b))))

(define (fact n)
  (if (zero? n) 1 (mul n (fact (sub1 n)))))

(fact 10)
