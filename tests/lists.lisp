; lists are nested pairs ending in false
(define (range n)
  (if (zero? n) false (pair n (range (sub1 n)))))

(define (sum l)
  (if (pair? l) (+ (left l) (sum (right l))) 0))

(define (reverse l acc)
  (if (pair? l) (reverse (right l) (pair (left l) acc)) acc))

(pair (sum (range 1000)) (reverse (range 5) false))
