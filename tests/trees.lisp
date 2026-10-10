; a complete binary tree of depth n, with numbered leaves
(define (tree n k)
  (if (zero? n) k (pair (tree (sub1 n) k) (tree (sub1 n) (+ k (pow2 (sub1 n)))))))

(define (pow2 n)
  (if (zero? n) 1 (+ (pow2 (sub1 n)) (pow2 (sub1 n)))))

(define (leaves t)
  (if (pair? t) (+ (leaves (left t)) (leaves (right t))) 1))

(define (total t)
  (if (pair? t) (+ (total (left t)) (total (right t))) t))

(let ((t (tree 10 0)))
  (pair (leaves t) (pair (total t) (tree 2 0))))
