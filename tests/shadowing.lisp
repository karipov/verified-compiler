(define (f x) (let ((x (add1 x))) (let ((y x)) (let ((x true)) (pair x y)))))

(let ((x 1))
  (pair (f x) x))
