(define (f a b c d e)
  (- (+ a (+ b c)) (+ d e)))

(define (g x y)
  (let ((z (f x y x y 1)))
    (pair z (f 10 20 30 (add1 x) (sub1 y)))))

(g 7 9)
