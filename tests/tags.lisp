(let ((p (pair 1 true)))
  (pair (pair (num? 3) (bool? 3))
    (pair (pair? p) (pair (= (left p) 1) (= (right p) false)))))
