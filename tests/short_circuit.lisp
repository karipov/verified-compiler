; `and` and `or` don't evaluate the second half when they don't need to, so the infinite loop
; never runs
(define (loop x) (loop x))

(pair (and false (loop 1)) (or true (loop 2)))
