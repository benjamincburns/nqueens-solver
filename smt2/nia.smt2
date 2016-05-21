(set-logic UFLIA)

(declare-fun row_for_queen (Int) Int)
(declare-const n Int)
(assert (= n 4))


(assert (forall ((x Int) (y Int)) (ite (or (>= x 0) (< x n) (>= y 0) (< y n))

  ; then
  (and
      (>= (row_for_queen x) 0)
      (< (row_for_queen x) n)
      (or (= x y) (not (= (row_for_queen x) (row_for_queen y))))
)

  ; else
  (= (row_for_queen x) (- 0 1)))))

;(assert (forall ((i Int) (j Int))
   ;(or (= i j) (not (= (row_for_queen i) (row_for_queen j))))))

(check-sat)
(get-model)
(eval (row_for_queen 0))
(eval (row_for_queen 1))
(eval (row_for_queen 2))
(eval (row_for_queen 3))
(eval (row_for_queen 4))
(eval (row_for_queen 5))
(eval (row_for_queen 6))
(eval (row_for_queen 7))
(eval (row_for_queen 8))
(eval (row_for_queen 9))
(eval (row_for_queen 10))
