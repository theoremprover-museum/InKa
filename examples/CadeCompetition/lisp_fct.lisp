
(defun reflections (n a r)

  (cond ((eq n 0) nil)
	(t (let ((rem (remainder (* a n) r)))
	     (cond ((< (/ r 2) rem) (cons (- r rem) (reflections (1- n) a r)))
		   (t  (cons rem (reflections (1- n) a r))))))))


(defun remainder (x y)

  (cond ((eq y 0) x)
	((< x y) x)
	(t (remainder (- x y) y))))


(defun inverse (j p)

  (cond ((eq p 2) (remainder j 2))
	(t (remainder (expt j (- p 2)) 2))))



(defun complement (j a p)

    (remainder (* (inverse j p) a) p))


(defun comp-list (i a r)
 (cond ((eq i 0) nil)
       (t (let ((rec (comp-list (1- i) a r)))
	    (cond ((member i rec) rec)
		  (t (cons (complement i a r) (comp-list (1- i) a r))))))))
