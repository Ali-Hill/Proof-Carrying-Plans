(defun drink(n1 n2 l11 l12 l13 l21 l22) (cons (cons `(locale ,n1 ,l11) (cons `(attacks ,l12 ,l11) (cons `(attacks ,l13 ,l12) (cons `(locale ,n2 ,l21) (cons `(attacks ,l21 ,l22) nil))))) (cons `(not (locale ,n1 ,l11)) (cons `(locale ,n1 ,l12) (cons `(not (locale ,n2 ,l21)) (cons `(locale ,n2 ,l22) nil))))))
(defun succumb(c v n s1 s2) (cons (cons `(fears ,c ,v) (cons `(pain ,c) (cons `(pleasure ,v) (cons `(craves ,v ,n) (cons `(food ,n) (cons `(harmony ,v ,s1) (cons `(orbits ,s1 ,s2) nil))))))) (cons `(not (fears ,c ,v)) (cons `(craves ,c ,n) (cons `(not (harmony ,v ,s1)) (cons `(harmony ,v ,s2) nil))))))
(defun feast(v n1 n2 l1 l2) (cons (cons `(craves ,v ,n1) (cons `(food ,n1) (cons `(pleasure ,v) (cons `(eats ,n1 ,n2) (cons `(food ,n2) (cons `(locale ,n1 ,l2) (cons `(attacks ,l1 ,l2) nil))))))) (cons `(not (craves ,v ,n1)) (cons `(craves ,v ,n2) (cons `(not (locale ,n1 ,l2)) (cons `(locale ,n1 ,l1) nil))))))
(defun overcome(c v n s1 s2) (cons (cons `(pain ,c) (cons `(pleasure ,v) (cons `(craves ,c ,n) (cons `(craves ,v ,n) (cons `(food ,n) (cons `(harmony ,v ,s2) (cons `(planet ,s2) (cons `(orbits ,s1 ,s2) (cons `(planet ,s1) nil))))))))) (cons `(not (craves ,c ,n)) (cons `(fears ,c ,v) (cons `(not (harmony ,v ,s2)) (cons `(harmony ,v ,s1) nil))))))
