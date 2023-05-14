;; taxi domain
;;

(define (domain taxi)
  (:requirements :strips) 
  (:predicates	 (taxi ?t1)
  		 (person ?p1)
		 (location ?l1)
		 (isIn ?obj1 ?l1))
		 
(:action drive_passenger
	:parameters
		(?t1 ?p1 ?l1 ?l2)
	:precondition
		(and
			(isIn ?t1 ?l1)
			(isIn ?p1 ?l1)
			(location ?l1)
			(location ?l2)
			(taxi ?t1)
			(person ?p1))
	:effect
		(and
			(not (isIn ?t1 ?l1))
			(not (isIn ?p1 ?l1))
			(isIn ?t1 ?l2)
			(isIn ?p1 ?l2)))

(:action drive
	:parameters
		(?t1 ?l1 ?l2)
	:precondition
		(and
			(isIn ?t1 ?l1)
			(location ?l1)
			(location ?l2)
			(taxi ?t1))
	:effect
		(and
			(not (isIn ?t1 ?l1))
			(isIn ?t1 ?l2))))			

