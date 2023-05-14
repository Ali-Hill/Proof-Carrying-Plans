;;Problem Parsing

(with-open-file (my-stream problemfile :direction :input)
	(setq input (read my-stream)))

; Parse function for problems
(defun parseProblem (in)
  (cond
   ((eq nil (car in)))
   ((eq 'define (car in)) (progn (parseProblem (cdr in))))
   ((eq :objects (caar in)) (progn (setq objList (concatenate 'string (objectConvert (cdar in) "") " : C")) (parseProblem (cdr in))))
   ((eq :init (caar in)) (progn (setq init (worldConvert (cdar in) "")) (parseProblem (cdr in))))
   ((eq :goal (caar in)) (progn (setq goal (stateConvert (cdar (cdar in)) "")) (parseProblem (cdr in))))
   (t (parseProblem (cdr in)))

  ))

(defun convert (obj)
	(if (eq nil obj)
		""
		(concatenate 'string " " (stringconvert (string obj)))))

;Convert object list into string
(defun objectConvert (objL st)
	(let* (	(s (convert (car objL)))
					(nst (concatenate 'string st s)))
	(if (cdr objL)
		(objectConvert (cdr objL) nst)
		nst)))

(defun stateConvert (world st)
	(let ((nst (concatenate 'string st "(+ ↝ (" (stringconvert (string (caar world))) (objectConvert (cdar world) "") "))" " ∷ " )))
	(if (cdr world)
		(stateConvert (cdr world) nst)
	  (concatenate 'string nst "[]"))))

(defun worldConvert (world st)
	(let ((nst (concatenate 'string st "(" (stringconvert (string (caar world))) (objectConvert (cdar world) "") ") ∷ " )))
	(if (cdr world)
		(worldConvert (cdr world) nst)
		(concatenate 'string nst "[]"))))


(parseProblem input)

;objlist string
(setq init (concatenate 'string "P = " init))
(setq goal (concatenate 'string "Q = " goal))

;(print objList)
;(print init)
;(print goal)
