;
; Blocksworld Problem 1: build a simple tower
;
; Author: Ron Petrick
;
; A set of blocks (a,b,c,d,e,f) is initially on a table.
; The planner should find a plan to stack the blocks so that
; a is on b, b is on c, c is on d, d is on e, and e is on f.
;
(define (problem blocksworld-problem1)
  (:domain blocksworld)

  (:objects
      a
      b
  )

  (:init
      (onTable a)
      (onTable b)

      (clear a)
      (clear b)

      (handEmpty)
  )

  (:goal
      (and
          (on a b)
      )
  )
)
