;;Warning. I am using case sensitive lisp for more pretty parsing.

;(setq domainfile "blocksworld-domain.pddl")
;(setq problemfile "blocksworld-problem.pddl")
;(setq outputfile "blocksworld")


(defun stringconvert (st)
  (let ((s st))

  (when (eq #\? (char s 0))
    (setq s (subseq s 1)))

  (if (upper-case-p (char s 0))
      (string-downcase s)
      s)
))

(load "../auto/domain_agda")
(load "../auto/problem_agda")

;(print objList)
;(print init)
;(print goal)
;(print predicates)
;(print actionList)
;(print context)

;(setf (readtable-case *readtable*) :preserve)
;(SETQ help (READ))
;(SETF (READTABLE-CASE *READTABLE*) :INVERT)
;(print HELP)
;(exit)


;Potential problem with and on the goal still needs fixed

(with-open-file ( my-stream (concatenate 'string outputfile ".agda") :direction :output)
  ;module
  (write-line (concatenate 'string "module " outputfile " where") my-stream)

  ;imports
  (write-line "" my-stream)
  (write-line "open import Relation.Binary.PropositionalEquality" my-stream)
  (write-line "open import Relation.Binary" my-stream)
  (write-line "open import Data.List" my-stream)
  (write-line "open import Data.List.Relation.Unary.Any" my-stream)
  (write-line "open import Relation.Nullary using (yes; no; Dec)" my-stream)
  (write-line "open import Level" my-stream)
  (write-line "open import Data.Product" my-stream)
  (write-line "open import Tactic.Deriving.Eq" my-stream)

  ;constants
  (write-line "" my-stream)
  (write-line "data C : Set where" my-stream)
  (write-line objList my-stream)
  (write-line "-- EqC : Eq C" my-stream)
  (write-line "unquoteDecl EqC = deriveEq EqC (quote C)" my-stream)

  ;predicates
  (write-line "" my-stream)
  (write-line "data R : Set where" my-stream)
  (loop for p in predicates
    do (write-line p my-stream))
  (write-line "-- EqR : Eq R" my-stream)
  (write-line "unquoteDecl EqR = deriveEq EqR (quote R)" my-stream)

  ;actions
  (write-line "" my-stream)
  (write-line "data Action : Set where" my-stream)
  (loop for a in actionList
    do (write-line a my-stream))
  (write-line "-- EqAction : Eq Action" my-stream)
  (write-line "unquoteDecl EqAction = deriveEq EqAction (quote Action)" my-stream)


  ;import domain 
  (write-line "open import Plans.Domain.Core Action R" my-stream)

  ;context
  (write-line "" my-stream)
  (write-line "Γ : Context" my-stream)
  (loop for g in context
    do  (write-line g my-stream))

  ;import
  (write-line "" my-stream)
  (write-line "open import Plans.Mangle using (mangle)" my-stream)
  (write-line "open import Plans.Domain" my-stream)
  (write-line "open import Plans.Domain.Core" my-stream)

  ;define domain
  (write-line "" my-stream)
  (write-line (concatenate 'string outputfile "Domain : Domain") my-stream)
  (write-line (concatenate 'string outputfile "Domain = record") my-stream)
  (write-line "  { Predicate = R" my-stream)
  (write-line "  ; Action = Action" my-stream)
  (write-line "  ; Γ = Γ" my-stream)
  (write-line "  ; _≟ₚ_ = mangle }" my-stream)

  ;open domain
  (write-line "" my-stream)
  (write-line (concatenate 'string "open Domain " outputfile "Domain  public") my-stream)
  (write-line "  hiding (Action; Predicate; Γ)" my-stream)

)

(with-open-file ( my-stream (concatenate 'string outputfile "Example.agda") :direction :output)

  ;imports  
  (write-line (concatenate 'string "open import " outputfile) my-stream)
  (write-line (concatenate 'string "open import Plans.Semantics " outputfile "Domain") my-stream)
  (write-line (concatenate 'string "open import Plans.PlanW " outputfile "Domain") my-stream)
  (write-line "open import Data.List" my-stream)
  (write-line "open import Data.Product renaming (_,_ to _↝_)" my-stream)
  (write-line "open import Relation.Nullary.Decidable" my-stream)

  ;module
  (write-line "" my-stream)
  (write-line (concatenate 'string "module " outputfile "Example where") my-stream)

  ;Initial State
  (write-line "" my-stream)
  (write-line "P : World" my-stream)
  (write-line init my-stream)

  ;Goal State
  (write-line "" my-stream)
  (write-line "Q : State" my-stream)
  (write-line goal my-stream)
)

