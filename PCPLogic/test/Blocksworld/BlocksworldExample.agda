open import Blocksworld.Blocksworld
open import Plans.Semantics blocksworldDomain
open import Plans.Plan blocksworldDomain
open import Plans.Subtyping Predicate _≟ₚ_
open import Plans.MembershipAndStateTyped blocksworldDomain
open import Plans.ActionHandler blocksworldDomain

open import Data.List
open import Data.Product
open import Data.Maybe
open import Data.List.Relation.Unary.Any
open import Agda.Builtin.Equality


module Blocksworld.BlocksworldExample where

_↓₊ : Form → State
P ↓₊ = P ↓[ + ] []

-- Initial State
F₁ : Form
F₁ = atom (onTable a) ∧ atom (onTable b) ∧ atom (onTable c) ∧
  atom (clear a) ∧ atom (clear b) ∧ atom (clear c) ∧ atom handEmpty

-- Goal State
F₂ : Form
F₂ = atom (on a b) ∧ atom (on b c)

-- Plan
plan₁ : Plan
plan₁ = pickup_from_table b ∷ putdown_on_stack b c ∷ pickup_from_table a
        ∷ putdown_on_stack a b ∷ halt

Derivation : Γ ⊢ (F₁ ↓₊) ↝ (F₂ ↓₊) ∶ plan₁
Derivation =
  seq
    (λ { (here refl) → here refl
         ; (there (here refl)) → there (there (there (there (there (here refl)))))
         ; (there (there (here refl))) → there (there (here refl))})
  (seq (λ { (here refl) → there (there (there (here refl)))
          ; (there (here refl)) → there (there (there (there (here refl))))})
  (seq (λ { (here refl) → there (there (there (here refl)))
          ; (there (here refl))
            → (there (there (there (there (there (there (there (there (here refl)))))))))
          ; (there (there (here refl)))
            → there (there (there (there (there (there (here refl))))))})
  (seq (λ { (here refl) → there (there (there (here refl)))
          ; (there (here refl))
            → (there (there (there (there (there (there (there (here refl))))))))})
  (halt λ { (here refl)
            → there (there (there (there (there (there (there (there (here refl))))))))
          ; (there (here refl)) → there (there (here refl))}))))

formula-eval : World
formula-eval = execute plan₁ (canonical-δ Γ) (δα (F₁ ↓[ + ] []) [])
