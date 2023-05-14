open import Naughty.naughty
open import Plans.Semantics blocksworldDomain
open import Plans.Plan blocksworldDomain
open import Plans.Subtyping Predicate _≟ₚ_
open import Plans.MembershipAndStateTyped blocksworldDomain
open import Data.List
open import Relation.Nullary.Decidable
open import Data.Product
open import Data.List.Relation.Unary.Any

module Naughty.naughtyExample where

plan : Plan
plan = naughty ∷ halt

Q : Form
Q = atom handEmpty ∧ ¬ handEmpty

Derivation : Γ ⊢ [] ↝ (Q ↓[ + ] []) ∶ plan
Derivation = seq (λ { ()}) (halt λ { (here px)
                 → there (here px) ; (there (here px)) → here px})

open import Data.Empty
open import Data.List.Membership.Propositional
open import Agda.Builtin.Equality
open import Plans.Domain
open ActionDescription

postulate
  implicit-consistency-assumption : (z : Polarity) (R : Predicate)
                                       → ∀ S → (z , R) ∈ S → (neg z , R) ∉ S
prop-inconsistent : ⊥
prop-inconsistent =
  implicit-consistency-assumption + handEmpty (effects (Γ naughty))
    (here refl) (there (here refl))
