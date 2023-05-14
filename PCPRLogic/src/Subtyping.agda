open import Data.List hiding (any)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.List.Relation.Unary.Any
open import Relation.Nullary
open import Relation.Binary

module Subtyping (A : Set) (decA : DecidableEquality A) where

open import Data.List.Membership.DecPropositional decA

private
  State = List A

-- Subtyping
infix 3 _<:_
data _<:_ : State → State → Set where
  []<:_ : ∀ Q → Q <: []
  atom<: : ∀{a P Q} → a ∈ Q → Q <: P → Q <: a ∷ P

<:atom : (P : State) -> (Q : State) -> (s : A) -> Q <: P -> s ∷ Q <: P
<:atom .[] Q s ([]<: .Q) = []<: (s ∷ Q)
<:atom .(_ ∷ _) Q s (atom<: x x₁) = atom<: (there x) (<:atom _ Q s x₁)

-- Reflexivity of subtyping
reflSub : (S : State) -> S <: S
reflSub [] = []<: []
reflSub (s ∷ S) = atom<: (here refl) (<:atom S S s (reflSub S))

helpTrans : ∀ x -> (P : State) -> (Q : State ) -> x ∈ P -> Q <: P -> x ∈ Q
helpTrans ._ .(_ ∷ _) Q (here refl) (atom<: x x₂) = x
helpTrans x .(_ ∷ _) Q (there x₁) (atom<: x₂ x₃) = helpTrans x _ Q x₁ x₃

transSub : (L : State) -> (M : State) -> (N : State) -> L <: M -> M <: N -> L <: N
transSub L M [] x x₁ = []<: L
transSub L M (._ ∷ N) x (atom<: x₁ x₂) = atom<: (helpTrans _ M L x₁ x) (transSub L M N x x₂)

weakSub : (a : A) -> (P : State) -> (Q : State) ->  Q <: (a ∷ P) -> Q <: P
weakSub a P Q (atom<: x x₁) = x₁

decSub : (P : State) -> (Q : State) -> Dec (P <: Q)
decSub P [] = yes ([]<: P)
decSub P (q ∷ Q) with q ∈? P
... | no ¬p = no (λ { (atom<: x x₁) → ¬p x})
... | yes p with decSub P Q
... | no ¬p = no (λ { (atom<: x x₁) → ¬p x₁})
... | yes p₁ = yes (atom<: p p₁)
