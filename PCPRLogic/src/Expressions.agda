open import Relation.Nullary
open import Data.Empty
open import Data.Unit
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.List

module Expressions {Action : Set} {R : Set} {C : Set} {isDEC : IsDecEquivalence {A = C} (_≡_) } where

open import Grammar {Action} {R} {C}

open IsDecEquivalence isDEC renaming (_≟_ to _=C?_) hiding (refl)

trueExp : exp -> Set
trueExp (a ¬L b) with a =C? b
trueExp (a ¬L .a) | yes refl = ⊥
trueExp (a ¬L b) | no ¬p = ⊤
trueExp (a =L b) with a =C? b
trueExp (a =L .a) | yes refl = ⊤
trueExp (a =L b) | no ¬p = ⊥

decTrueExp : (e : exp) -> Dec (trueExp e)
decTrueExp (a ¬L b) with a =C? b
decTrueExp (a ¬L .a) | yes refl = no (λ z → z)
decTrueExp (a ¬L b) | no ¬p = yes tt
decTrueExp (a =L b) with a =C? b
decTrueExp (a =L .a) | yes refl = yes tt
decTrueExp (a =L b) | no ¬p = no (λ z → z)

trueListExp : List exp -> Set
trueListExp [] = ⊤
trueListExp (x ∷ x₁) with decTrueExp x
trueListExp (x ∷ x₁) | yes p with trueListExp x₁
... | ans = ans
trueListExp (x ∷ x₁) | no ¬p = ⊥

decTrueListExp : (e : List exp) -> Dec (trueListExp e)
decTrueListExp [] = yes tt
decTrueListExp (x ∷ xs) with decTrueExp x
decTrueListExp (x ∷ xs) | yes p with decTrueListExp xs
decTrueListExp (x ∷ xs) | yes p | yes p₁ = yes p₁
decTrueListExp (x ∷ xs) | yes p | no ¬p = no ¬p
decTrueListExp (x ∷ xs) | no ¬p = no (λ z → z)
