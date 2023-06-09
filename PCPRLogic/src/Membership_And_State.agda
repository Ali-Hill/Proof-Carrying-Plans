open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Level

module Membership_And_State  {Action : Set} {R : Set} {C : Set} {isDE : IsDecEquivalence {A = R} (_≡_) }
                                              {isDEC : IsDecEquivalence {A = C} (_≡_) }
                                              {isDECA : IsDecEquivalence {A = Action} (_≡_) }  where

open import Grammar {Action} {R} {C}

open import Data.Product
open import Relation.Nullary
open IsDecEquivalence isDEC renaming (_≟_ to _=C?_) hiding (refl)
open import Data.Empty
open import Data.Unit hiding (_≟_)
open IsDecEquivalence isDE hiding (refl)
open import AnyLemma
open import Data.List hiding (any)


-- New Definitions Of Membership -----------------------------------------------------------------

--Defining above using Any instead
{-
_atom≡_ : (a : R) (p : PredMap) -> Set
a atom≡ s = a ≡ proj₂ s

_∈S_ : (a : R) (s : State) -> Set
a ∈S s = Any (a atom≡_) s

isInState  : (a : R) -> (s : State) -> Dec (a ∈S s)
isInState a s = any? (λ x → a ≟ proj₂ x) s
-}
-- Is an atom in a State
_∈S_ : (a : R) (s : State) -> Set
At ∈S [] = ⊥
At ∈S ((t , At') ∷ s) with At' ≟ At
(At ∈S ((t , At') ∷ s)) | yes p = At ≡ At'
(At ∈S ((t , At') ∷ s)) | no ¬p = At ∈S s

-- Is an atom not in a State
_∉S_ : (a : R) (s : State) -> Set
a ∉S s = Relation.Nullary.¬ (a ∈S s)

-- Decidability of an Atom's membership in a State
isInState : (a : R) -> (s : State) -> Dec (a ∈S s)
isInState At [] = no (λ z → z)
isInState At ((t , At') ∷ s) with At' ≟  At
isInState At ((t , .At) ∷ s) | yes refl = yes refl
isInState At ((t , At') ∷ s) | no ¬p = isInState At s
-- uses any in Data.List.Relation.Unary.Any renamed to any? in new version of std lib

------------------------------------------------------------------------------------------------

-- A State is valid if there is no duplicate predicates in the State.
ValidState : State -> Set
ValidState [] = ⊤
ValidState ((t , At') ∷ s) with isInState At' s
ValidState ((t , At') ∷ s) | yes p = ⊥
ValidState ((t , At') ∷ s) | no ¬p = ValidState s

-- Alternate declaration of validity of States. Showing that all states do not contain any duplicate predicates.
validS : State -> Set
validS [] = ⊤
validS ((z , r) ∷ S) = r ∉S S × validS S

-- Proof that validS is equivalent to ValidState
validProof : (S : State) -> validS S -> ValidState S
validProof [] x = tt
validProof ((z , a)  ∷ S) x with isInState a S
validProof ((z , a) ∷ S) (fst , snd) | yes p = fst p
validProof ((z , a) ∷ S) (fst , snd) | no ¬p = validProof S snd

validStateToS :  (S : State) -> ValidState S -> validS S
validStateToS [] x = tt
validStateToS ((z , r) ∷ S) x with isInState r S
validStateToS ((z , r) ∷ S) x | yes p = ⊥-elim x
validStateToS ((z , r) ∷ S) x | no ¬p = ¬p , validStateToS S x

open Data.Product renaming (_,_ to _↝_)
open import Relation.Nullary

-- Decidablity of polarities
decZ : (z : Polarity) -> (z' : Polarity) -> Dec (z ≡ z')
decZ + + = yes refl
decZ + - = no (λ ())
decZ - + = no (λ ())
decZ - - = yes refl

-- Decidablity of PredMaps
isSame : (s : PredMap) -> (s' : PredMap) -> Dec (s ≡ s')
isSame (z , a) (z' , a') with decZ z z' | a ≟ a'
isSame (z ↝ a) (.z ↝ .a) | yes refl | yes refl = yes refl
isSame (z ↝ a) (.z ↝ a') | yes refl | no ¬p = no λ { refl → ¬p refl}
isSame (z ↝ a) (z' ↝ a') | no ¬p | yes p = no λ { refl → ¬p refl}
isSame (z ↝ a) (z' ↝ a') | no ¬p | no ¬p₁ = no λ { refl → ¬p refl}
