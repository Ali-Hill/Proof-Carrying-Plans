-- Alasdair Hill
-- This file defines Planning languages as types, plans as prrof terms approach to PDDL

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Level

--------------------------------------------------------
--  Definition of formulae, possible world semantics, actions, plans

--
-- The following module declarartion allows to develop the file parametrised on an abstract set R of predicates
-- an an abstract set A of declared actions. The former must have decidable equivalence.

module PCPLogic_no_equality {Action : Set} {R : Set} {C : Set} {isDE : IsDecEquivalence {A = R} (_≡_) }
                                              {isDEC : IsDecEquivalence {A = C} (_≡_) }
                                              {isDECA : IsDecEquivalence {A = Action} (_≡_) } where

-- R is a predicate

open import Agda.Builtin.Nat hiding (_*_ ; _+_ ; _-_; zero)
open import Data.Vec hiding (_++_; remove)
open import Data.List hiding (any)
open import Data.Product

open import Grammar {Action} {R} {C}

open import Membership_And_State {Action} {R} {C} {isDE} {isDEC} {isDECA}

open import Subtyping PredMap isSame

open import Data.Product renaming (_,_ to _↝_)
open Data.List renaming (_∷_ to _*_)


data  _,_¦_ :  Γ -> (State × State) -> f -> Set where
    weakening : ∀{Γ P Q fs} ->  (P' : State) -> P <: P' -> ValidState P' -> Γ , P ↝ Q ¦ fs -> Γ , P' ↝ Q ¦ fs
    applyAction : ∀ {Γ f} -> ValidState (proj₁ (Γ f)) -> ValidState (proj₂ (Γ f)) -> Γ , Γ f ¦ act f
    composition : ∀ {Γ P Q Q' R fs f'} -> Q' <: Q -> Γ , P ↝ Q ¦ fs -> Γ , Q' ↝ R ¦ f' -> Γ , P ↝ R ¦ join fs f'
    frame : ∀ {Γ P Q f } -> (z : Polarity) -> (a : R) -> a ∉S P -> a ∉S Q -> Γ , P ↝  Q  ¦ act f
                                                                              -> Γ , ((z , a) * P) ↝  ((z , a) * Q)  ¦ act f --this is a restriction on the normal frame rule

    shrink :  ∀ {Γ P Q} -> (ValidState P) -> (ValidState Q) -> Q <: P ->  Γ , P ↝ Q ¦ shrink
