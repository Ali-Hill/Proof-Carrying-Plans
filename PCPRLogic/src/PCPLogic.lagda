\begin{code}
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

module PCPLogic {Action : Set} {R : Set} {C : Set} {isDE : IsDecEquivalence {A = R} (_≡_) }
                                              {isDEC : IsDecEquivalence {A = C} (_≡_) }
                                              {isDECA : IsDecEquivalence {A = Action} (_≡_) } where
-- R is a predicate

open import Agda.Builtin.Nat hiding (_*_ ; _+_ ; _-_; zero)
open import Data.Vec hiding (_++_; remove)
open import Data.List hiding (any)
open import Data.Product

open import Grammar {Action} {R} {C} hiding (Γ)

open import Membership_And_State {Action} {R} {C} {isDE} {isDEC} {isDECA}

open import Subtyping PredMap isSame

open import Data.Product renaming (_,_ to _↝_)
open Data.List renaming (_∷_ to _*_)

-----------------------------------------------------------------------

open import Expressions {Action} {R} {C} {isDEC}
open ActionDescription

data  _,_¦_ :  Γₑ → (State × State) → f → Set where
    weakening : ∀{Γₑ P Q fs}
                → (P' : State)
                → P' <: P
                → ValidState P'
                → Γₑ , P ↝ Q ¦ fs
                → Γₑ , P' ↝ Q ¦ fs
    applyAction : ∀ {Γₑ f}
                → trueListExp (expressions (Γₑ f)) 
                → ValidState (preconditions (Γₑ f))
                → ValidState (postconditions (Γₑ f))
                → Γₑ , (preconditions (Γₑ f)) ↝ (postconditions (Γₑ f)) ¦ act f
    composition : ∀ {Γₑ P Q R f f'}
                → Γₑ , P ↝ Q ¦ f
                → Γₑ , Q ↝ R ¦ f'
                → Γₑ , P ↝ R ¦ join f f'
    frame : ∀ {Γₑ P Q f }
                → (z : Polarity)
                → (a : R)
                → a ∉S P
                → a ∉S Q
                → Γₑ , P ↝ Q  ¦ act f
                → Γₑ , ((z , a) ∷ P) ↝ ((z , a) ∷ Q)  ¦ act f 
    shrink :  ∀ {Γₑ P Q}
                → (ValidState P)
                → (ValidState Q)
                → P <: Q
                → Γₑ , P ↝ Q ¦ shrink

\end{code}







