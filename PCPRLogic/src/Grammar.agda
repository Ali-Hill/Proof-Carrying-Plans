module Grammar {Action : Set} {R : Set} {C : Set} where

-- R is a predicate

open import Agda.Builtin.Nat hiding (_*_ ; _+_ ; _-_; zero)
open import Data.Vec hiding (_++_; remove)
open import Data.List hiding (any)
open import Data.Product

--This data type describes a plan which is a non-empty sequence of Actions
 
--  _||_ : Action -> f -> f -- this is for concurrent actions which we currently do not use
--infixl 4 _||_

data f : Set where
  shrink : f
  act  : Action -> f
  join : f -> f -> f --changed from join f -> f -> f to Action -> f -> f for comparison of semantics

----------------------------------------------------------------------------------------------

-- Old Implementation

data Form : Set where
  _∧_ : Form → Form → Form
  ¬_ : R  → Form
  atom : R → Form
infixl 4 _∧_
infixl 5 ¬_

---------------------------------------------------------
-- Figure 4. Possible worlds
--

-- Polarity
data Polarity : Set where
  + - : Polarity

-- Negation of polarities
neg : Polarity → Polarity
neg + = -
neg - = +


-- A pair containing a predicate and polarity
PredMap : Set
PredMap = (Polarity × R)


-- A list containing pairs of polarities and predicates
State = List PredMap

open import Data.Unit


--validS : State -> Set
--validS [] = ⊤
--validS ((z , r) ∷ S) = r ∉S S × validS S


-- Is a given state satisfied in a world.
-- A state is satisfied if for all positive polarities
-- of a predicate the predicate exists in the world and
-- for all negative polatities the predicate does not exist
-- in the world.

-- Context
Γ : Set
Γ = Action → State × State

-- Logical expressions involving equality
data exp : Set where
  _¬L_ : (a b : C) -> exp
  _=L_ : (a b : C) -> exp

record ActionDescription : Set where
  field
    expressions : List exp
    preconditions : State
    postconditions : State

Γₑ : Set
Γₑ = Action → ActionDescription


-- Adding Expressions to the Context
--Γₑ : Set
--Γₑ = Action → (List exp) × (State × State)


--------------------------------------------------------
-- Declarative (possible world) semantics
--

World : Set
World = List R


open import Data.List.Membership.Propositional
--open import Data.List.Any.Membership.Propositional

-- Entailment Relation
infix 3 _⊨[_]_
data _⊨[_]_ : World → Polarity → Form → Set where
  flip : ∀{w t A} → w ⊨[ neg t ] (atom A) → w ⊨[ t ] ¬ A
  both : ∀{w t P Q} → w ⊨[ t ] P → w ⊨[ t ] Q → w ⊨[ t ] P ∧ Q
  somewhere : ∀{w a} → a ∈ w → w ⊨[ + ] atom a
  nowhere : ∀{w a} → a ∉ w → w ⊨[ - ] atom a


open import Data.List.Membership.Propositional

-- Operational Semantics: normalisation function
infixr 3 _↓[_]_
_↓[_]_ : Form → Polarity → State → State
P ∧ Q ↓[ t ] N = Q ↓[ t ] P ↓[ t ] N
¬ x ↓[ t ] N = (neg t , x) ∷ N
atom x ↓[ t ] N = (t , x) ∷ N


_∈⟨_⟩ : World → State → Set
w ∈⟨ S ⟩ = (∀ a → (+ , a) ∈ S → a ∈ w) × (∀ a → (- , a) ∈ S → a ∉ w)

--------------------------------------------------------
