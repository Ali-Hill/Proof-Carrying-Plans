open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.List.Membership.Propositional
open import Level
open import Data.Product
open import Relation.Nullary
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.List hiding (any)
open import Data.List.Relation.Unary.Any using (Any; any?; here; there)
open Data.Product renaming (_,_ to _↝_)
open import Relation.Nullary
open import Data.Sum

open import Plans.Domain

module Plans.MembershipAndStateTyped (domain : Domain) where

open Domain domain
open import Plans.Semantics domain


-- New Definitions Of Membership -----------------------------------------------------------------

--Defining above using Any instead
_atom≡_ : (a : Predicate) (p : PredMap) → Set
a atom≡ s = a ≡ proj₂ s

_∈S_ : (a : Predicate) (s : State) → Set
a ∈S s = Any (a atom≡_) s

-- Is an atom not in a State
_∉S_ : (a : Predicate) (s : State) → Set
a ∉S s = Relation.Nullary.¬ (a ∈S s)

isInState  : (a : Predicate) → (s : State) → Dec (a ∈S s)
isInState a s = any? (λ x → a ≟ₚ proj₂ x) s

------------------------------------------------------------------------------------------------
-- Decidablity of polarities
decZ : DecidableEquality Polarity
decZ + + = yes refl
decZ + - = no (λ ())
decZ - + = no (λ ())
decZ - - = yes refl

-- Decidablity of PredMaps
isSame : DecidableEquality PredMap
isSame (z , a) (z' , a') with decZ z z' | a ≟ₚ a'
isSame (z ↝ a) (.z ↝ .a) | yes refl | yes refl = yes refl
isSame (z ↝ a) (.z ↝ a') | yes refl | no ¬p = no λ { refl → ¬p refl}
isSame (z ↝ a) (z' ↝ a') | no ¬p | yes p = no λ { refl → ¬p refl}
isSame (z ↝ a) (z' ↝ a') | no ¬p | no ¬p₁ = no λ { refl → ¬p refl}


del : Predicate → State → State
del x [] = []
del x ((t' , x') ∷ M) with x ≟ₚ x'
del x ((t' , x') ∷ M) | yes p =  del x M
del x ((t' , x') ∷ M) | no ¬p = (t' , x') ∷ del x M

del-spec : ∀ t x N → (t , x) ∉ del x N
del-spec t x [] ()
del-spec t x ((t' , y) ∷ N) tx∈N' with x ≟ₚ y
del-spec t x ((t' , y) ∷ N) tx∈N' | yes p = del-spec t x N tx∈N'
del-spec .t' .y ((t' , y) ∷ N) (here refl) | no ¬p = ¬p _≡_.refl
del-spec t x ((t' , y) ∷ N) (there tx∈N') | no ¬p =  del-spec t x N tx∈N'


del-∈ : ∀{M y x} → x ∈ del y M → x ∈ M
del-∈ {[]}             ()
del-∈ {(t , z) ∷ M}{y} x∈ with y ≟ₚ z
del-∈ {(t , z) ∷ M} {y} x∈ | yes p = there (del-∈ x∈)
del-∈ {(t , z) ∷ M} {y} (here refl) | no ¬p = here _≡_.refl
del-∈ {(t , z) ∷ M} {y} (there x∈) | no ¬p = there (del-∈ x∈)


-- Override operator
_⊔N_ : State → State → State
P ⊔N [] = P
P ⊔N ((z , q) ∷ Q) = (z , q) ∷ del q P ⊔N Q

-- Alternate declaration of validity of States. Showing that all states do not contain any duplicate predicates.
ValidS : State -> Set
ValidS [] = ⊤
ValidS ((z ↝ A) ∷ S) = A ∉S S × ValidS S

ValidS? : (S : State) -> Dec (ValidS S)
ValidS? [] = yes tt
ValidS? ((t , p) ∷ S) with isInState p S
... | yes p₁ = no λ { (fst ↝ snd) → fst p₁}
... | no ¬p with ValidS? S
... | no ¬p₁ = no λ { (fst ↝ snd) → ¬p₁ snd}
... | yes p₁ = yes (¬p ↝ p₁)

-- Helper lemma
subProofHelp : (a : Predicate) -> (z : Polarity) -> (P : State) -> a ∈S ((z , a) ∷ P)
subProofHelp a z P with a ≟ₚ a
subProofHelp a z P | yes p₁ = here refl
subProofHelp a z P | no ¬p = ⊥-elim (¬p refl)

-- Weakening for state membership
stateMemWeak : (a : Predicate) -> (P : State) -> (s : PredMap) ->  a ∈S P -> a ∈S (s ∷ P)
stateMemWeak a [] s x₁ = there x₁
stateMemWeak a (p ∷ P) s x₁ with proj₂ s ≟ₚ a
stateMemWeak .(proj₂ s) (p ∷ P) s x₁ | yes refl = here refl
stateMemWeak a (p ∷ P) s x₁ | no ¬p = there x₁

membershipHelper : (a : Predicate) -> (z : Polarity) -> (S : State) -> (z , a) ∈ S -> a ∈S S
membershipHelper a z .((z , a) ∷ _) (here refl) = subProofHelp a z _
membershipHelper a z (s ∷ S) (there x) = stateMemWeak a S s (membershipHelper a z S x)

del-∈S : ∀{M y x} → x ∈S del y M → x ∈S M
del-∈S {(t , p) ∷ M} {y} x with y ≟ₚ p
... | yes p₁ = there (del-∈S x)
del-∈S {(t , p) ∷ M} {y} (here refl) | no ¬p = here refl
del-∈S {(t , p) ∷ M} {y} (there x) | no ¬p = there (del-∈S x)


⊔-union : ∀{N t x M} → (t , x) ∈ M ⊔N N → (t , x) ∈ M × (neg t , x) ∉ N ⊎ (t , x) ∈ N
⊔-union {[]} x∈M = inj₁ (x∈M , λ ())
⊔-union {x ∷ N} (here refl)   = inj₂ (here _≡_.refl)
⊔-union {x ∷ N}{t}{y}{M} (there x∈M⊔N) = h (⊔-union {N}{t}{y} x∈M⊔N)
  where h : (t , y) ∈ del (proj₂ x) M × (neg t , y) ∉ N ⊎ (t , y) ∈ N → (t , y) ∈ M × (neg t , y) ∉ x ∷ N ⊎ (t , y) ∈ x ∷ N
        h (inj₁ (ty∈ , -ty∉N)) = inj₁ (del-∈ ty∈ , h') where
          h' : (neg t , y) ∉ x ∷ N
          h' (here refl) = del-spec t y M ty∈
          h' (there -ty∈N) = -ty∉N -ty∈N
        h (inj₂ pf) = inj₂ (there pf) 
