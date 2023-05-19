open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary hiding (¬_)
open import Data.Product
open import Data.List hiding (any)
open import Data.Unit hiding (_≟_)
open import Data.Empty


module Proofs.Consistency {Action : Set} {R : Set} {C : Set} {isDE : IsDecEquivalence {A = R} (_≡_) }
                                              {isDEC : IsDecEquivalence {A = C} (_≡_) }
                                              {isDECA : IsDecEquivalence {A = Action} (_≡_) }  where


open import PCPLogic {Action} {R} {C} {isDE} {isDEC} {isDECA}
open import Grammar {Action} {R} {C}
open import Membership_And_State {Action} {R} {C} {isDE} {isDEC} {isDECA}

-- A proof showing that our rules will never introduce inconsistency as long as we were given
-- valid actions.
consistency : ∀ {Γ P Q fs} -> Γ , (P , Q) ¦ fs -> validS P × validS Q
consistency (weakening _ P<:P₁ ValidP P₁↝Q) with consistency P₁↝Q
... | ValidP₁ , ValidQ = validStateToS _ ValidP , ValidQ
consistency (applyAction e ValidP ValidQ) =
  (validStateToS _ ValidP) , validStateToS _ ValidQ
consistency (composition P↝Q Q'↝R) with consistency Q'↝R | consistency P↝Q
... | ValidQ' , ValidR | ValidP , ValidQ = ValidP , ValidR  
consistency (frame z a a∉P a∉Q P↝Q) with consistency P↝Q
... | ValidP , ValidQ = (a∉P , ValidP) , (a∉Q , ValidQ)
consistency (shrink ValidP ValidQ P<:Q) =
  (validStateToS _ ValidP) , validStateToS _ ValidQ

open import Subtyping PredMap isSame
open import Data.Product renaming (_,_ to _↝_)

weakComp : ∀{Γₑ P Q Q' R f f'} → Q <: Q' → Γₑ , P ↝ Q ¦ f → Γₑ , Q' ↝ R ¦ f' → Γₑ , P ↝ R ¦ (join f f')
weakComp Q<:Q' h h₁ = composition h (weakening _ Q<:Q' (validProof _ (proj₂ (consistency h))) h₁)

open import ActionHandler {Action} {R} {C} {isDE} {isDEC} {isDECA}
open IsDecEquivalence isDE hiding (refl)
