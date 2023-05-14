open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary hiding (¬_)
open import Data.Product
open import Data.List hiding (any)
open import Data.Unit
open import Data.Empty


module Proofs.NoEquality.Consistency {Action : Set} {R : Set} {C : Set} {isDE : IsDecEquivalence {A = R} (_≡_) }
                                              {isDEC : IsDecEquivalence {A = C} (_≡_) }
                                              {isDECA : IsDecEquivalence {A = Action} (_≡_) }  where


open import PCPLogic_no_equality {Action} {R} {C} {isDE} {isDEC} {isDECA}
open import Grammar {Action} {R} {C}
open import Membership_And_State {Action} {R} {C} {isDE} {isDEC} {isDECA}

consistency : ∀ Γ P Q fs -> Γ , (P , Q) ¦ fs -> ValidState P × ValidState Q
consistency Γ₁ P Q fs (weakening .P P<:P₁ ValidP P₁↝Q)
            with consistency Γ₁ _ Q fs P₁↝Q
... | ValidP₁ , ValidQ = ValidP , ValidQ
consistency Γ₁ P Q .(act _) (applyAction ValidP ValidQ) =  ValidP , ValidQ
consistency Γ₁ P R .(join _ _) (composition Q<:Q' P↝Q Q'↝R)
            with consistency Γ₁ _ R _ Q'↝R | consistency Γ₁ P _ _ P↝Q
... | ValidQ' , ValidR | ValidP , ValidQ = ValidP , ValidR
consistency Γ₁ ((z , a) ∷ P) ((z , a) ∷ Q) f (frame z a a∉P a∉Q P↝Q)
            with consistency Γ₁ P _ f P↝Q
... | ValidP , ValidQ = (a∉P , ValidP) , (a∉Q , ValidQ)
consistency Γ₁ P Q f (shrink ValidP ValidQ P<:Q) = ValidP , ValidQ
