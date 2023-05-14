open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _↝_)
open import Data.List hiding (any)

module Proofs.Soundness_Of_Evaluation {Action : Set} {R : Set} {C : Set} {isDE : IsDecEquivalence {A = R} (_≡_) }
                                              {isDEC : IsDecEquivalence {A = C} (_≡_) }
                                              {isDECA : IsDecEquivalence {A = Action} (_≡_) }  where

open import Grammar {Action} {R} {C}
open import PCPLogic {Action} {R} {C} {isDE} {isDEC} {isDECA}
open import Proofs.Soundness_Of_Evaluation_Normalised 
open import Proofs.Possible_World_Soundness
open import ActionHandler

---------------------------------------------------------------
--  Soundness of evaluation
--

_↓₊ : Form → State
P ↓₊ = P ↓[ + ] []

sound' : ∀{Γ fs P Q σ}
       → WfHandlerₑ Γ σ 
       → Γ , (P ↓₊) ↝ (Q ↓₊) ¦ fs
       → ∀{w} → w ⊨[ + ] P
       → ⟦ fs ⟧ σ w ⊨[ + ] Q
sound' {Γ}{f}{P}{Q}{σ} wfσ Γ⊢f∶P↓₊↝Q↓₊ {w} w⊨₊P = ↓-sound h
  where h : ⟦ f ⟧ σ w ∈⟨ Q ↓₊ ⟩
        h = sound wfσ Γ⊢f∶P↓₊↝Q↓₊ (↓-complete w⊨₊P)

