open import Relation.Binary
open import Data.List.Membership.Propositional
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary hiding (¬_)
open import Data.Product renaming (_,_ to _↝_)
open import Data.Product
open import Data.List hiding (any)
open import Data.Empty
open import Data.List.Relation.Unary.Any

open import Plans.Domain

module Plans.Proofs.Soundness_Of_EvaluationW (domain : Domain) where

open Domain domain
open import Plans.Semantics domain
open import Plans.PlanW domain 
open import Plans.MembershipAndStateTyped domain
open import Plans.ActionHandlerW domain
open import Plans.Proofs.Possible_World_Soundness domain
open ActionDescription

WfHandler : Context → ActionHandler → Set
WfHandler Γ δ =
  ∀{α w} → w ∈⟨ preconditions (Γ α) ⟩
         → ValidS (effects (Γ α))
         → δ α w ≡ updateWorld (effects (Γ α)) w 
 
sound : ∀{δ w Γ f Q}
      → WfHandler Γ δ
      → Γ ⊢ f ∶ w ↝ Q
      → execute f δ w ∈⟨ Q ⟩
sound wfh (halt w∈⟨Q⟩) = w∈⟨Q⟩
sound wfh (seq w∈⟨P⟩ prf tr) rewrite wfh w∈⟨P⟩ prf = sound wfh tr

canonical-δ : Context → ActionHandler
canonical-δ Γ α = updateWorld (effects (Γ α))

wf-canonical-δ : ∀ Γ → WfHandler Γ (canonical-δ Γ)
wf-canonical-δ Γ w∈⟨P⟩ prf = refl
