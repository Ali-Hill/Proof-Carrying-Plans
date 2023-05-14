open import Relation.Binary
open import Data.List.Membership.Propositional
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary hiding (¬_)
open import Data.Product renaming (_,_ to _↝_)
open import Data.Product
open import Data.List hiding (any)
open import Data.Empty
open import Data.List.Relation.Unary.Any


module Proofs.Soundness_Of_Evaluation_Normalised {Action : Set} {R : Set} {C : Set} {isDE : IsDecEquivalence {A = R} (_≡_) }
                                              {isDEC : IsDecEquivalence {A = C} (_≡_) }
                                              {isDECA : IsDecEquivalence {A = Action} (_≡_) }  where

open import Grammar {Action} {R} {C}
open import PCPLogic {Action} {R} {C} {isDE} {isDEC} {isDECA}
open import Membership_And_State {Action} {R} {C} {isDE} {isDEC} {isDECA}
open import Subtyping PredMap isSame
open import Expressions {Action} {R} {C} {isDEC}
open import Proofs.Consistency {Action} {R} {C} {isDE} {isDEC} {isDECA}

open ActionDescription

--Proof that an actions preconditions are always a subtype of pre-state, p , in a given contstruction of our semantics
preSatP : ∀ Γₑ p q f -> Γₑ , p ↝ q ¦ act f -> p <: (preconditions (Γₑ f))
preSatP Γₑ p q f₁ (weakening .p x₁ x₂ x) with preSatP Γₑ _ q f₁ x
... | ans = transSub p _ _ x₁ ans
preSatP Γₑ p q f₁ (applyAction e x x₁) = reflSub p
preSatP Γₑ ((z ↝ a) ∷ p) ((z ↝ a) ∷ q) f₁ (frame z a x x₁ x₂) with preSatP Γₑ p q f₁ x₂
... | ans = <:atom _ p (z , a) ans



--Proof that an actions postconditions are always a subtype of post-state, q , in a given contstruction of our semantics
postSatQ : ∀ Γₑ p q f -> Γₑ , p ↝ q ¦ act f -> q <: (postconditions (Γₑ f))
postSatQ Γₑ₁ p q f₁ (weakening .p x₁ x₂ x) with postSatQ Γₑ₁ _ q f₁ x
... | ans = ans
postSatQ Γₑ p q f₁ (applyAction e x x₁) = reflSub q
postSatQ Γₑ ((z ↝ a) ∷ p) ((z ↝ a) ∷ q) f₁ (frame z a x x₁ x₂) with postSatQ Γₑ p q f₁ x₂
... | ans = <:atom _ q (z , a) ans




open import Data.Sum

-------------------------------------------------------------------

--Action Handler

open import ActionHandler {Action} {R} {C} {isDE} {isDEC} {isDECA}

-- If some state M is satisfied in the world w and we have another state N
-- that is a subtype of M then N is also satisfied in the world
<:-resp-∈ : ∀{N M} → M <: N → ∀{w} → w ∈⟨ M ⟩ → w ∈⟨ N ⟩
<:-resp-∈ ([]<: N) w∈⟨M⟩ = (λ _ ()) , λ _ ()
<:-resp-∈ (atom<: {x}{N}{M} tx∈M N<:M) {w} w∈⟨M⟩ = lt , rt where
  ih : w ∈⟨ N ⟩
  ih = <:-resp-∈ N<:M w∈⟨M⟩
  lt : ∀ a' → (+ , a') ∈ x ∷ N → a' ∈ w
  lt a' (here px) =  proj₁ w∈⟨M⟩ a' (subst (λ tx → tx ∈ M) (Relation.Binary.PropositionalEquality.sym px) tx∈M)
  lt a' (there +a'∈N) = proj₁ ih a' +a'∈N
  rt : ∀ a' → (- , a') ∈ x ∷ N → a' ∉ w
  rt a' (here px) a'∈w =
    proj₂ w∈⟨M⟩ a' (subst (λ tx → tx ∈ M) (Relation.Binary.PropositionalEquality.sym px) tx∈M) a'∈w
  rt a' (there -a'∈N) a'∈w = proj₂ ih a' -a'∈N a'∈w

open import AnyLemma

PostSubO : (P : State) -> (Q : State) -> (P ⊔N Q) <: Q
PostSubO P [] = []<: P
PostSubO P  (q ∷ Q) with isInState (proj₂ q) P
... | no ¬p = atom<: (here refl) (<:atom Q ((P ⊔N Q)) q (PostSubO P Q))
... | yes p = atom<: (here refl) (<:atom Q (((P AnyLemma.─ p)) ⊔N Q) q (PostSubO ((P AnyLemma.─ p)) Q))

-- If P override Q is satisfied in a world then Q is also satsfied in that world
PostSatO : (σ : ActionHandler) -> (f : Action) -> (w : World) -> (P : State) -> (Q : State) ->  (Γₑ₁ : Γₑ) -> σ f w ∈⟨ P ⊔N Q ⟩ ->  σ f w ∈⟨ Q ⟩
PostSatO σ f₁ w P Q Γₑ₁ x = <:-resp-∈ (PostSubO P Q) x

-- If we have a well formed handler and an action and the pre-conditions of an action are satsfied in a given world then we can apply
-- the ActionHandler to produce a world where the post-conditions are satisfied.
open import Agda.Builtin.Unit

wellFormedApplication : (σ : ActionHandler) -> (w : World) -> (Γ₁ : Γₑ) -> (f : Action) -> WfHandlerₑ Γ₁ σ
                                               -> ValidState ((preconditions (Γ₁ f)))
                                               -> ValidState ((postconditions (Γ₁ f)))
                                               -> w ∈⟨ (preconditions (Γ₁ f)) ⟩
                                               -> trueListExp (expressions (Γ₁ f))
                                               ->  σ f w ∈⟨ (postconditions (Γ₁ f)) ⟩
wellFormedApplication σ w Γ₁ f₁ WfH vp vq w∈⟨P⟩ eSat with WfH (preSatP Γ₁ ((preconditions (Γ₁ f₁))) ((postconditions (Γ₁ f₁))) f₁ (applyAction eSat vp vq)) w∈⟨P⟩ eSat vq 
wellFormedApplication σ w Γ₁ f₁ x vp vq x₁ eSat | ans = PostSatO σ f₁ w ((preconditions (Γ₁ f₁))) ((postconditions (Γ₁ f₁))) Γ₁ ans


-- If a State, (s :: S), is satisfied in a world then we can Weaken the result to show that S will also be satisfiedw
weakHelp : (w : World) -> (s : PredMap) -> (S : State) -> w ∈⟨ s ∷ S ⟩ -> w ∈⟨ S ⟩
weakHelp w s S w∈⟨s∷S⟩ = <:-resp-∈ (<:atom S S s (reflSub S)) w∈⟨s∷S⟩

open IsDecEquivalence isDE hiding (refl)

-- Helper lemma
subProofHelp : (a : R) -> (z : Polarity) -> (P : State) -> a ∈S ((z , a) ∷ P)
subProofHelp a z P with a ≟ a
subProofHelp a z P | yes p₁ = here refl
subProofHelp a z P | no ¬p = ⊥-elim (¬p refl)  

-- Weakening for state membership
stateMemWeak : (a : R) -> (P : State) -> (s : PredMap) ->  a ∈S P -> a ∈S (s ∷ P)
stateMemWeak a [] s ()
stateMemWeak a (p ∷ P) s x₁ with proj₂ s ≟ a
stateMemWeak .(proj₂ s) (p ∷ P) s x₁ | yes refl = here refl 
stateMemWeak a (p ∷ P) s x₁ | no ¬p = there x₁  

{- Doesn't work with older versions of Agda
test28 : (a : R) -> (p : NPred) -> (x : (Polarity × R)) ->  a ∈S p -> a ∈S (x ∷ p)
test28 a (x₂ ∷ p) x x₁ with proj₂ x ≟ a
test28 .(proj₂ x) (x₂ ∷ p) x x₁ | yes refl = refl
test28 a (x₂ ∷ p) x x₁ | no ¬p = x₁ -}

-- Helper proof for ProofSubIn
membershipHelper : (a : R) -> (z : Polarity) -> (S : State) -> (z , a) ∈ S -> a ∈S S
membershipHelper a z .((z ↝ a) ∷ _) (here refl) = subProofHelp a z _
membershipHelper a z (s ∷ S) (there x) = stateMemWeak a S s (membershipHelper a z S x)

ProofSubIn :  (a : R) -> (P : State) -> (Q : State) -> Q <: P -> a ∈S P -> a ∈S Q
ProofSubIn a ((z1 ↝ .a) ∷ P) Q (atom<: x x₁) (here refl) = membershipHelper a z1 Q x
ProofSubIn a ((z1 ↝ a1) ∷ P) Q (atom<: x x₁) (there x₂) = ProofSubIn a P Q x₁ x₂

proofSub : (a : R) -> (P : State) -> (Q : State) -> Q <: P -> a ∉S Q -> a ∉S P
proofSub a (p ∷ P) Q x x₁ x₂ with proj₂ p ≟ a
... | yes p₁ = x₁ (ProofSubIn _ (p ∷ P) Q x x₂)
proofSub .(proj₂ p) (p ∷ P) Q x x₁ (here refl) | no ¬p = x₁ (ProofSubIn _ (p ∷ P) Q x (here refl))
proofSub a (p ∷ P) Q x x₁ (there x₂) | no ¬p = proofSub a P Q (weakSub p P Q x) x₁  x₂

negMemHelp : (a : R) -> (p : PredMap) -> (P : State) -> a ∉S (p ∷ P) -> a ∉S P
negMemHelp a p P x x₁ = x (there x₁)


-- If a predicate, a, is not in Q and a predMap containing a is in P then that predMap will still exist after P is overriden by Q
-- This defines predMapMemership using the override operator defined with minus
predMapMembership : (Γₑ₁ : Γₑ) ->  (f₁ : Action) -> (z : Polarity) -> (a : R) -> (P : State) -> (Q : State) -> a ∉S Q -> (z , a) ∈ (((z , a) ∷ P) ⊔N Q)
predMapMembership Γₑ₁ f₁ z a P [] x = here refl
predMapMembership Γₑ₁ f₁ z a P (q ∷ Q) x with proj₂ q ≟ a
predMapMembership Γₑ₁ f₁ z .(proj₂ q) P (q ∷ Q) x | yes refl = ⊥-elim (x (here refl))
predMapMembership Γₑ₁ f₁ z a P (q ∷ Q) x | no ¬p with isInState (proj₂ q) P
... | no ¬p₁ = there (predMapMembership Γₑ₁ f₁ z a P Q λ x₁ → x (there x₁))
... | yes p = there (predMapMembership Γₑ₁ f₁ z a (P AnyLemma.─ p) Q λ x₁ → x (there x₁))


predMapHelp : (P : State) -> (z : Polarity) -> (a : R) -> (x₂ : PredMap) -> (z , a) ∈ P -> (p : (proj₂ x₂) ∈S P) -> Relation.Nullary.¬ ((proj₂ x₂) ≡ a) -> (z , a) ∈ (P AnyLemma.─ p) 
predMapHelp .((z ↝ a) ∷ _) z a x₂ (here refl) (here px) x₁ = ⊥-elim (x₁ px)
predMapHelp .(_ ∷ _) z a x₂ (there x) (here px) x₁ = x
predMapHelp .(_ ∷ _) z a x₂ (here px) (there p) x₁ = here px
predMapHelp (q ∷ Q) z a x₂ (there x) (there p) x₁ = there (predMapHelp Q z a x₂ x p x₁)
 
--proven for full membership
predMapMembership2 : (Γₑ₁ : Γₑ) ->  (f₁ : Action) -> (z : Polarity) -> (a : R) -> (P : State) -> (Q : State) -> a ∉S Q -> (z , a) ∈ P -> (z , a) ∈ P ⊔N Q
predMapMembership2 Γₑ₁ f₁ z a P [] x x₁ = x₁
predMapMembership2 Γₑ₁ f₁ z a P (x₂ ∷ Q) x x₁ with isInState (proj₂ x₂) P
predMapMembership2 Γₑ₁ f₁ z a ((z ↝ a) ∷ P) (q ∷ Q) x (here refl) | no ¬p = there (predMapMembership Γₑ₁ f₁ z a P Q (negMemHelp a q Q x))
predMapMembership2 Γₑ₁ f₁ z a (p ∷ P) (x₂ ∷ Q) x (there x₁) | no ¬p = there (predMapMembership2 Γₑ₁ f₁ z a ((p ∷ P)) Q (negMemHelp a _ Q x) (there x₁)) 
... | yes p with (proj₂ x₂) ≟ a
... | yes refl = ⊥-elim (x (here refl))
... | no ¬p = there (((predMapMembership2 Γₑ₁ f₁ z a ((P AnyLemma.─ p)) Q (negMemHelp a _ Q x) (predMapHelp P z a x₂ x₁ _ ¬p))))


--there (predMapMembership2 Γₑ₁ f₁ z a ((P AnyLemma.─ p)) Q {!!} {!!})

--Any (λ section → proj₂ x₂ ≡ proj₂ section) P

-- If a predicate, a, is not in Q and a predMap containing a is in P then that predMap will be a subtype of P overriden by Q
predMapPreservation : (Γₑ₁ : Γₑ) ->  (f₁ : Action) -> (P : State) -> (Q : State) -> (s : PredMap) -> proj₂ s ∉S Q -> ((s ∷ P) ⊔N Q) <: s ∷ []
predMapPreservation Γₑ₁ f₁ P Q s x₁ = atom<: (predMapMembership Γₑ₁ f₁ (proj₁ s) (proj₂ s) P Q x₁) ([]<: ((s ∷ P) ⊔N Q))

-- If a predicate is not in Q and a PredMap, s, containing that predicate in P and we have a world which satisfies P overriden by Q then the PredMap s is satisfied in that world
framePreservation : ∀{f₁ w P s} -> (Γₑ₁ : Γₑ) -> (σ : ActionHandler) -> (Q : State) -> proj₂ s ∉S Q -> σ f₁ w ∈⟨ (s ∷ P) ⊔N Q ⟩ -> σ f₁ w ∈⟨ (s ∷ []) ⟩
framePreservation {f₁} {w} {P} {s} Γₑ₁ σ Q s∉Sq res = <:-resp-∈ (predMapPreservation Γₑ₁ f₁ P Q s s∉Sq) res

--Now proven for full membership
framePreservation2 : ∀{f₁ w P s} -> (Γₑ₁ : Γₑ) -> (σ : ActionHandler) -> (Q : State) -> s ∈ P -> proj₂ s ∉S Q -> σ f₁ w ∈⟨ P ⊔N Q ⟩ -> σ f₁ w ∈⟨ (s ∷ []) ⟩
framePreservation2 {f₁} {w} {P} {s} Γₑ₁ σ Q s∈P s∉Sq res = <:-resp-∈ (atom<: (predMapMembership2 Γₑ₁ f₁ _ _ P Q s∉Sq s∈P) (([]<: (P ⊔N Q)))) res 

-- If we have derived two results from the same action then we can combine them since they both represents smaller portions of the world
strength : ∀{f₁ w Q } -> (s : PredMap) -> (σ : ActionHandler) -> σ f₁ w ∈⟨ Q ⟩ ->  σ f₁ w ∈⟨ (s ∷ []) ⟩ -> σ f₁ w ∈⟨ s ∷ Q ⟩
strength {f₁} {w} {Q} x σ x₁ x₂ = (λ { a (here px) → proj₁ x₂ a (here px) ; a (there x₃) → proj₁ x₁ a x₃})
                             ↝ λ { a (here px) x₄ → proj₂ x₂ a (here px) x₄ ; a (there x₃) x₄ → proj₂ x₁ a x₃ x₄}

---------------------------------------------------------------
--  Soundness of evaluation of normalised formula
--


alwaysValid : ∀ Γₑ p q f -> Γₑ , p ↝ q ¦ act f -> ValidState ((postconditions (Γₑ f)))
alwaysValid Γₑ₁ p q f₁ (weakening .p x x₁ x₂) = alwaysValid Γₑ₁ _ q f₁ x₂
alwaysValid Γₑ₁ .((preconditions (Γₑ₁ f₁))) .((postconditions (Γₑ₁ f₁))) f₁ (applyAction x x₁ x₂) = x₂ 
alwaysValid Γₑ₁ .((z ↝ a) ∷ _) .((z ↝ a) ∷ _) f₁ (frame z a x x₁ x₂) = alwaysValid Γₑ₁ _ _ f₁ x₂

alwaysTrue : ∀{Γₑ p₁ q₁ f₁} -> Γₑ , p₁ ↝ q₁ ¦ act f₁ -> trueListExp (expressions (Γₑ f₁))
alwaysTrue (weakening x _ x₁ x₂) = alwaysTrue x₂
alwaysTrue (applyAction x vp vq) = x
alwaysTrue (frame z a x x₁ x₂) = alwaysTrue x₂

sound : ∀{w σ p Γₑ fs q}
      → WfHandlerₑ Γₑ σ
      → Γₑ , p ↝ q ¦ fs
      → w ∈⟨ p ⟩
      → ⟦ fs ⟧ σ w ∈⟨ q ⟩
sound  {w} {σ} {p} {Γ} {fs} {q} WfH  (weakening x p1 x₁ x₂) w∈⟨P⟩ with sound WfH x₂ (<:-resp-∈ p1 w∈⟨P⟩) 
... | ans = ans  
sound  {w} {σ} {p} {Γₑ} {fs} {q} WfH (applyAction x₁ vp vq) w∈⟨P⟩ = wellFormedApplication σ w Γₑ _ WfH vp vq w∈⟨P⟩ x₁
sound WfH (composition Γ₁,P↝Q¦f Γ₁,Q↝R¦f') w∈⟨P⟩ = sound WfH Γ₁,Q↝R¦f' (sound WfH Γ₁,P↝Q¦f w∈⟨P⟩)
sound {w} {σ} {p} {Γₑ} {fs} {q} WfH (frame {Γ₁} {p₁} {q₁} {f₁} z a x₁ x₃ x₄ ) x₂ = strength (z ↝ a) σ
                                                                                   (sound WfH x₄ (weakHelp w (z , a) p₁ x₂))
                                                                                   (framePreservation Γₑ σ ((postconditions (Γₑ f₁)))
                                                                                     (proofSub a ((postconditions (Γₑ f₁))) q₁ (postSatQ Γ₁ p₁ q₁ f₁ x₄) x₃)
                                                                                     (WfH (preSatP Γₑ p q f₁ (frame z a x₁ x₃ x₄)) x₂ (alwaysTrue x₄) (alwaysValid _ _ _ _ x₄)))  
sound {w} {σ} {p} {Γ} {fs} WfH (shrink Q' x x₁) x₃ = <:-resp-∈ x₁ x₃
