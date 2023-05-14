open import Relation.Binary.PropositionalEquality
open import Relation.Nullary hiding (¬_)
open import Data.Product
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.List hiding (any)
open import Data.Empty
open import Data.Sum
open import Plans.Domain

module Plans.Proofs.WellFormedCanonical (domain : Domain) where

open Domain domain
open import Plans.Semantics domain
open import Plans.ActionHandler domain
open import Plans.MembershipAndStateTyped domain

∉-tail : {A : Set} {xs : List A} {x y : A} → x ∉ y ∷ xs → x ∉ xs
∉-tail x∉y∷ys x∈ys = x∉y∷ys (there x∈ys)

remove-other : ∀{w x} → x ∈ w → ∀{y} → x ≢ y → x ∈ remove y w
remove-other {[]}    x∈w x≢y = x∈w
remove-other {z ∷ w} x∈w {y} x≢z with y ≟ₚ z
remove-other {z ∷ w} (here _≡_.refl) {y} x≢z | yes p = ⊥-elim (x≢z (sym p))
remove-other {z ∷ w} (there x∈w) {y} x≢z | yes p = remove-other x∈w x≢z
remove-other {z ∷ w} (here px) {y} x≢z | no ¬p = here px
remove-other {z ∷ w} (there x∈w) {y} x≢z | no ¬p = there (remove-other x∈w x≢z)

remove-spec : (x : Predicate) (w : World) → x ∉ remove x w
remove-spec x [] = λ ()
remove-spec x (y ∷ w) with  x ≟ₚ y
remove-spec x (y ∷ w) | yes p = remove-spec x w
remove-spec x (y ∷ w) | no ¬p = contr
  where
    contr : x ∉ y ∷ remove x w
    contr (here x≡y) = ¬p x≡y
    contr (there x∈) = remove-spec x w x∈

remove-resp-∈ : ∀{N x y} → x ∈ remove y N → x ∈ N
remove-resp-∈ {[]}    x∈ = x∈
remove-resp-∈ {z ∷ N}{x}{y} x∈ with y ≟ₚ z
remove-resp-∈ {z ∷ N}{x}{y} x∈ | yes refl = there (remove-resp-∈ {N} x∈)
remove-resp-∈ {z ∷ N} {x} {y} (here refl) | no y≢x = here _≡_.refl
remove-resp-∈ {z ∷ N} {x} {y} (there x∈)  | no y≢x = there (remove-resp-∈ x∈)

remove-resp-∉ : ∀{N x} → x ∉ N → ∀{y} → x ∉ remove y N
remove-resp-∉ {[]}    x∉N x∈N' = x∉N x∈N'
remove-resp-∉ {x ∷ N} x∉N {y} x∈N' with y ≟ₚ x
remove-resp-∉ {x ∷ N} x∉N {.x} x∈N' | yes refl = remove-resp-∉ (∉-tail x∉N) x∈N'
remove-resp-∉ {x ∷ N} x∉N {y} (here refl)  | no x≢y = x∉N (here _≡_.refl)
remove-resp-∉ {x ∷ N} x∉N {y} (there x∈N') | no x≢y = remove-resp-∉ (∉-tail x∉N) x∈N'

sym≢ : {A : Set} → {x y : A} → x ≢ y → y ≢ x
sym≢ x≢y refl = x≢y _≡_.refl

σα-keep : ∀{x w} → x ∈ w → ∀{N} → (- , x) ∉ N → x ∈ updateWorld N w
σα-keep     x∈w {[]}          -x∉N  = x∈w
σα-keep {x} x∈w {(+ , y) ∷ N} -ty∉N = there (σα-keep x∈w (∉-tail -ty∉N))
σα-keep {x} x∈w {(- , y) ∷ N} -ty∉N with x ≟ₚ y
σα-keep {x} x∈w {(- , .x) ∷ N} -ty∉N | yes refl = ⊥-elim (-ty∉N (here _≡_.refl))
σα-keep {x} x∈w {(- , y) ∷ N} -ty∉N  | no x≢y = remove-other (σα-keep x∈w (∉-tail -ty∉N)) x≢y

σα-source : ∀{N x w} → x ∈ updateWorld N w → (+ , x) ∈ N ⊎ x ∈ w
σα-source {[]}          {x} x∈ = inj₂ x∈
σα-source {(+ , y) ∷ N} {x} x∈ with x ≟ₚ y
σα-source {(+ , .x) ∷ N} {x}{w} x∈ | yes refl = inj₁ (here  _≡_.refl)
σα-source {(+ , y) ∷ N}  {x}{w} (here refl) | no y≢y = ⊥-elim (y≢y _≡_.refl)
σα-source {(+ , y) ∷ N}  {x}{w} (there x∈)  | no x≢y = h (σα-source x∈) where
  h : (+ , x) ∈ N ⊎ x ∈ w → (+ , x) ∈ (+ , y) ∷ N ⊎ x ∈ w
  h (inj₁ +x∈N) = inj₁ (there +x∈N)
  h (inj₂ x∈w) = inj₂ x∈w
σα-source {(- ,  y) ∷ N} {x} x∈ with x ≟ₚ y
σα-source {(- , .x) ∷ N} {x}{w} x∈ | yes refl = ⊥-elim (remove-spec x (updateWorld N w) x∈)
σα-source {(- ,  y) ∷ N} {x}{w} x∈ | no x≢y = h (σα-source (remove-resp-∈ x∈)) where
  h : (+ , x) ∈ N ⊎ x ∈ w → (+ , x) ∈ (- , y) ∷ N ⊎ x ∈ w
  h (inj₁ +x∈N) = inj₁ (there +x∈N)
  h (inj₂ x∈w)  = inj₂ x∈w

σα-keep-∉ : ∀{x w} → x ∉ w → ∀{N} → (+ , x) ∉ N → x ∉ updateWorld N w
σα-keep-∉        x∉w {[]}          +x∉N x∈w = x∉w x∈w
σα-keep-∉ {x}{w} x∉w {(+ , y) ∷ N} +x∉N (here refl) = +x∉N (here _≡_.refl)
σα-keep-∉ {x}{w} x∉w {(+ , y) ∷ N} +x∉N (there x∈) = σα-keep-∉ x∉w (∉-tail +x∉N) x∈
σα-keep-∉ {x}{w} x∉w {(- , y) ∷ N} +x∉N x∈ with x ≟ₚ y
σα-keep-∉ {x}{w} x∉w {(- , .x) ∷ N} +x∉N x∈ | yes refl = remove-spec x (updateWorld N w) x∈
σα-keep-∉ {x}{w} x∉w {(- , y) ∷ N}  +x∉N x∈ | no x≢y = h (σα-source (remove-resp-∈ x∈)) where
  h : (+ , x) ∈ N ⊎ x ∈ w → ⊥
  h (inj₁ +x∈N) = +x∉N (there +x∈N)
  h (inj₂ x∈w)  = x∉w x∈w


⊔-right-bias : ∀{N x M} → x ∈ N → x ∈ M ⊔N N
⊔-right-bias {[]}    ()
⊔-right-bias {y ∷ N} (here refl) = here _≡_.refl 
⊔-right-bias {y ∷ N}{x}{M} (there x∈N) = there (⊔-right-bias x∈N) 


open ActionDescription using (preconditions; effects)
open import Agda.Builtin.Unit

--removing inconsistency assumption from insert 
σα-insert : ∀{x} → (N : State) -> (ValidS N) -> (+ , x) ∈ N → ∀ w → x ∈ updateWorld N w
σα-insert (x ∷ N) vs (here refl) w = here refl
σα-insert {x} ((- , y) ∷ N) (vp , vs) (there +x∈N) w with y ≟ₚ x
σα-insert {x} ((- , x) ∷ .((+ , x) ∷ _)) (vp , vs) (there (here refl)) w | yes refl = ⊥-elim (vp (here refl))
σα-insert {x} ((- , x) ∷ .(_ ∷ _)) (vp , vs) (there (there +x∈N)) w | yes refl = ⊥-elim (vp (there (membershipHelper x + _ +x∈N)))
... | no y≢x  = remove-other (σα-insert N vs +x∈N w) (sym≢ y≢x)
σα-insert {x} ((+ , y) ∷ N) (vp , vs) (there +x∈N) w with y ≟ₚ x
... | no ¬p = there (σα-insert N vs +x∈N w)
... | yes refl = here refl

σα-delete : ∀{x} → (N : State) -> (ValidS N) -> (- , x) ∈ N → ∀ w → x ∉ updateWorld N w
σα-delete {x} (s ∷ N) vs (here refl) w = remove-spec x (updateWorld N w)
σα-delete {x} ((+ , y) ∷ N) (vp , vs) (there -x∈N) w with y ≟ₚ x
σα-delete {x} ((+ , x) ∷ .((- , x) ∷ _)) (vp , vs) (there (here refl)) w | yes refl = ⊥-elim (vp (here refl))
σα-delete {x} ((+ , x) ∷ .(_ ∷ _)) (vp , vs) (there (there -x∈N)) w | yes refl = ⊥-elim (vp (there (membershipHelper x - _ -x∈N)))
... | no y≢x = contr where
  contr : x ∉ y ∷ updateWorld N w
  contr (here x≡y) = y≢x (Relation.Binary.PropositionalEquality.sym x≡y)
  contr (there x∈) = σα-delete N vs -x∈N w x∈ -- σα-delete -x∈N w x∈
σα-delete {x} ((- , y) ∷ N) (vp , vs) (there -x∈N) w =  remove-resp-∉ (σα-delete N vs -x∈N w) {y}


-- Proposition 1: The canonical handler is well-formed
wf-canonical-σ : ∀ Γ → WfHandler Γ (canonical-σ Γ)
wf-canonical-σ Γ {α} {M} M'<:M {w} w∈⟨M⟩ vs =
  (λ {a +a∈M → lt a (⊔-union +a∈M)})
  ,
  λ a -a∈M a∈w  →  rt a (⊔-union -a∈M) a∈w
  where lt : ∀ x → (+x∈M⊎N : (+ , x) ∈ M × (- , x) ∉ effects (Γ α) ⊎ (+ , x) ∈ effects (Γ α)) → x ∈ canonical-σ Γ α w
        lt x (inj₁ (+x∈M , -x∉N)) = σα-keep (proj₁ w∈⟨M⟩ x +x∈M) -x∉N
        lt x (inj₂ +x∈N) = σα-insert _ vs +x∈N w
        rt : ∀ x → (+x∈M⊎N : (- , x) ∈ M × (+ , x) ∉ effects (Γ α) ⊎ (- , x) ∈ effects (Γ α)) → x ∉ canonical-σ Γ α w
        rt x (inj₁ (-x∈M , +x∉N)) = σα-keep-∉ (proj₂ w∈⟨M⟩ x -x∈M) +x∉N
        rt x (inj₂ -x∈N) = σα-delete _ vs -x∈N w


-- Proof that using updateWorld with the empty list is a sound way to produce the initial world 
stateToWorldConversionSound : (N : State) -> (ValidS N) -> (updateWorld N []) ∈⟨ N ⟩
stateToWorldConversionSound [] vs = (λ { a ()}) , λ { a () x₁}
stateToWorldConversionSound ((+ , a) ∷ N) (vp , vs) = (λ { a₁ (here refl) → here refl ; a₁ (there x) → there (σα-insert N vs x [])})
                                          , λ a₁ x x₁ → σα-delete ((+ , a) ∷ N) (vp , vs) x [] x₁
stateToWorldConversionSound ((- , a) ∷ N) vs = (λ { a₁ (there x) → σα-insert ((- , a) ∷ N) vs (there x) []})
                                              , λ {a₁ x x₁ → σα-delete ((- , a) ∷ N) vs x [] x₁} 

_↓₊ : Form → State
P ↓₊ = P ↓[ + ] []

open import Plans.Proofs.Possible_World_Soundness domain

convertedStateEntailsPositiveForm : (P : Form) -> (ValidS (P ↓₊)) -> (updateWorld (P ↓₊) []) ⊨[ + ] P
convertedStateEntailsPositiveForm N vs = ↓-sound (stateToWorldConversionSound (N ↓[ + ] []) vs)

----------------------------------

