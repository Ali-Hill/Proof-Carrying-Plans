module Plans.Mangle where

open import Prelude.Decidable renaming (Dec to PDec)
open import Relation.Nullary using (Dec;yes;no)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Prelude.Empty
pdec-to-dec : {A : Set} → PDec A → Dec A
pdec-to-dec (PDec.yes x) = Relation.Nullary.yes x
pdec-to-dec (PDec.no x) = Relation.Nullary.no (λ x₁ → ⊥-elim (x x₁))

open import Prelude.Equality using (Eq; _==_) 

mangle : {A : Set}  ⦃ _ : Eq A ⦄  → Decidable (_≡_ {A = A} )
mangle {A} x y = pdec-to-dec (x == y)

open import Relation.Nullary renaming (yes to yes'; no to no')
open import Data.Empty renaming (⊥-elim to ⊥-elim')

dec-to-pdec : {A : Set} → Dec A → PDec A
dec-to-pdec (yes' p) = PDec.yes p
dec-to-pdec (no' ¬p) = PDec.no (λ x → ⊥-elim' (¬p x))

mangle' : {A : Set}  → Decidable (_≡_ {A = A} ) → Eq A
mangle' {A} x = record { _==_ = λ x₁ y → dec-to-pdec (x x₁ y) }
