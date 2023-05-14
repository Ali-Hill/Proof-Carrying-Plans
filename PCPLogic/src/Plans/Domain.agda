open import Relation.Binary

import Plans.Domain.Core as DomainCore

module Plans.Domain where

record Domain : Set₁ where
  field
    Predicate : Set
    Action : Set

  open DomainCore Action Predicate public

  field
    Γ : Context
    _≟ₚ_ : DecidableEquality Predicate
