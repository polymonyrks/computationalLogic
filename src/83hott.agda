{-# OPTIONS --without-K #-}
open import Level

module 83hott where
-- Part III Types as spaces

Type : (i : Level) → Set (Agda.Primitive.lsuc i)
Type i = Set i

data _≡_ {i : Level} {A : Type i} (x : A) : A → Type i where
  refl : x ≡ x

