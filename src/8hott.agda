open import Level
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)


module 8hott where

_≡₁_ : {A : Set} (x y : A) → Set₁
_≡₁_ {A} x y = (P : A → Set) → P x → P y

leibniz : {A : Set} {x y : A} → x ≡ y → x ≡₁ y
leibniz refl P p = p

leibniz' : {A : Set} {x y : A} → x ≡₁ y → x ≡ y
leibniz' {A} {x} {y} x≡₁y = x≡₁y (λ z → x ≡ z) refl

