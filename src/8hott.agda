module 8hott where

-- Part I Equality

data _≡_ {A : Set} (x : A) : (y : A) → Set where
  refl : x ≡ x

J : {A : Set} (B : (x y : A) → x ≡ y → Set) (r : (x : A) → B x x refl)
    (t : A) (u : A) (p : t ≡ u) → B t u p
J B r t .t refl = r t

_≡₁_ : {A : Set} (x y : A) → Set₁
_≡₁_ {A} x y = (P : A → Set) → P x → P y

leibniz : {A : Set} {x y : A} → x ≡ y → x ≡₁ y
leibniz refl P p = p

leibniz' : {A : Set} {x y : A} → x ≡₁ y → x ≡ y
leibniz' {A} {x} {y} x≡₁y = x≡₁y (λ z → x ≡ z) refl

leibniz-refl : {A : Set} {x : A} → x ≡₁ x
leibniz-refl {x = x} P p = p

leibniz-sym : {A : Set} {x y : A} → x ≡₁ y → y ≡₁ x
leibniz-sym {A} {x} {y} F P' = F (λ z → (P' z → P' x)) (λ p → p)

leibniz-trans : {A : Set} {x y z : A} → x ≡₁ y → y ≡₁ z → x ≡₁ z
leibniz-trans {A} {x} {y} {z} F F₁ P'' = λ w → (F₁ P'') ((F P'') w)

-- Part II The axioms K and UIP

UIP : Set₁
UIP = {A : Set} {x y : A} (p q : x ≡ y) → p ≡ q

K : Set₁
K = {A : Set} {x : A} (P : (x ≡ x) → Set) → P refl → (p : x ≡ x) → P p

UIP-K : UIP → K
UIP-K uip P Pr p = subst P (uip refl p) Pr
  where
    -- uip refl p  : refl ≡ p
    -- (P : (x ≡ x) → Set)
    -- subst P (uip refl p) : P refl → P p
    subst : {A : Set} (P : A → Set) → {x y : A} → x ≡ y → P x → P y
    subst P refl p = p

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

loop-eq : {A : Set} {x y : A} (p q : x ≡ y) → trans (sym p) q ≡ refl → p ≡ q
loop-eq refl refl refl = refl

K-UIP : K → UIP
K-UIP K p q = {!!}

UIP-proof : {A : Set} {x y : A} (p q : x ≡ y) → p ≡ q
UIP-proof refl refl = refl

K-proof : {A : Set} {x : A} (P : (x ≡ x) → Set) → P refl → (p : x ≡ x) → P p
K-proof P Pr refl = Pr
