{-# OPTIONS --without-K --type-in-type #-}
open import Level

module 83hott where
-- Part III Types as spaces

{-
Type : (i : Level) → Set (Agda.Primitive.lsuc i)
Type i = Set i
-}

Type = Set

data _≡_ {A : Type} (x : A) : A → Type where
  refl : x ≡ x


{-
UIP : {i : Level} {A : Type i} (x y : A) (p q : x ≡ y) → p ≡ q
UIP x .x refl q = {!!}

_●_ : {i : Level} {A : Type i} (x y z : A) → (p : x ≡ y) → (q : y ≡ z) → x ≡ z
p ● q = {!!}

! : {i : Level} {A : Type i} (x y : A) → x ≡ y → y ≡ x
! p = {!!}
●-assoc : {i : Level} {A : Type i} {x y z w : A} → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) → ((p ● q) ● r) ≡ (p ● (q ● r))
●-assoc p q r = ?

●-inv-l : {i : Level} {A : Type i} {x y : A} → ((! p) ● p) ≡ refl
●-inv-l p = ?

●-inv-r : {i : Level} {A : Type i} {x y : A} →  (p ● (! p)) ≡ refl
●-inv-r p = ?
-}


-- Part IV n-types

data ⊥ : Type where
data ⊤ : Type where
  tt : ⊤

data Bool : Type where
  true : Bool
  false : Bool

¬ : (A : Type) → Type
¬ A = A → ⊥


isProp : Type → Type
isProp A = (x y : A) → x ≡ y

⊥-isProp : isProp ⊥
⊥-isProp ()

⊤-isProp : isProp ⊤
⊤-isProp tt tt = refl

Bool-isnt-prop : ¬ (isProp Bool)
Bool-isnt-prop P with P true false
Bool-isnt-prop P | ()

{-
data Σ {i : Level} (A : Type i) (P : A → Type i) : Type i where
 _,_ : (a : A) → P a → Σ A P

PROP : ∀{i} → Type i
PROP {i} = Σ (Type i) isProp
-}

data _×_ (A : Type) (B : Type) : Type where
 _,_ : A → B → A × B

isProp-∧ : {A B : Type} → isProp A → isProp B → isProp (A × B)
isProp-∧ PA PB (a , b) (a' , b') with PA a a' , PB b b'
... | refl , refl = refl

postulate funext : {A : Type} {B : A → Type} → {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g

⊥-elim : {A : Type} → ⊥ → A
⊥-elim ()

isProp-¬ : {A : Type} → isProp (¬ A)
isProp-¬ {A} ¬x ¬y = funext (λ x → ⊥-elim ((¬x) x))

isSet : Type → Type
isSet A = (x y : A) → (p q : x ≡ y) → p ≡ q

