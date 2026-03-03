```agda
{-# OPTIONS --without-K --safe #-}

module HoTTestL2 where

-- lecture 2
-- Basic MLTT types and elimination principles

open import lecture1 hiding (𝟘 ; 𝟙 ; D ; ℕ ; _+_)
open import introduction using (ℕ ; zero ; suc ; _+_)

data 𝟘 : Type where

𝟘-elim : { A : 𝟘 → Type} (x : 𝟘) → A x
𝟘-elim ()

-- 𝟘 interpreted as "false"
-- Record definitions satisfy a certain "η" rule

¬_ : Type → Type
¬ A = A → 𝟘

infix 1000 ¬_

𝟘-nondep-elim : {B : Type} → 𝟘 → B
𝟘-nondep-elim {B} = 𝟘-elim {λ _ → B}

is-empty : Type → Type
is-empty A = A → 𝟘

𝟘-is-empty'' : is-empty 𝟘
𝟘-is-empty'' = λ ()

record 𝟙 : Type where
  constructor
    ⋆

open 𝟙 public

𝟙-is-non-empty' : ¬ is-empty 𝟙
𝟙-is-non-empty' = λ (f : 𝟙 → 𝟘) → f ⋆

𝟙-is-non-empty : ¬ is-empty 𝟙
𝟙-is-non-empty f = f ⋆

𝟙-elim : {A : 𝟙 → Type}
       → A ⋆
       → (x : 𝟙) → A x
𝟙-elim a x = a

𝟙-nondep-elim : {A : Type}
              → A
              → 𝟙 → A
𝟙-nondep-elim {A} = 𝟙-elim {λ _ → A}

data 𝟚 : Type where
  𝟎 𝟏 : 𝟚

𝟚-elim : {A : 𝟚 → Type}
       → A 𝟎
       → A 𝟏
       → (x : 𝟚) → A x
𝟚-elim a₀ a₁ 𝟎 = a₀
𝟚-elim a₀ a₁ 𝟏 = a₁

𝟚-nondep-elim : {A : Type}
              → A
              → A
              → 𝟚 → A
𝟚-nondep-elim {A} = 𝟚-elim {λ _ → A}

Pi : (A : Type) (B : A → Type) → Type
Pi A B = (x : A) → B x

syntax Pi A (λ x → b) = Π x ꞉ A , b -- the ꞉ is typed "\:4" in emacs

module _ where
  private
   _∘_ : {A B C : Type} → (B → C) → (A → B) → (A → C)
   (g ∘ f) x = g (f x)

_∘_ : {A B : Type} {C : B → Type}
    → ((y : B) → C y)
    → (f : A → B)
    → (x : A) → C (f x)
(g ∘ f) x = g (f x)
  
module _ where
  private

    data Σ {A : Type} (B : A → Type) : Type where
     _,_ : (x : A) (y : B x) → Σ {A} B

    pr₁ : {A : Type} {B : A → Type} → Σ B → A
    pr₁ (x , y) = x

    pr₂ : {A : Type} {B : A → Type} → (z : Σ B) → B (pr₁ z)
    pr₂ (x , y) = y


-- Our preferred definition:

record Σ {A : Type} (B : A → Type) : Type where
  constructor
    _,_
  field
    pr₁ : A
    pr₂ : B pr₁

open Σ public
infixr 0 _,_

pr₁-again : {A : Type} {B : A → Type} → Σ B → A
pr₁-again = pr₁

pr₂-again : {A : Type} {B : A → Type} ((x , y) : Σ B) → B x
pr₂-again = pr₂


-- This satisfies the η-rule z = (pr₁ z, pr₂ z), which the definition using `data` doesn't.


Sigma : (A : Type) (B : A → Type) → Type
Sigma A B = Σ {A} B

syntax Sigma A (λ x → b) = Σ x ꞉ A , b -- Syntax is read right to left, i.e. left is def

infix -1 Sigma

-- Recall that we defined D as follows in the first lecture:

D : Bool → Type
D true = ℕ
D false = Bool

-- Example

Σ-example₁ Σ-example₂ : Σ b ꞉ Bool , D b
Σ-example₁ = (true , 17)
Σ-example₂ = (false , true)

Σ-elim : {A : Type} {B : A → Type} {C : (Σ x ꞉ A , B x) → Type}
       → ((x : A) (y : B x) → C (x , y))
       → (z : Σ x ꞉ A , B x) → C z
Σ-elim f (x , y) = f x y

Σ-uncurry : {A : Type} {B : A → Type} {C : (Σ x ꞉ A , B x) → Type}
       → ((z : Σ x ꞉ A , B x) → C z)
       → (x : A) (y : B x) → C (x , y)
Σ-uncurry g x y = g (x , y)
       
_×_ : Type → Type → Type
A × B = Σ x ꞉ A , B

-- (x : X) → A x
-- (x : X) × A x

infixr 2 _×_

-- We will have that A₀ × A₁ ≅ Π (n : 𝟚), A n ≅ ((n : 𝟚) → A n)
-- where A 𝟎 = A₀
--       A 𝟏 = A₁
--       A ꞉ 𝟚 → Type
-- f ↦ (f 𝟎, f 𝟏)
--
-- Binary products are special cases of products
```

Various uses of Σ:
  *
  *
  *
  
```agda

-- Binary sums _+_ +

data _∔_ (A B : Type) : Type where
  inl : A → A ∔ B
  inr : B → A ∔ B

-- Mathematically A ∔ B is (disjoint) union


infixr 20 _∔_

∔-elim : {A B : Type} (C : A ∔ B → Type)
       → ((x : A) → C (inl x)) -- f
       → ((y : B) → C (inr y)) -- g
       → (z : A ∔ B) → C z
∔-elim C f g (inl x) = f x
∔-elim C f g (inr y) = g y
```

```agda
data _≡_ {A : Type} : A → A → Type where
  refl : (x : A) → x ≡ x

-- refl x : proof that x is equal to itself

infix 0 _≡_

-- The following is also called "J"

≡-elim : {X : Type} (A : (x y : X) → x ≡ y → Type)
       → ((x : X) → A x x (refl x))
       → (x y : X) (p : x ≡ y) → A x y p
≡-elim A f x x (refl x) = f x
```

To conclude that a property A x y p of identifications p of
elements x and y holds for all x, y and p, it is enough to show
that A x x (refl x) holds for all x.
