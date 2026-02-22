```agda
{-# OPTIONS --without-K --safe #-}

module lecture1 where
import introduction

Type = Set
Type₁ = Set₁

data Bool : Type where
 true false : Bool

-- Type "→" as "\to" or "\->"
not : Bool → Bool
not true  = false
not false = true

idBool : Bool → Bool
idBool x = x

idBool' : Bool → Bool
idBool' = λ (x : Bool) → x

-- The following is a Π type
id' : (X : Type) → X → X
id' X x = x

-- Implicit
id : {X : Type} → X → X
id x = x

idBool'' : Bool → Bool
idBool'' = id' _

-- "propositions as types" "mathematical statements as types"
example : {P Q : Type} → P → (Q → P)
example {P} {Q} p = f
 where
  f : Q → P
  f _ = p

example' : {P Q : Type} → P → (Q → P)
example' p = λ q → p

open import binary-products

-- "×" is "and" in propositions as types
ex : {P Q : Type} → P × Q → Q × P
ex (p , q) = (q , p)

-- \bN
data ℕ : Type where
 zero : ℕ
 suc  : ℕ → ℕ

three : ℕ
three = suc (suc (suc zero))

-- {-# BUILTIN NATURAL ℕ #-}
-- for technical reasons we can not have this binding here. however
-- there is already a type ℕ in the introduction module which /does/
-- support numeral notation. we are careful not to use the ℕ type
-- defined in this module again.

three' : introduction.ℕ
three' = 3 -- synonym for the above

D : Bool → Type
D true  = introduction.ℕ
D false = Bool

-- "mix-fix" operator (3rd sense of "_" in Agda)
--                           b      x   y
if_then_else_ : {X : Type} → Bool → X → X → X
if true  then x else y = x
if false then x else y = y

if[_]_then_else_ : (X : Bool → Type)
                 → (b : Bool)
                 → X true
                 → X false
                 → X b
if[ X ] true then  x else y = x
if[ X ] false then x else y = y

-- Π (b : Bool), D b
unfamiliar : (b : Bool) → D b
unfamiliar b = if[ D ] b then 3 else false

data List (A : Type) : Type where
 []   : List A  -- empty list
 _::_ : A → List A → List A -- if xs is a list then x :: xs is list

infixr 10 _::_

ff : Type → Type
ff = List

sample-list₀ : List introduction.ℕ
sample-list₀ = 0 :: 1 :: 2 :: []

length : {X : Type} → List X → ℕ
length []        = zero
length (x :: xs) = suc (length xs)

-- Principle of induction on ℕ
ℕ-elim : {A : ℕ → Type}
       → A zero -- base case
       → ((k : ℕ) → A k → A (suc k)) -- induction step
       → (n : ℕ) → A n
ℕ-elim {A} a₀ f = h
 where
  h : (n : ℕ) → A n
  h zero    = a₀
  h (suc n) = f n IH
   where
    IH : A n
    IH = h n

ℕ-elim' : {A : ℕ → Type}
       → A zero -- base case
       → ((k : ℕ) → A k → A (suc k)) -- induction step
       → (n : ℕ) → A n
ℕ-elim' {A} a₀ f zero    = a₀
ℕ-elim' {A} a₀ f (suc n) = f n (ℕ-elim' a₀ f n)

List-elim : {X : Type} (A : List X → Type)
          → A [] -- base
          → ((x : X) (xs : List X) → A xs → A (x :: xs)) -- step
          → (xs : List X) → A xs
List-elim {X} A a f = h
 where
  h : (xs : List X) → A xs
  h []        = a -- base
  h (x :: xs) = f x xs (h xs) -- step

-- \b0
data 𝟘 : Type where

-- \b1
data 𝟙 : Type where
 ⋆ : 𝟙  -- \star

_≣_ : ℕ → ℕ → Type
zero  ≣ zero  = 𝟙
zero  ≣ suc y = 𝟘
suc x ≣ zero  = 𝟘
suc x ≣ suc y = x ≣ y

infix 0 _≣_

ℕ-refl : (x : ℕ) → x ≣ x
ℕ-refl zero    = ⋆
ℕ-refl (suc x) = ℕ-refl x

_+_ : ℕ → ℕ → ℕ
zero  + y = y
suc x + y = suc (x + y)

infixr 20 _+_

_++_ : {A : Type} → List A → List A → List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

lh : {X : Type} (xs ys : List X)
   → length (xs ++ ys) ≣ length xs + length ys
lh [] ys        = ℕ-refl (length ys)
lh (x :: xs) ys = IH
 where
  IH : length (xs ++ ys) ≣ (length xs + length ys)
  IH = lh xs ys

data Vector (A : Type) : ℕ → Type where
 [] : Vector A (zero)
 _::_ : {n : ℕ} → A → Vector A n → Vector A (suc n)

head : {A : Type} {n : ℕ} → Vector A (suc n) → A
head (x :: xs) = x

tail : {A : Type} {n : ℕ} → Vector A (suc n) → Vector A n
tail (x :: xs) = xs
```
