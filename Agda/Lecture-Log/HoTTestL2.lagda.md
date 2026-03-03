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


