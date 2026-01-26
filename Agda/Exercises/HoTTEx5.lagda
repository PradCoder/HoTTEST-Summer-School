Using Agda to do Formalize The HoTT Exercises in the course
Since I can't do it in Regular Lean anymore, and HoTTLean is not yet ready.

```agda
{-# OPTIONS --without-K --allow-unsolved-metas #-}

module 01-Exercises where

open import prelude hiding (not-is-involution)
```

Equivalences Exercise 1 
```agda

retract-is-injection : ∀ {f : A → B} → is-retract f → is-injection f
retract-is-injection {f} = ?
```