module InductionLecture where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_; _≡⟨_⟩_; _∎)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver

open import NaturalsLecture

{-

  January 13, 2020, Part 2
 
-}

dub : ℕ → ℕ
dub zero = 0
dub (suc n) = suc (suc (dub n))

dub-correct : (n : ℕ) → dub n ≡ n + n
dub-correct zero = refl
dub-correct (suc n) =
  let IH = dub-correct n in
  begin
  suc (suc (dub n))        ≡⟨ cong suc (cong suc IH) ⟩
  suc (suc (n + n))        ≡⟨ cong suc (sym (+-suc n n)) ⟩
  suc (n + suc n)
  ∎

gauss-formula : (n : ℕ) → 2 * gauss n ≡ n * suc n
gauss-formula zero = refl
gauss-formula (suc n) =
  let IH : 2 * gauss n ≡ n * suc n
      IH = gauss-formula n in
  begin
    2 * gauss (suc n)          ≡⟨ refl ⟩
    2 * (suc n + gauss n)      ≡⟨ *-distribˡ-+ 2 (suc n) (gauss n) ⟩
    2 * (suc n) + 2 * gauss n  ≡⟨ cong (λ □ → 2 * (suc n) + □) IH ⟩
    2 * (suc n) + (n * suc n)  ≡⟨ EQ n ⟩
    (suc n) * suc (suc n)
  ∎
  where
  EQ = solve 1 (λ n → (con 2 :* (con 1 :+ n)) :+ (n :* (con 1 :+ n))
         := (con 1 :+ n) :* (con 1 :+ (con 1 :+ n))) refl
