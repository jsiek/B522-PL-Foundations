module NaturalsLecture where

{-

  January 13, 2020
 
-}

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

_ : Nat
_ = zero

one : Nat
one = suc zero

two : Nat
two = suc (suc zero)

add : Nat → Nat → Nat
add zero n = n
add (suc m) n = suc (add m n)

three = add two one

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

_ : zero ≡ zero
_ = refl

_ : three ≡ suc (suc (suc zero))
_ = refl

open import Data.Nat

gauss : ℕ → ℕ
gauss zero = 0
gauss (suc n) = suc n + gauss n

open import Data.Nat.Properties
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_; _≡⟨_⟩_; _∎)
open import Relation.Binary.PropositionalEquality using (sym; cong; cong₂)

_ : (x : ℕ) → (y : ℕ) → x + y + x ≡ 2 * x + y
_ = λ x y →
  begin
    (x + y) + x             ≡⟨ +-comm (x + y) x ⟩
    x + (x + y)             ≡⟨ sym (+-assoc x x y) ⟩
    (x + x) + y             ≡⟨ cong₂ _+_ {u = y} (cong₂ _+_ {x = x } refl (sym (+-identityʳ x))) refl ⟩
    (x + (x + zero)) + y    ≡⟨ refl ⟩
    2 * x + y
  ∎

{-
  Alternative version using cong and a λ instead of cong₂.
  Thanks Jacob and Kuang-Chen!
-}

_ : (x : ℕ) → (y : ℕ) → x + y + x ≡ 2 * x + y
_ = λ x y →
  begin
    (x + y) + x             ≡⟨ +-comm (x + y) x ⟩
    x + (x + y)             ≡⟨ sym (+-assoc x x y) ⟩
    (x + x) + y             ≡⟨ cong (λ □ → (x + □) + y) (sym (+-identityʳ x)) ⟩
    (x + (x + zero)) + y    ≡⟨ refl ⟩
    2 * x + y
  ∎

open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver

_ : ∀ (x y : ℕ) → x + y + x ≡ 2 * x + y
_ = solve 2 (λ x y → x :+ y :+ x := con 2 :* x :+ y) refl

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
    2 * (suc n) + 2 * gauss n  ≡⟨ cong₂ _+_ refl IH ⟩
    2 * (suc n) + (n * suc n)  ≡⟨ EQ n ⟩
    (suc n) * suc (suc n)
  ∎
  where
  EQ = solve 1 (λ n → (con 2 :* (con 1 :+ n)) :+ (n :* (con 1 :+ n))
         := (con 1 :+ n) :* (con 1 :+ (con 1 :+ n))) refl
