module EqualityLecture where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

0≡0+0 : 0 ≡ 0 + 0
0≡0+0 = refl

_ : 0 + 0 ≡ 0
_ = sym 0≡0+0

_ : 0 + 0 ≡ 0
_ = refl

0+0≡0+0+0 : 0 + 0 ≡ 0 + (0 + 0)
0+0≡0+0+0 = cong (λ □ → 0 + □) 0≡0+0

0≡0+0+0 : 0 ≡ 0 + 0 + 0
0≡0+0+0 = trans 0≡0+0 0+0≡0+0+0

data Even : ℕ → Set where
  even-0 : Even 0
  even-+2 : (n : ℕ) → Even n → Even (2 + n)

sn+sn≡ss[n+n] : ∀ n → (suc n) + (suc n) ≡ suc (suc (n + n))
sn+sn≡ss[n+n] n rewrite +-comm n (suc n) = refl

even-dub : (n : ℕ) → Even (n + n)
even-dub zero = even-0
even-dub (suc n) rewrite sn+sn≡ss[n+n] n =
    let IH : Even (n + n)
        IH = even-dub n in
    even-+2 (n + n) IH 

even-dub' : (n m : ℕ) → m + m ≡ n → Even n
even-dub' n m eq =
  let even-m = even-dub m in
  subst (λ □ → Even □) eq even-m

open Relation.Binary.PropositionalEquality.≡-Reasoning
  using (begin_; _≡⟨_⟩_; _≡⟨⟩_; _∎)

_ : 0 ≡ 0 + 0 + 0
_ =
  begin
    0             ≡⟨ 0≡0+0 ⟩
    0 + 0         ≡⟨ 0+0≡0+0+0 ⟩
    0 + 0 + 0
  ∎

even-dub'' : (n m : ℕ) → m + m ≡ n → Even n
even-dub'' n m eq rewrite sym eq = even-dub m

