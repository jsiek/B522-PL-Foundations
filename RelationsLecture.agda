module RelationsLecture where

  {-

  January 15, 2020

  -}


open import Data.Nat
open import Data.Nat.Properties

data Even : ℕ → Set where
  even-0 : Even 0
  even-+2 : (n : ℕ) → Even n → Even (2 + n)  

{-
_ : ¬ Even 1
_ = ?
-}

_ : Even 2
_ = even-+2 zero even-0

_ : Even 4
_ = even-+2 2 (even-+2 zero even-0)

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)

sn+sn≡ss[n+n] : ∀ n → (suc n) + (suc n) ≡ suc (suc (n + n))
sn+sn≡ss[n+n] n rewrite +-comm n (suc n) = refl

even-dub : (n : ℕ) → Even (n + n)
even-dub zero = even-0
even-dub (suc n) rewrite sn+sn≡ss[n+n] n =
  let IH = even-dub n in
  even-+2 (n + n) IH

inv-Even : (n m : ℕ) → Even m → m ≢ 0 → suc (suc n) ≡ m → Even n
inv-Even n .(suc (suc n')) (even-+2 n' even-m) m≢0 refl = even-m

data _div_ : ℕ → ℕ → Set where
  div-refl : (m : ℕ) → m ≢ 0 → m div m
  div-step : (n m : ℕ) → m div n → m div (m + n)

3-div-3 : 3 div 3
3-div-3 = div-refl 3 (λ ())

3-div-6 : 3 div 6
3-div-6 = div-step 3 3 (div-refl 3 (λ ()))

mdivn→m≢0 : (m n : ℕ) → m div n → m ≢ 0
mdivn→m≢0 m .m (div-refl .m m≢0) m≡0 = m≢0 m≡0
mdivn→m≢0 m .(m + n) (div-step n .m mdivn) m≡0 = mdivn→m≢0 m n mdivn m≡0

mdivn→n≢0 : (m n : ℕ) → m div n → n ≢ 0
mdivn→n≢0 m .m (div-refl .m x) n≡0 = x n≡0
mdivn→n≢0 m .(m + n) (div-step n .m mdivn) m+n≡0 =
  let IH = mdivn→n≢0 m n mdivn in
  IH (m+n≡0⇒n≡0 m m+n≡0)

open import Data.Product using (Σ-syntax) renaming (_,_ to ⟨_,_⟩)

mdivn→k*m≡n : (m n : ℕ) → m div n → Σ[ k ∈ ℕ ] k * m ≡ n
mdivn→k*m≡n m .m (div-refl .m x) = ⟨ 1 , +-identityʳ m ⟩
mdivn→k*m≡n m .(m + n) (div-step n .m mdivn) 
    with mdivn→k*m≡n m n mdivn
... | ⟨ q , q*m≡n ⟩
    rewrite sym q*m≡n = 
    ⟨ suc q , refl ⟩

open import Data.Empty using (⊥-elim)

m-div-k*m : (k m : ℕ) → m ≢ 0 → k ≢ 0 → m div (k * m)
m-div-k*m zero m m≢0 k≢0 = ⊥-elim (k≢0 refl)
m-div-k*m (suc zero) m m≢0 k≢0 rewrite +-identityʳ m = div-refl m m≢0
m-div-k*m (suc (suc k)) m m≢0 k≢0 =
  let IH = (m-div-k*m (suc k) m m≢0 (λ ())) in
  div-step (m + k * m) m IH

div-trans : (m n p : ℕ) → m div n → n div p → m div p
div-trans m n p mn np
    with mdivn→k*m≡n m n mn | mdivn→k*m≡n n p np
... | ⟨ k₁ , k₁*m≡n ⟩ | ⟨ k₂ , k₂*k₁*m≡p ⟩
      rewrite sym k₁*m≡n | sym k₂*k₁*m≡p | sym (*-assoc k₂ k₁ m) =
   m-div-k*m (k₂ * k₁) m (mdivn→m≢0 m (k₁ * m) mn) {!!}
