module IsomorphismLecture where

{-

 Jan. 16, 2020

 -}

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open Relation.Binary.PropositionalEquality.≡-Reasoning
  using (begin_; _≡⟨_⟩_; _∎)
open import Relation.Nullary using (¬_)
open import Data.Sum
import Data.Empty.Irrelevant
open import Data.Empty using (⊥-elim)


infix 0 _≃_

record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y

×-comm : ∀{A B : Set} → A × B ≃ B × A
×-comm =
  record {
    to = λ { ⟨ a , b ⟩ → ⟨ b , a ⟩ } ;
    from = λ { ⟨ b , a ⟩ → ⟨ a , b ⟩ }  ;
    from∘to =  λ ab → refl ;
    to∘from = λ ba → refl }


open import Data.Bool

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

_ : ∀{A B : Set} → ((A → B) × (A → B) ≃ ((A × Bool) → B))
_ = record {
      to = λ { fg ⟨ a , true ⟩ → proj₁ fg a ;
               fg ⟨ a , false ⟩ → proj₂ fg a };
      from = λ h → ⟨ (λ a → h ⟨ a , true ⟩) , (λ a → h ⟨ a , false ⟩) ⟩ ;
      from∘to = λ fg → refl ;
      to∘from = λ h → extensionality λ { ⟨ a , true ⟩ → refl ; ⟨ a , false ⟩ → refl } }

data IsEven : ℕ → Set where
  is-even : ∀ n m → n ≡ m + m → IsEven n

data IsOdd : ℕ → Set where
  is-odd : ∀ n m → n ≡ suc (m + m) → IsOdd n

data Evens : Set where
  even : (n : ℕ) → .(IsEven n) → Evens

Evens≡ : ∀{x y : ℕ} .{p : IsEven x} .{q : IsEven y}
       → x ≡ y
       → (even x p) ≡ (even y q)
Evens≡ {x} {y} {p} {q} refl = refl

to-evens : ℕ → Evens
to-evens n = even (n + n) (is-even (n + n) n refl)

from-evens : Evens → ℕ
from-evens (even n even-n) = ⌊ n /2⌋

⌊n+n/2⌋≡n : (n : ℕ) → ⌊ n + n /2⌋ ≡ n
⌊n+n/2⌋≡n zero = refl
⌊n+n/2⌋≡n (suc n) rewrite +-comm n (suc n) =
  let IH = ⌊n+n/2⌋≡n n in
  cong suc IH

from∘to-evens : ∀ (n : ℕ) → from-evens (to-evens n) ≡ n
from∘to-evens n = ⌊n+n/2⌋≡n n

⌊n/2⌋+⌊n/2⌋≡n : ∀ n → (IsEven n) → ⌊ n /2⌋ + ⌊ n /2⌋ ≡ n
⌊n/2⌋+⌊n/2⌋≡n n (is-even .n m refl) rewrite ⌊n+n/2⌋≡n m = refl

even⊎odd : ∀ (n : ℕ) → IsEven n ⊎ IsOdd n
even⊎odd zero = inj₁ (is-even 0 0 refl)
even⊎odd (suc n)
    with even⊎odd n
... | inj₁ (is-even n m refl) =
      inj₂ (is-odd (suc (m + m)) m refl)
... | inj₂ (is-odd n m refl) =
      inj₁ (is-even (suc (suc (m + m))) (suc m) (cong suc (sym (+-suc m m))))

2*n≢1+2*m : ∀ (n m : ℕ) → n + n ≢ suc (m + m)
2*n≢1+2*m (suc n) zero eq rewrite +-comm n (suc n)
    with eq
... | ()
2*n≢1+2*m (suc n) (suc m) eq rewrite +-comm n (suc n) | +-comm m (suc m) =
    let IH = 2*n≢1+2*m n m in
    IH (suc-injective (suc-injective eq))

IsOdd→¬IsEven : ∀ n → IsOdd n → ¬ IsEven n
IsOdd→¬IsEven n (is-odd .n m refl) (is-even .n m₁ eq) =
  2*n≢1+2*m m₁ m (sym eq)

IsEven-irrelevant→IsEven : ∀ n → .(IsEven n) → IsEven n
IsEven-irrelevant→IsEven n even-n
    with even⊎odd n
... | inj₁ even-n' = even-n'
... | inj₂ odd-n =
   let not-even = IsOdd→¬IsEven n odd-n in
   Data.Empty.Irrelevant.⊥-elim (not-even even-n)

to∘from-evens : ∀ (e : Evens) → to-evens (from-evens e) ≡ e
to∘from-evens (even n even-n) = Evens≡ (⌊n/2⌋+⌊n/2⌋≡n n (IsEven-irrelevant→IsEven n even-n))

ℕ≃Evens : ℕ ≃ Evens
ℕ≃Evens =
  record {
    to = to-evens ;
    from = from-evens ;
    from∘to = from∘to-evens ;
    to∘from = to∘from-evens }
