```
module junk where
```

```
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_; _≡⟨_⟩_; _∎)
open import Relation.Binary.PropositionalEquality using (sym; cong; cong₂)
```

Predicates
----------


```
data Triangular : ℕ → ℕ → Set where
  tri-zero : Triangular 0 0
  tri-add : (k n : ℕ) → Triangular k n → Triangular (suc k) (n + suc k)
```

```
dub-div2 : (k n : ℕ) → ⌊ k + k + n /2⌋ ≡ ⌊ n /2⌋ + k
dub-div2 zero n = sym (+-identityʳ ⌊ n /2⌋)
dub-div2 (suc k) n =
  let IH = dub-div2 k n in
  begin
    ⌊ suc ((k + suc k) + n) /2⌋
  ≡⟨ cong ⌊_/2⌋ (cong suc (cong₂ _+_ (+-comm k (suc k)) refl)) ⟩
    ⌊ suc ((suc k + k) + n) /2⌋
  ≡⟨ cong ⌊_/2⌋ (cong suc (+-assoc (suc k) k n)) ⟩
    ⌊ suc (suc k + (k + n)) /2⌋
  ≡⟨ cong ⌊_/2⌋ (cong suc (+-suc zero (k + (k + n)))) ⟩
    ⌊ suc (suc (k + (k + n))) /2⌋
  ≡⟨ cong ⌊_/2⌋ (cong suc (cong suc (sym (+-assoc k k n)))) ⟩
    ⌊ suc (suc ((k + k) + n)) /2⌋
  ≡⟨ refl ⟩
    suc ⌊ k + k + n /2⌋
  ≡⟨ cong suc IH ⟩
    suc (⌊ n /2⌋ + k)
  ≡⟨ cong suc (+-comm ⌊ n /2⌋ k) ⟩
    suc (k + ⌊ n /2⌋)
  ≡⟨ +-suc zero (k + ⌊ n /2⌋) ⟩
    suc k + ⌊ n /2⌋
  ≡⟨ +-comm (suc k) ⌊ n /2⌋ ⟩
    ⌊ n /2⌋ + suc k
  ∎ 
```

```
tri-sum : (k n : ℕ) → Triangular k n → n ≡ ⌊ (k * k + k) /2⌋
tri-sum zero 0 tri-zero = refl
tri-sum (suc k) .(n + suc k) (tri-add .k n t) =
  let IH = tri-sum k n t in
  begin
    n + suc k
  ≡⟨ cong₂ _+_ IH refl ⟩
    ⌊ k * k + k /2⌋ + suc k
  ≡⟨ sym (dub-div2 (suc k) (k * k + k)) ⟩
    ⌊ ((suc k) + (suc k)) + (k * k + k) /2⌋
  ≡⟨ cong ⌊_/2⌋ (+-assoc (suc k) (suc k) (k * k + k)) ⟩
    ⌊ (suc k) + ((suc k) + (k * k + k)) /2⌋
  ≡⟨ cong ⌊_/2⌋ (cong₂ _+_ refl (+-comm (suc k) (k * k + k))) ⟩
    ⌊ (suc k) + ((k * k + k) + (suc k)) /2⌋
  ≡⟨ cong ⌊_/2⌋ (sym (+-assoc (suc k) (k * k + k) (suc k))) ⟩
    ⌊ ((suc k) + (k * k + k)) + suc k /2⌋
  ≡⟨ cong ⌊_/2⌋ (cong₂ _+_ {u = suc k} (cong₂ _+_ {x = suc k}{u = k * k + k} refl (+-comm (k * k) k)) refl) ⟩
    ⌊ ((suc k) + (suc k * k)) + suc k /2⌋
  ≡⟨ cong ⌊_/2⌋ (cong₂ _+_ {u = suc k} (cong₂ _+_ {x = suc k} refl (*-comm (suc k) k)) refl) ⟩
    ⌊ ((suc k) + (k * suc k)) + suc k /2⌋
  ≡⟨ sym (cong ⌊_/2⌋ (+-suc zero (k + k * suc k + suc k))) ⟩
    ⌊ suc (k + k * suc k + suc k) /2⌋
  ∎ 
```
