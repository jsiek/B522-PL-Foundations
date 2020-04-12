```
module ScottNumeralsPlus where
```

## Imports

```
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
open import Data.Nat using (ℕ; zero; suc; s≤s; z≤n; _+_; _<_; _≤_; _≟_)
open import Data.Nat.Properties
  using (≤∧≢⇒<; ≤-pred; <-trans; ≤-refl; +-comm; +-suc; suc-injective;
         ≤-trans; ≤-reflexive; ≤-step)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans)
open import Relation.Nullary using (Dec; yes; no)
open import plfa.part3.Denotational
   using (Value; _↦_; _⊔_; ⊥; _⊑_; _⊢_↓_; Env; `∅; _`,_;
         ↦-intro; ↦-elim; var; sub; ⊥-intro; ⊔-intro;
         ⊑-conj-R2; ⊑-fun; ⊑-refl; ⊑-conj-R1; ⊑-trans)
open import plfa.part2.Untyped
   using (`suc_; `zero; μ_; case; plus; ★; ∅; _,_; _⊢_; `_; _·_; ƛ_; #_)
```

## An `nth` function for lists of Values

Instead of requiring the index to be less than the length of the list,
we use `⊥` as a default value. This sidesteps an considerable amount
extra bookkeeping and proof obligation.

```
nth : (i : ℕ) (ls : List Value) → Value
nth zero (x ∷ ls) = x
nth (suc i) (x ∷ ls) = nth i ls
nth _ _ = ⊥
```

```
nth-++ : ∀{i}{xs ys : List Value} .{lt : i < length xs}
  → nth i (xs ++ ys) ≡ nth i xs
nth-++ {zero} {x ∷ xs} {ys} {lt} = refl
nth-++ {suc i} {x ∷ xs} {ys} {lt} = nth-++ {i}{xs}{ys}{≤-pred lt}

nth-++-> : ∀{i j}{xs ys : List Value}
    {eq : i ≡ length xs + j }{lt : j < length ys}
  → nth i (xs ++ ys) ≡ nth j ys
nth-++-> {i} {j} {[]} {ys} {refl} = refl
nth-++-> {suc i} {j} {x ∷ xs} {ys} {refl}{lt} =
   nth-++-> {i}{j}{xs}{ys}{refl}{lt}
```

## Scott Numerals

The `scott` function generates the nth Scott numeral.

```
scott : (n : ℕ) → ∀{Γ} → Γ ⊢ ★
scott 0 = ƛ ƛ (# 0)
scott (suc n) = ƛ ƛ (# 1) · (scott n)
```

The following function `Dˢ` gives the denotation of the nth Scott
numeral.  Like the Church numerals, the Scott numerals are more
general than natural numbers. The Scott numeral n represents taking n
steps along a path.  In the following definition, the list `ls` is the
path.

```
Dˢ : (n : ℕ) → (ls : List Value) → Value
Dˢ zero ls = ⊥ ↦ (nth 0 ls) ↦ (nth 0 ls)
Dˢ (suc n) ls =
  let D[n] = Dˢ n ls in
  (D[n] ↦ nth (suc n) ls) ↦ ⊥ ↦ nth (suc n) ls
```

* The Scott numeral for `0` is a function that ignores its first
  argument and returns its second argument, which is the first element
  of the path (which often corresponds to zero).

* The Scott numeral for `n + 1` is a function whose first argument is
  a funny kind of successor function, one that maps 
  the Scott numeral for `n` to the `n + 1` element of the path.
  The second argument is ignored. The result is   
  the `n + 1` element of the path.


A straightforward proof by induction on n verifies that `Dˢ n ls` is
the denotation of `scott n` for any choice of path `ls`.

```
denot-scott : ∀{n : ℕ}{ls : List Value}{Γ}{γ : Env Γ}
  → γ ⊢ scott n ↓ (Dˢ n ls)
denot-scott {zero} {ls} = ↦-intro (↦-intro var)
denot-scott {suc n} {ls} = ↦-intro (↦-intro (↦-elim var denot-scott))
```

The successor function for Scott numerals does indeed produce the
Scott numeral for `suc n` when given the Scott numeral for `n`.

```
denot-suc : ∀{Γ}{M : Γ ⊢ ★}{n}{ls : List Value}{γ : Env Γ}
  → γ ⊢ M ↓ Dˢ n ls
  → γ ⊢ `suc M ↓ Dˢ (suc n) ls
denot-suc {n = n} {ls} M↓D[n] =
    ↦-elim (↦-intro (↦-intro (↦-intro (↦-elim var var)))) M↓D[n]
```

## Addition of Scott Numerals via the Y Combinator

Recall that in the Untyped chapter, addition of Scott numerals is
defined as a recursive function using the Y combinator.
(Shown here with variable names instead of de Bruijn indices.)

    plus = Y · (ƛ r ⇒ ƛ m ⇒ ƛ n ⇒ case m n (ƛ m' ⇒ `suc (r · m' · n)))

We shall prove that the denotation of `plus` applied to the Scott numerals
for `m` and `n` is `Dˢ (m + n) rs` for any list `rs`.
