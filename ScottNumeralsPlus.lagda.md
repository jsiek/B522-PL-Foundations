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

We need the following corollary of `⊑-refl`. (Perhaps it should
defined in the Denotational chapter.)

```
⊑-reflexive : ∀{v w : Value} → v ≡ w → v ⊑ w
⊑-reflexive refl = ⊑-refl
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
steps along a path.  In the following definition, the function `ls` is
the path.

```
Dˢ : (n : ℕ) → (ls : ℕ → Value) → Value
Dˢ zero ls = ⊥ ↦ (ls 0) ↦ (ls 0)
Dˢ (suc n) ls =
  let D[n] = Dˢ n ls in
  (D[n] ↦ ls (suc n)) ↦ ⊥ ↦ ls (suc n)
```

* The Scott numeral for `0` is a function that ignores its first
  argument and returns its second argument, i.e., the first element
  of the path (which often corresponds to zero).

* The Scott numeral for `n + 1` is a function whose first argument is
  a funny kind of successor function, one that maps 
  the Scott numeral for `n` to the `n + 1` element of the path.
  The second argument is ignored. The result is   
  the `n + 1` element of the path.

A straightforward proof by induction on n verifies that `Dˢ n ls` is
the denotation of `scott n` for any choice of path `ls`.

```
denot-scott : ∀{n : ℕ}{ls : ℕ → Value}{Γ}{γ : Env Γ}
  → γ ⊢ scott n ↓ (Dˢ n ls)
denot-scott {zero} {ls} = ↦-intro (↦-intro var)
denot-scott {suc n} {ls} = ↦-intro (↦-intro (↦-elim var denot-scott))
```

The successor function for Scott numerals does indeed produce the
Scott numeral for `suc n` when given the Scott numeral for `n`.

```
denot-suc : ∀{Γ}{M : Γ ⊢ ★}{n}{ls : ℕ → Value}{γ : Env Γ}
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


    plus[m,n] : ∀{m n : ℕ}{rs : ℕ → Value}
       → `∅ ⊢ (plus · scott m) · (scott n) ↓ Dˢ (m + n) rs

In the `plus` function, the recursion is on `m`, i.e., the base case
is when `m` is zero, and the recursive call to `r` is given
`m' = m - 1`. So let's think about the denotation of `plus`
when `m` is `0`, then `1`, and then `2`.

When `m` is `0`, the denotation of `plus` looks like

    (⊥ ↦ Dˢ n rs ↦ Dˢ n rs)  ↦  Dˢ n rs  ↦  Dˢ n rs

Let's look closely at why this works, analyzing the denotation
of the term `ƛ m ⇒ ƛ n ⇒ case m n ...`.
So the parameter `m` and `n` have the following denotations.

    ⟦m₀⟧ = ⊥ ↦ Dˢ n rs ↦ Dˢ n rs
    ⟦n⟧ = Dˢ n rs

Recall that `case` on a Scott numeral is defined as follows.

    case L M N = L · (ƛ pˢ ⇒ N) · M

So for the `plus` function, the `case m n ...` is really

    m · (ƛ m' ⇒ `suc (r · m' · n)) · n

We analyze the application of `m` to its two arguments
`(ƛ m' ⇒ ...)` and `n`. Guided by the value for parameter `m`,
the first argument should have value `⊥`. Indeed, any
term can have value `⊥`.  The second argument, which `n`, should
have value `Dˢ n rs`, which indeed it does. The result of the application
is `Dˢ n rs`, which matches the expected result of `Dˢ (0 + n) rs`.

Next consider when `m` is `1`.

      ((⟦m₀⟧ ↦ Dˢ (1 + n) rs) ↦ ⊥ ↦ Dˢ (1 + n) rs)
    ↦ Dˢ n rs
    ↦ Dˢ (1 + n) rs

Again we analyze the term `ƛ m ⇒ ƛ n ⇒ case m n ...`.
So the parameters `m` and `n` have the following denotations.

    ⟦m₁⟧ = (⟦m₀⟧ ↦ Dˢ (1 + n) rs) ↦ ⊥ ↦ Dˢ (1 + n) rs
    ⟦n⟧ = Dˢ n rs

Next we analyze the application of `m` to its two arguments.
This time we must check that the argument `(ƛ m' ⇒ ...)`
produces the value

    ⟦m₀⟧ ↦ Dˢ (1 + n) rs

So parameter m' has the denotation `⟦m₀⟧`
and we need to show that `suc (r · m' · n)` produces `Dˢ (1 + n) rs`.
This can be obtained from the `denot-suc` lemma,
so long as `r · m' · n` produces `Dˢ n rs`.
This will be the case so long as `r` has the value

    ⟦m₀⟧  ↦  Dˢ n rs  ↦  Dˢ n rs

which was the denotation of plus for `m` at zero.
Thus, we have finished analyzing the first argument `(ƛ m' ⇒ ...)`.

The second argument in the application of `m`, which
is `n`, must have value `⊥`, which of course it does.
Thus, the result of applying `m` to `(ƛ m' ⇒ ...)`
and `n` is indeed `Dˢ (1 + n) rs` when `m` is 1.

We have seen the denotation of `plus` for `m` at zero and one, and now
we need to generalize to arbitrary numbers. So let us review
the denotations that we obtained for `m`:

    ⟦m₀⟧ = ⊥ ↦ Dˢ n rs ↦ Dˢ n rs
    ⟦m₁⟧ = (⟦m₀⟧ ↦ Dˢ (1 + n) rs) ↦ ⊥ ↦ Dˢ (1 + n) rs

Indeed, these are denotations of a Scott numeral, but over an
interesting choice of path:

    Dˢ n rs, Dˢ (1 + n) rs, Dˢ (2 + n) rs, ..., Dˢ (m + n) rs

We define the following function `ms` to produce this path.

```
ms : (n : ℕ) → (ℕ → Value) → (ℕ → Value)
ms n rs i = Dˢ (i + n) rs
```

The denotations for each `mᵢ` can now be expressed using `Dˢ` and `ms`:

    ⟦mᵢ⟧ = Dˢ i (ms n rs)

Now that we have a succinct way to write the denotation of the `m`
parameter, we can write down the ith denotation of `plus`.

```
plusᵐ : (m n : ℕ) → (ℕ → Value) → Value
plusᵐ m n rs = Dˢ m (ms n rs) ↦  Dˢ n rs  ↦  Dˢ (m + n) rs
```

Recall that the denotation of the `r` parameter needs to be the
denotation of `plus` for the previous `m`. Also, when m is zero we did
not use parameter `r`, so its denotation can be `⊥`.  So the following
function gives the denotation for `plus` at `m - 1`.

```
prev-plusᵐ : (m n : ℕ) → (ℕ → Value) → Value
prev-plusᵐ 0 n rs = ⊥
prev-plusᵐ (suc m) n rs = plusᵐ m n rs
```

We are now ready to formally verify the denotation
of the expression

    case m n (ƛ m' ⇒ `suc (r · m' · n))

which translates to de Bruijn notation as follows.

```
CASE : ∅ , ★ , ★ , ★ ⊢ ★
CASE = case (# 1) (# 0) (`suc (# 3 · # 0 · # 1))
```

The show that the denotation of `CASE` is `Dˢ (m + n) rs`
under the assumptions that the denotation
of parameter `r` is `prev-plusᵐ m n rs`,
parameter `m` is `Dˢ m (ms n rs)`, and parameter `n` is `Dˢ n rs`.
We proceed by induction on `m`.

```
CASE↓ : (m n : ℕ) (rs : ℕ → Value)
      → `∅ `, prev-plusᵐ m n rs `, Dˢ m (ms n rs) `, Dˢ n rs
        ⊢ CASE ↓ Dˢ (m + n) rs
CASE↓ zero n rs = ↦-elim (↦-elim var ⊥-intro) var
CASE↓ (suc m') n rs = ↦-elim (↦-elim var Sbranch) ⊥-intro
    where
    γ = `∅ `, prev-plusᵐ (suc m') n rs `, Dˢ (suc m') (ms n rs) `, Dˢ n rs
    Sbranch : γ ⊢ ƛ (`suc ((# 3) · (# 0) · (# 1)))
                ↓ Dˢ m' (ms n rs) ↦ Dˢ (suc m' + n) rs
    Sbranch = ↦-intro (denot-suc (↦-elim (↦-elim var var) var))
```

* When `m ≡ 0`, the denotation of m is `⊥ ↦ Dˢ n rs ↦  Dˢ n rs`.
  The non-zero branch has value `⊥` by `⊥-intro`, and `n`
  has value `Dˢ n rs`, so the result of the case is `Dˢ n rs`.

* When `m ≡ suc m'`, the denotation of m is

        ⟦m⟧ = Dˢ (suc m') (ms n rs)
           = (Dˢ m' (ms n rs) ↦ Dˢ (suc m' + n) rs) ↦ ⊥ ↦ Dˢ (suc m' + n) rs

  so we need to show that the non-zero branch has the value

        Dˢ m' (ms n rs) ↦ Dˢ (suc m' + n) rs

  Going under the `ƛ`, we need to show that
  `suc (r · m' · n)` produces `Dˢ (suc m' + n) rs`.
  Working backwards using the `denot-suc` lemma,
  it suffices to show that `r · m' · n` produces `Dˢ (m' + n) rs`.
  The denotation of `r` is `plusᵐ m' n rs`, so applying it
  to `m'` and `n` indeed produces `Dˢ (m' + n) rs`.

Moving outwards, we now analyze the expression

    ƛ r ⇒ ƛ m ⇒ ƛ n ⇒ case m n (ƛ m' ⇒ `suc (r · m' · n))

We shall show that is has the denotation

      (prev-plusᵐ 0 n rs ↦ plusᵐ 0 n rs)
    ⊔ (prev-plusᵐ 1 n rs ↦ plusᵐ 1 n rs)
    ⊔ (prev-plusᵐ 2 n rs ↦ plusᵐ 2 n rs)
      ...

which we construct with the following `Pᵐ` function (P for plus).

```
Pᵐ : (m n : ℕ) → (ℕ → Value) → Value
Pᵐ 0 n rs = ⊥ ↦ plusᵐ 0 n rs
Pᵐ (suc m') n rs = Pᵐ m' n rs ⊔ (plusᵐ m' n rs ↦ plusᵐ (suc m') n rs)
```

We proceed by induction, using the `CASE↓` lemma to analyze the `CASE`
expression and using the induction hypothesis to accumulate all of the
smaller denotations for plus.

```
P↓Pᵐ : ∀ m n → (rs : ℕ → Value) → `∅ ⊢ ƛ (ƛ (ƛ CASE)) ↓ Pᵐ m n rs
P↓Pᵐ zero n rs = ↦-intro (↦-intro (↦-intro (CASE↓ 0 n rs)))
P↓Pᵐ (suc m') n rs =
   ⊔-intro (P↓Pᵐ m' n rs)
           (↦-intro (↦-intro (↦-intro (CASE↓ (suc m') n rs))))
```

We shall need the following lemma, which extracts a single entry from `Pᵐ`.

```
prev↦plus⊑Pᵐ : (m k n : ℕ) → (rs : ℕ → Value)
    → prev-plusᵐ m n rs ↦ plusᵐ m n rs ⊑ Pᵐ (m + k) n rs
prev↦plus⊑Pᵐ zero zero n rs = ⊑-refl
prev↦plus⊑Pᵐ (suc m') zero n rs =
    ⊑-conj-R2 (⊑-fun (⊑-reflexive (cong (λ □ → plusᵐ □ n rs) (+-comm m' 0)))
                  (⊑-reflexive (cong (λ □ → plusᵐ (suc □) n rs) (+-comm 0 m'))))
prev↦plus⊑Pᵐ m' (suc k) n rs =
      let IH = prev↦plus⊑Pᵐ m' k n rs in
      ⊑-trans IH (⊑-trans (⊑-conj-R1 ⊑-refl)
                    (⊑-reflexive (cong (λ □ → Pᵐ □ n rs) (sym (+-suc m' k)))))
```

The final step of this proof is to analyze the denotation of the Y
combinator:

    M = ƛ x ⇒ f · (x · x)
    Y = ƛ f ⇒ M · M

In de Bruijn notation, we define Y as follows.

```
M : ∅ , ★ ⊢ ★
M = ƛ (# 1 · (# 0 · # 0))
Y : ∅ ⊢ ★
Y = ƛ M · M
```

The M is short for Matryoshka dolls (aka russian doll), which are
wooden dolls that nest smaller and smaller copies inside themselves.
In particular, for each m, the term M is a function from all the
previous denotations for M to `plusᵐ m n rs`.

    ⟦M₀⟧ = ⊥
    ⟦M₁⟧ = (⟦M₀⟧) ↦ plusᵐ 0 n rs
    ⟦M₂⟧ = (⟦M₀⟧ ⊔ ⟦M₁⟧) ↦ plusᵐ 1 n rs
    ⟦M₃⟧ = (⟦M₀⟧ ⊔ ⟦M₁⟧ ⊔ ⟦M₂⟧) ↦ plusᵐ 2 n rs
    ...

We define the function `Mᵐ` to compute the above denotations
for M, using the auxiliary function `Ms` to join all the
previous denotations of M.

```
Mᵐ : (m n : ℕ) → (ℕ → Value) → Value
Ms : (m n : ℕ) → (ℕ → Value) → Value
Mᵐ 0 n rs = ⊥
Mᵐ (suc m') n rs = (Ms m' n rs)  ↦  plusᵐ m' n rs
Ms zero n rs = ⊥
Ms (suc m') n rs = Ms m' n rs ⊔  Mᵐ (suc m') n rs
```

We prove by cases that the term M has
the denotation `Mᵐ i n rs` for any i from 0 to m + 1,
assuming the `f` parameter has the denotation `Pᵐ m n rs`.

```
M↓ : (i k m n : ℕ) (rs : ℕ → Value) {lt : suc m ≡ i + k}
   → `∅ `, Pᵐ m n rs ⊢ M ↓ Mᵐ i n rs
M↓ zero k m n rs = ⊥-intro
M↓ (suc i) k m n rs {lt} = ↦-intro (↦-elim (sub var H) x·x↓)
  where
  H : prev-plusᵐ i n rs ↦ plusᵐ i n rs ⊑ Pᵐ m n rs
  H = ⊑-trans (prev↦plus⊑Pᵐ i k n rs)
              (⊑-reflexive (cong (λ □ → Pᵐ □ n rs) (sym (suc-injective lt))))
  x·x↓ : ∀{i} → `∅ `, Pᵐ m n rs `, Ms i n rs ⊢ (# 0) · (# 0) ↓ prev-plusᵐ i n rs
  x·x↓ {zero} = ⊥-intro
  x·x↓ {suc i} = ↦-elim (sub var (⊑-conj-R2 ⊑-refl))
                     (sub var (⊑-conj-R1 ⊑-refl))
```

* The zero case is trivial: we apply `⊥-intro` to show that
  `M` has the value `⊥`.

* For the non-zero case, we need to show that M has the value

        Ms i n rs  ↦  plusᵐ i n rs

  Going under the `ƛ x`, we need to show that `f · (x · x)`
  has the value `plusᵐ i n rs`. The value of `x · x`
  is `prev-plusᵐ i n rs`, which we prove by induction on i.
  The case for 0 is trivial because `prev-plusᵐ 0 n rs ≡ ⊥`.
  In the case for `suc i`, we need to show that `x · x`
  produces `plusᵐ i n rs`. Now the first `x` has the value
  `Ms (suc i) n rs`, so by the `sub` rule and `⊑-conj-R2`,
  it also has the value `Mᵐ (suc m') n rs`, which is equivalent to

        Ms m' n rs  ↦  plusᵐ m' n rs

  The second `x`, of course, has the value
  `Ms (suc i) n rs`, so by the `sub` rule and `⊑-conj-R1`,
  is has the value
  
        Ms m' n rs

  So indeed, apply `x` to itself produces the value `plusᵐ m' n rs`.


With the above lemma in hand, it is also straightforward to prove that
the term M also produces the value `Ms i n rs` for each i from 0 to m + 1.
We prove this by a straightforward induction on i.

```
M↓Ms : (i k m n : ℕ) (rs : ℕ → Value) {lt : suc m ≡ i + k}
   → `∅ `, Pᵐ m n rs ⊢ M ↓ Ms i n rs
M↓Ms zero k m n rs {lt} = ⊥-intro
M↓Ms (suc i) k m n rs {lt} =
    ⊔-intro (M↓Ms i (suc k) m n rs {trans lt (sym (+-suc i k))})
            (M↓ (suc i) k m n rs {lt})
```

Now for the meaning of the Y combinator. It takes the table of the
plus functions (`Pᵐ m n rs`), the meaning of the Scott numeral for m
(`Dˢ m (ms n rs)`), and the meaning of n (`Dˢ n rs`), and returns the
meaning of the Scott numeral for `m + n` (`Dˢ (m + n) rs`).

```
Y↓ : ∀ m n (rs : ℕ → Value)
   → `∅ ⊢ Y ↓ Pᵐ m n rs ↦ Dˢ m (ms n rs) ↦ Dˢ n rs ↦ Dˢ (m + n) rs
Y↓ m n rs = ↦-intro (↦-elim M↓₁ M↓₂)
    where
    M↓₁ : `∅ `, Pᵐ m n rs ⊢ M
          ↓ Ms m n rs ↦ Dˢ m (ms n rs) ↦ Dˢ n rs ↦ Dˢ (m + n) rs
    M↓₁ = (M↓ (suc m) 0 m n rs {cong suc (+-comm 0 m)})
    
    M↓₂ : `∅ `, Pᵐ m n rs ⊢ M ↓ Ms m n rs
    M↓₂ = (M↓Ms m 1 m n rs {+-comm 1 m})
```

We go under the `ƛ f`, so `f` has the value `Pᵐ m n rs`.
We then show that M applied to itself has the value

    Dˢ m (ms n rs) ↦ Dˢ n rs ↦ Dˢ (m + n) rs

We apply the lemma `M↓` as `suc m` to show that the first M
produces

    Ms m n rs ↦ Dˢ m (ms n rs) ↦ Dˢ n rs ↦ Dˢ (m + n) rs

We apply the lemma `M↓Ms` to show that the second M produces

    Ms m n rs

So putting the above two together, the application `M · M`
produces the following, as desired.

    Dˢ m (ms n rs) ↦ Dˢ n rs ↦ Dˢ (m + n) rs


We arrive at the finish line: our theorem that the addition of two
Scott numerals produces the Scott numeral of the sum.

```  
plus[m,n] : ∀{m n : ℕ}{rs : ℕ → Value}
       → `∅ ⊢ (plus · scott m) · (scott n) ↓ Dˢ (m + n) rs
plus[m,n] {m}{n}{rs} =
  ↦-elim (↦-elim (↦-elim (Y↓ m n rs) (P↓Pᵐ m n rs)) (denot-scott{m}{ms n rs}))
         (denot-scott{n}{rs})
```

The `plus` function is the Y combinator applied to `ƛ r ⇒ ƛ m ⇒ ƛ n ...`,
So we obtain its meaning using `↦-elim` and the lemmas `Y↓` and `P↓Pᵐ`.
We then apply the result to the denotations of the Scott numerals
for `m` and `n`.

