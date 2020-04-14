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
defined in the [Denotational](https://plfa.github.io/Denotational/) chapter.)

```
⊑-reflexive : ∀{v w : Value} → v ≡ w → v ⊑ w
⊑-reflexive refl = ⊑-refl
```

## Scott Numerals

Recall that the Scott numerals are terms in the lambda calculus that
represent the natural numbers:

    zero = ƛ s ⇒ ƛ z ⇒ z
    one  = ƛ s ⇒ ƛ z ⇒ s · zero
    two  = ƛ s ⇒ ƛ z ⇒ s · one

The below `scott` function generates the nth Scott numeral.

```
scott : (n : ℕ) → ∀{Γ} → Γ ⊢ ★
scott 0 = ƛ ƛ (# 0)
scott (suc n) = ƛ ƛ (# 1) · (scott n)
```

The denotation `Dˢ` of the nth Scott numeral is defined below.  Like
the Church numerals, the Scott numerals are more general than natural
numbers. The Scott numeral for n represents taking n steps along a
path.  In the definition of `Dˢ`, the function `f` represents the
path.

```
Dˢ : (n : ℕ) → (f : ℕ → Value) → Value
Dˢ zero f = ⊥ ↦ (f 0) ↦ (f 0)
Dˢ (suc n) f =
  let D[n] = Dˢ n f in
  (D[n] ↦ f (suc n)) ↦ ⊥ ↦ f (suc n)
```

* The Scott numeral for `0` is a function that ignores its first
  argument and returns its second argument, i.e., the first element
  of the path.

* The Scott numeral for `n + 1` is a function whose first argument is
  a funny kind of successor function, one that maps the Scott numeral
  for `n` to the `n + 1` element of the path.  The second argument is
  ignored, so its value is `⊥`. The result is the `n + 1` element of
  the path.

A straightforward proof by induction on n verifies that `Dˢ n f` is
the denotation of `scott n` for any path `f`.

```
denot-scott : ∀{n : ℕ}{f : ℕ → Value}{Γ}{γ : Env Γ}
  → γ ⊢ scott n ↓ (Dˢ n f)
denot-scott {zero} {f} = ↦-intro (↦-intro var)
denot-scott {suc n} {f} = ↦-intro (↦-intro (↦-elim var denot-scott))
```

The successor function for Scott numerals does indeed produce the
Scott numeral for `suc n` when given the Scott numeral for `n`.

```
denot-suc : ∀{Γ}{M : Γ ⊢ ★}{n}{f : ℕ → Value}{γ : Env Γ}
  → γ ⊢ M ↓ Dˢ n f
  → γ ⊢ `suc M ↓ Dˢ (suc n) f
denot-suc {n = n} {f} M↓D[n] =
    ↦-elim (↦-intro (↦-intro (↦-intro (↦-elim var var)))) M↓D[n]
```

## Addition of Scott Numerals via the Y Combinator

Recall that in the [Untyped](https://plfa.github.io/Untyped/) chapter,
addition of Scott numerals is defined as a recursive function using
the Y combinator.  (Shown here with variable names instead of de
Bruijn indices.)

    plus = Y · (ƛ r ⇒ ƛ m ⇒ ƛ n ⇒ case m n (ƛ m' ⇒ `suc (r · m' · n)))

We shall prove that the denotation of `plus` applied to the Scott numerals
for `m` and `n` is `Dˢ (m + n) g` for any path `g`.

    plus[m,n] : ∀{m n : ℕ}{g : ℕ → Value}
       → `∅ ⊢ (plus · scott m) · (scott n) ↓ Dˢ (m + n) g

In the `plus` function, the recursion is on `m`, i.e., the base case
is when `m` is zero and the recursion is on `m' = m - 1`.
So let's think about the denotation of `plus` when `m` is `0` and
then `1` on the way to identifying its denotation for arbitrary `m`.

When `m` is `0`, the denotation of `plus` looks like

    (⊥ ↦ Dˢ n g ↦ Dˢ n g)  ↦  Dˢ n g  ↦  Dˢ n g

Let's see why this works by analyzing the denotation of the term
`ƛ m ⇒ ƛ n ⇒ case m n ...`.  So the parameter `m` and `n` have the
following denotations.

    ⟦m₀⟧ = ⊥ ↦ Dˢ n g ↦ Dˢ n g
    ⟦n⟧ = Dˢ n g

Recall that `case` on a Scott numeral is defined as follows.

    case L M N = L · (ƛ pˢ ⇒ N) · M

So for the `plus` function, the `case m n ...` is really

    m · (ƛ m' ⇒ `suc (r · m' · n)) · n

Guided by the value for parameter `m`, the term `(ƛ m' ⇒ ...)`
should have value `⊥`. Indeed, any term can have value `⊥`.  Next, `n`
should have value `Dˢ n g`, which indeed it does. The result of the
application is `Dˢ n g`, which matches the expected result
`Dˢ (0 + n) g`.

Next consider the meaning of `plus` when `m` is `1`.

      ((⟦m₀⟧ ↦ Dˢ (1 + n) g) ↦ ⊥ ↦ Dˢ (1 + n) g)
    ↦ Dˢ n g
    ↦ Dˢ (1 + n) g

Again we analyze the term `ƛ m ⇒ ƛ n ⇒ case m n ...`.
So the parameters `m` and `n` have the following denotations.

    ⟦m₁⟧ = (⟦m₀⟧ ↦ Dˢ (1 + n) g) ↦ ⊥ ↦ Dˢ (1 + n) g
    ⟦n⟧ = Dˢ n g

Next we analyze the application of `m` to its two arguments.
This time we must check that the argument `(ƛ m' ⇒ ...)`
produces the value

    ⟦m₀⟧ ↦ Dˢ (1 + n) g

So parameter m' has the denotation `⟦m₀⟧`
and we need to show that `suc (r · m' · n)` produces `Dˢ (1 + n) g`.
This can be obtained from the `denot-suc` lemma,
so long as `r · m' · n` produces `Dˢ n g`.
This will be the case so long as `r` has the value

    ⟦m₀⟧  ↦  Dˢ n g  ↦  Dˢ n g

which was the denotation of plus for `m` at zero.
Thus, we have finished analyzing the term `(ƛ m' ⇒ ...)`.

The second argument in the application of `m`, which
is `n`, must have value `⊥`, which of course it does.
Thus, the result of applying `m` to `(ƛ m' ⇒ ...)`
and `n` is indeed `Dˢ (1 + n) g` when `m` is 1.

We have seen the denotation of `plus` for `m` at zero and one, and now
we need to generalize to arbitrary numbers. So let us review
the denotations that we obtained for parameter `m`:

    ⟦m₀⟧ = ⊥ ↦ Dˢ n g ↦ Dˢ n g
    ⟦m₁⟧ = (⟦m₀⟧ ↦ Dˢ (1 + n) g) ↦ ⊥ ↦ Dˢ (1 + n) g

Indeed, these are denotations of a Scott numeral, but over an
interesting choice of path:

    Dˢ n g, Dˢ (1 + n) g, Dˢ (2 + n) g, ..., Dˢ (m + n) g

We define the following function `ms` to produce this path.

```
ms : (n : ℕ) → (ℕ → Value) → (ℕ → Value)
ms n g i = Dˢ (i + n) g
```

The denotations for each `mᵢ` can now be expressed using `Dˢ` and `ms`:

    ⟦mᵢ⟧ = Dˢ i (ms n g)

Now that we have a succinct way to write the denotation of the `m`
parameter, we can write down the denotation of `plus`.

```
plusᵐ : (m n : ℕ) → (ℕ → Value) → Value
plusᵐ m n g = Dˢ m (ms n g) ↦  Dˢ n g  ↦  Dˢ (m + n) g
```

Recall that the denotation of the `r` parameter needs to be the
denotation of `plus` for the previous `m`. Also, when m is zero we did
not use parameter `r`, so its denotation can be `⊥`.  So the following
function gives the denotation for `plus` at `m - 1`.

```
prev-plusᵐ : (m n : ℕ) → (ℕ → Value) → Value
prev-plusᵐ 0 n g = ⊥
prev-plusᵐ (suc m) n g = plusᵐ m n g
```

We are now ready to formally verify the denotation
of the expression

    case m n (ƛ m' ⇒ `suc (r · m' · n))

which translates to de Bruijn notation as follows.

```
CASE : ∅ , ★ , ★ , ★ ⊢ ★
CASE = case (# 1) (# 0) (`suc (# 3 · # 0 · # 1))
```

We show that the denotation of `CASE` is `Dˢ (m + n) g`
under the assumptions that the denotation
of parameter `r` is `prev-plusᵐ m n g`,
parameter `m` is `Dˢ m (ms n g)`, and parameter `n` is `Dˢ n g`.
We proceed by induction on `m`.

```
CASE↓ : (m n : ℕ) (g : ℕ → Value)
      → `∅ `, prev-plusᵐ m n g `, Dˢ m (ms n g) `, Dˢ n g
        ⊢ CASE ↓ Dˢ (m + n) g
CASE↓ zero n g = ↦-elim (↦-elim var ⊥-intro) var
CASE↓ (suc m') n g = ↦-elim (↦-elim var nz-branch) ⊥-intro
    where
    γ = `∅ `, prev-plusᵐ (suc m') n g `, Dˢ (suc m') (ms n g) `, Dˢ n g
    nz-branch : γ ⊢ ƛ (`suc ((# 3) · (# 0) · (# 1)))
                ↓ Dˢ m' (ms n g) ↦ Dˢ (suc m' + n) g
    nz-branch = ↦-intro (denot-suc (↦-elim (↦-elim var var) var))
```

* When `m ≡ 0`, the denotation of m is `⊥ ↦ Dˢ n g ↦  Dˢ n g`.
  The non-zero branch has value `⊥` by `⊥-intro`, and `n`
  has value `Dˢ n g`, so the result of the case is `Dˢ n g`.

* When `m ≡ suc m'`, the denotation of m is

        ⟦m⟧ = Dˢ (suc m') (ms n g)
           = (Dˢ m' (ms n g) ↦ Dˢ (suc m' + n) g) ↦ ⊥ ↦ Dˢ (suc m' + n) g

  so we need to show that the non-zero branch has the value

        Dˢ m' (ms n g) ↦ Dˢ (suc m' + n) g

  Going under the `ƛ`, we need to show that
  `suc (r · m' · n)` produces `Dˢ (suc m' + n) g`.
  Working backwards using the `denot-suc` lemma,
  it suffices to show that `r · m' · n` produces `Dˢ (m' + n) g`.
  The denotation of `r` is `plusᵐ m' n g`, so applying it
  to `m'` and `n` indeed produces `Dˢ (m' + n) g`.

Moving outwards, we now analyze the expression

    ƛ r ⇒ ƛ m ⇒ ƛ n ⇒ case m n (ƛ m' ⇒ `suc (r · m' · n))

We shall show that is has the denotation

      (prev-plusᵐ 0 n g ↦ plusᵐ 0 n g)
    ⊔ (prev-plusᵐ 1 n g ↦ plusᵐ 1 n g)
    ⊔ (prev-plusᵐ 2 n g ↦ plusᵐ 2 n g)
      ...

which we construct with the following `Pᵐ` function (P for plus).

```
Pᵐ : (m n : ℕ) → (ℕ → Value) → Value
Pᵐ 0 n g = ⊥ ↦ plusᵐ 0 n g
Pᵐ (suc m') n g = Pᵐ m' n g ⊔ (plusᵐ m' n g ↦ plusᵐ (suc m') n g)
```

We proceed by induction, using the `CASE↓` lemma to analyze the `CASE`
expression and using the induction hypothesis to accumulate all of the
smaller denotations for plus.

```
P↓Pᵐ : ∀ m n → (g : ℕ → Value) → `∅ ⊢ ƛ (ƛ (ƛ CASE)) ↓ Pᵐ m n g
P↓Pᵐ zero n g = ↦-intro (↦-intro (↦-intro (CASE↓ 0 n g)))
P↓Pᵐ (suc m') n g =
   ⊔-intro (P↓Pᵐ m' n g)
           (↦-intro (↦-intro (↦-intro (CASE↓ (suc m') n g))))
```

We shall need the following lemma, which extracts a single entry from `Pᵐ`.

```
prev↦plus⊑Pᵐ : (m k n : ℕ) → (g : ℕ → Value)
    → prev-plusᵐ m n g ↦ plusᵐ m n g ⊑ Pᵐ (m + k) n g
prev↦plus⊑Pᵐ zero zero n g = ⊑-refl
prev↦plus⊑Pᵐ (suc m') zero n g =
    ⊑-conj-R2 (⊑-fun (⊑-reflexive (cong (λ □ → plusᵐ □ n g) (+-comm m' 0)))
                  (⊑-reflexive (cong (λ □ → plusᵐ (suc □) n g) (+-comm 0 m'))))
prev↦plus⊑Pᵐ m' (suc k) n g =
      let IH = prev↦plus⊑Pᵐ m' k n g in
      ⊑-trans IH (⊑-trans (⊑-conj-R1 ⊑-refl)
                    (⊑-reflexive (cong (λ □ → Pᵐ □ n g) (sym (+-suc m' k)))))
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
previous denotations for M to `plusᵐ m n g`.

    ⟦M₀⟧ = ⊥
    ⟦M₁⟧ = (⟦M₀⟧) ↦ plusᵐ 0 n g
    ⟦M₂⟧ = (⟦M₀⟧ ⊔ ⟦M₁⟧) ↦ plusᵐ 1 n g
    ⟦M₃⟧ = (⟦M₀⟧ ⊔ ⟦M₁⟧ ⊔ ⟦M₂⟧) ↦ plusᵐ 2 n g
    ...

We define the function `Mᵐ` to compute the above denotations
for M, using the auxiliary function `Ms` to join all the
previous denotations of M.

```
Mᵐ : (m n : ℕ) → (ℕ → Value) → Value
Ms : (m n : ℕ) → (ℕ → Value) → Value
Mᵐ 0 n g = ⊥
Mᵐ (suc m') n g = (Ms m' n g)  ↦  plusᵐ m' n g
Ms zero n g = ⊥
Ms (suc m') n g = Ms m' n g ⊔  Mᵐ (suc m') n g
```

We prove by cases that the term M has
the denotation `Mᵐ i n g` for any i from 0 to m + 1,
assuming the `f` parameter has the denotation `Pᵐ m n g`.

```
M↓ : (i k m n : ℕ) (g : ℕ → Value) {lt : suc m ≡ i + k}
   → `∅ `, Pᵐ m n g ⊢ M ↓ Mᵐ i n g
M↓ zero k m n g = ⊥-intro
M↓ (suc i) k m n g {lt} = ↦-intro (↦-elim (sub var H) x·x↓)
  where
  H : prev-plusᵐ i n g ↦ plusᵐ i n g ⊑ Pᵐ m n g
  H = ⊑-trans (prev↦plus⊑Pᵐ i k n g)
              (⊑-reflexive (cong (λ □ → Pᵐ □ n g) (sym (suc-injective lt))))
  x·x↓ : ∀{i} → `∅ `, Pᵐ m n g `, Ms i n g ⊢ (# 0) · (# 0) ↓ prev-plusᵐ i n g
  x·x↓ {zero} = ⊥-intro
  x·x↓ {suc i} = ↦-elim (sub var (⊑-conj-R2 ⊑-refl))
                     (sub var (⊑-conj-R1 ⊑-refl))
```

* The zero case is trivial: we apply `⊥-intro` to show that
  `M` has the value `⊥`.

* For the non-zero case, we need to show that M has the value

        Ms i n g  ↦  plusᵐ i n g

  Going under the `ƛ x`, we need to show that `f · (x · x)`
  has the value `plusᵐ i n g`. The value of `x · x`
  is `prev-plusᵐ i n g`, which we prove by induction on i.
  The case for 0 is trivial because `prev-plusᵐ 0 n g ≡ ⊥`.
  In the case for `suc i`, we need to show that `x · x`
  produces `plusᵐ i n g`. Now the first `x` has the value
  `Ms (suc i) n g`, so by the `sub` rule and `⊑-conj-R2`,
  it also has the value `Mᵐ (suc m') n g`, which is equivalent to

        Ms m' n g  ↦  plusᵐ m' n g

  The second `x`, of course, has the value
  `Ms (suc i) n g`, so by the `sub` rule and `⊑-conj-R1`,
  is has the value
  
        Ms m' n g

  So indeed, apply `x` to itself produces the value `plusᵐ m' n g`.


With the lemma `M↓` in hand, we prove that the term M also produces
the value `Ms i n g` for each i from 0 to m + 1.  We prove this by a
straightforward induction on i.

```
M↓Ms : (i k m n : ℕ) (g : ℕ → Value) {lt : suc m ≡ i + k}
   → `∅ `, Pᵐ m n g ⊢ M ↓ Ms i n g
M↓Ms zero k m n g {lt} = ⊥-intro
M↓Ms (suc i) k m n g {lt} =
    ⊔-intro (M↓Ms i (suc k) m n g {trans lt (sym (+-suc i k))})
            (M↓ (suc i) k m n g {lt})
```

Now for the meaning of the Y combinator. It takes the table of the
plus functions (`Pᵐ m n g`), the meaning of the Scott numeral for m
(`Dˢ m (ms n g)`), and the meaning of n (`Dˢ n g`), and returns the
meaning of the Scott numeral for `m + n` (`Dˢ (m + n) g`).

```
Y↓ : ∀ m n (g : ℕ → Value)
   → `∅ ⊢ Y ↓ Pᵐ m n g ↦ Dˢ m (ms n g) ↦ Dˢ n g ↦ Dˢ (m + n) g
Y↓ m n g = ↦-intro (↦-elim M↓₁ M↓₂)
    where
    M↓₁ : `∅ `, Pᵐ m n g ⊢ M
          ↓ Ms m n g ↦ Dˢ m (ms n g) ↦ Dˢ n g ↦ Dˢ (m + n) g
    M↓₁ = (M↓ (suc m) 0 m n g {cong suc (+-comm 0 m)})
    
    M↓₂ : `∅ `, Pᵐ m n g ⊢ M ↓ Ms m n g
    M↓₂ = (M↓Ms m 1 m n g {+-comm 1 m})
```

The proof is as follows. We first go under the `ƛ f` with `↦-intro`,
so `f` has the value `Pᵐ m n g`.  We then show that M applied to
itself has the value

    Dˢ m (ms n g) ↦ Dˢ n g ↦ Dˢ (m + n) g

We apply the lemma `M↓` as `suc m` to show that the first M
produces

    Ms m n g ↦ Dˢ m (ms n g) ↦ Dˢ n g ↦ Dˢ (m + n) g

We apply the lemma `M↓Ms` to show that the second M produces

    Ms m n g

So putting the above two together, the application `M · M`
produces the following, as desired.

    Dˢ m (ms n g) ↦ Dˢ n g ↦ Dˢ (m + n) g


We now arrive at the finish line: the addition of two Scott numerals
produces the Scott numeral of the sum.

```  
plus[m,n] : ∀{m n : ℕ}{g : ℕ → Value}
       → `∅ ⊢ (plus · scott m) · (scott n) ↓ Dˢ (m + n) g
plus[m,n] {m}{n}{g} =
  ↦-elim (↦-elim (↦-elim (Y↓ m n g) (P↓Pᵐ m n g)) (denot-scott{m}{ms n g}))
         (denot-scott{n}{g})
```

The `plus` function is the Y combinator applied to `ƛ r ⇒ ƛ m ⇒ ƛ n ...`,
So we obtain its meaning using `↦-elim` and the lemmas `Y↓` and `P↓Pᵐ`.
We conclude by appling the result to the denotations of the Scott numerals
for `m` and `n`.

