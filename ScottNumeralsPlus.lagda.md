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

We need the following corollary of `⊑-refl`, and it should perhaps be
defined in the Denotational chapter.

```
⊑-reflexive : ∀{v w : Value} → v ≡ w → v ⊑ w
⊑-reflexive refl = ⊑-refl
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

We shall need the following two basic properties of `nth` and the list
append function `++`.

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


    plus[m,n] : ∀{m n : ℕ}{rs : List Value}
       → `∅ ⊢ (plus · scott m) · (scott n) ↓ Dˢ (m + n) rs

In the `plus` function, the recursion is on `m`, i.e., the base case
is when `m` is zero, and the recursive call to `r` is given
`m' = m - 1`. So let's think about the denotation of `plus`
when `m` is `0`, then `1`, and then `2`.

When `m` is `0`, the denotation of `plus` looks like

    (⊥ ↦ Dˢ n rs ↦ Dˢ n rs)  ↦  Dˢ n rs  ↦  Dˢ n rs

Let's look closely at why this works, analyzing the denotation
of the term `ƛ m ⇒ ƛ n ⇒ case m n ...`.
So the parameter `m` and `n` are is bound to values as follows

    m := ⊥ ↦ Dˢ n rs ↦ Dˢ n rs
    n := Dˢ n rs

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

Next consider when `m` is `1`. The denotation of `plus` grows
to be more complicated, especially regarding its first argument.

      (((⊥ ↦ Dˢ n rs ↦ Dˢ n rs) ↦ Dˢ (1 + n) rs) ↦ ⊥ ↦ Dˢ (1 + n) rs)
    ↦ Dˢ n rs
    ↦ Dˢ (1 + n) rs

Again we analyze the term `ƛ m ⇒ ƛ n ⇒ case m n ...`.
So the parameter `m` and `n` are is bound to values as follows

    m := ((⊥ ↦ Dˢ n rs ↦ Dˢ n rs) ↦ Dˢ (1 + n) rs) ↦ ⊥ ↦ Dˢ (1 + n) rs
    n := Dˢ n rs

Next we analyze the application of `m` to its two arguments.
This time we must check that the argument `(ƛ m' ⇒ ...)`
produces the value

    (⊥ ↦ Dˢ n rs ↦ Dˢ n rs) ↦ Dˢ (1 + n) rs

So we have the binding

    m' := (⊥ ↦ Dˢ n rs ↦ Dˢ n rs)

and need to show that `suc (r · m' · n)` produces `Dˢ (1 + n) rs`.
This can be obtained from the `denot-suc` lemma,
so long as `r · m' · n` produces `Dˢ n rs`.
This will be the case so long as `r` has the value

    (⊥ ↦ Dˢ n rs ↦ Dˢ n rs)  ↦  Dˢ n rs  ↦  Dˢ n rs

which was the denotation of plus for `m` at zero.
Thus, we have finished analyzing the first argument `(ƛ m' ⇒ ...)`.

The second argument in the application of `m`, which
is `n`, must have value `⊥`, which of course it does.
Thus, the result of applying `m` to `(ƛ m' ⇒ ...)`
and `n` is indeed `Dˢ (1 + n) rs` when `m` is 1.

We have seen the denotation of `plus` for `m` at zero and one, and now
we need to generalize to arbitrary numbers. So let us review
the denotations that we obtained for `m`:

    m₀ := ⊥ ↦ Dˢ n rs ↦ Dˢ n rs
    m₁ := ((⊥ ↦ Dˢ n rs ↦ Dˢ n rs) ↦ Dˢ (1 + n) rs) ↦ ⊥ ↦ Dˢ (1 + n) rs

Indeed, these are denotations of a Scott numeral, but over an
interesting choice of path:

    Dˢ n rs, Dˢ (1 + n) rs, Dˢ (2 + n) rs, ..., Dˢ (m + n) rs

We define the following function `ms` to produce this path.

```
ms : (m n : ℕ) → List Value → List Value
ms zero n rs = (Dˢ n rs) ∷ []
ms (suc m) n rs = ms m n rs ++ ((Dˢ (suc m + n) rs) ∷ [])
```

The denotations for `m` can now be expressed using `Dˢ` and `ms`:

    m₀ := Dˢ 0 (ms m n rs)
    m₁ := Dˢ 1 (ms m n rs)
    m₂ := Dˢ 2 (ms m n rs)
    ...

Of course, the length of the list produced by `ms m n rs` is `suc m`.

```
len-ms : ∀(m n : ℕ) → (rs : List Value) → length (ms m n rs) ≡ suc m
len-ms zero n rs = refl
len-ms (suc m) n rs =
    trans (length-++ (ms m n rs))
          (trans (cong₂ _+_ (len-ms m n rs) refl)
                 (cong suc (+-comm m _)))
```

The ith element of the list `ms m n rs` is `Dˢ (i + n) rs`.

```
nth-ms : ∀ i m' n → (rs : List Value) → .{lt'' : i ≤ m'}
   → nth i (ms m' n rs) ≡ Dˢ (i + n) rs
nth-ms zero zero n rs = refl
nth-ms i (suc m') n rs {lt''}
    with i ≟ suc m'
... | yes refl =
      nth-++-> {suc m'} {0} {ms m' n rs} {_}
         {sym (trans (+-comm (length (ms m' n rs)) 0) (len-ms m' n rs))}
         {s≤s z≤n} 
... | no neq =
      let IH = nth-ms i m' n rs {≤-pred (≤∧≢⇒< lt'' neq)} in
      trans (nth-++ {i}{ms m' n rs}{_}{≤-trans (≤∧≢⇒< lt'' neq)
                                           (≤-reflexive (sym (len-ms m' n rs)))})
            IH
```

Now that we have a succinct way to write the denotation of the `m`
parameter, we can write down the denotation of `plus`.

    plus₀ = Dˢ 0 (ms m n rs)  ↦  Dˢ n rs  ↦  Dˢ (0 + n) rs
    plus₁ = Dˢ 1 (ms m n rs)  ↦  Dˢ n rs  ↦  Dˢ (1 + n) rs
    plus₂ = Dˢ 2 (ms m n rs)  ↦  Dˢ n rs  ↦  Dˢ (2 + n) rs

So in general, the ith denotation for `plus` is given by the following
`plusᵐ` function.

```
plusᵐ : (i m n : ℕ) → List Value → Value
plusᵐ i m n rs = Dˢ i (ms m n rs) ↦  Dˢ n rs  ↦  Dˢ (i + n) rs
```

```
prev-plusᵐ : (i m n : ℕ) → List Value → Value
prev-plusᵐ 0 m n rs = ⊥
prev-plusᵐ (suc i) m n rs = plusᵐ i m n rs

CASE : ∅ , ★ , ★ , ★ ⊢ ★
CASE = case (# 1) (# 0) (`suc (# 3 · # 0 · # 1))

  
plus[m,n] : ∀{m n : ℕ}{rs : List Value}
       → `∅ ⊢ (plus · scott m) · (scott n) ↓ Dˢ (m + n) rs
plus[m,n] {m}{n}{rs} =
  ↦-elim (↦-elim (↦-elim Y↓ (P↓Tᵐ {m}{≤-refl})) (denot-scott{m}{ms m n rs})) (denot-scott{n}{rs})
  where

  CASE↓ : (m' : ℕ) .{lt' : m' ≤ m}
        → `∅ `,
           prev-plusᵐ m' m n rs `,
           Dˢ m' (ms m n rs) `,
           Dˢ n rs
          ⊢ CASE ↓ Dˢ (m' + n) rs
  CASE↓ zero {lt'} rewrite nth-ms 0 m n rs {lt'} = ↦-elim (↦-elim var ⊥-intro) var
  CASE↓ (suc m') {lt'} rewrite nth-ms (suc m') m n rs {lt'} =
      ↦-elim (↦-elim var (↦-intro (denot-suc (↦-elim (↦-elim var var) var) ))) ⊥-intro

  Tᵐ : (m' : ℕ) → Value
  Tᵐ 0 = ⊥ ↦ (plusᵐ 0 m n rs)
  Tᵐ (suc m') = Tᵐ m' ⊔ (plusᵐ m' m n rs ↦ plusᵐ (suc m') m n rs)

  P↓Tᵐ : ∀{m'}{lt : m' ≤ m} → `∅ ⊢ ƛ (ƛ (ƛ CASE)) ↓ Tᵐ m'
  P↓Tᵐ {zero} = ↦-intro (↦-intro (↦-intro (CASE↓ 0 {z≤n})))
  P↓Tᵐ {suc m'} {lt} =
     let C = CASE↓ (suc m') {lt} in
     ⊔-intro (P↓Tᵐ {m'}{≤-trans (≤-step ≤-refl) lt}) (↦-intro (↦-intro (↦-intro C)))
     
  prev-plus↦plus⊑Tᵐ : (m' k : ℕ)
      → prev-plusᵐ m' m n rs ↦ plusᵐ m' m n rs ⊑ Tᵐ (m' + k)
  prev-plus↦plus⊑Tᵐ zero zero = ⊑-refl
  prev-plus↦plus⊑Tᵐ (suc m') zero =
      ⊑-conj-R2 (⊑-fun (⊑-reflexive (cong (λ □ → plusᵐ □ m n rs) (+-comm m' 0)))
                       (⊑-reflexive (cong (λ □ → plusᵐ (suc □) m n rs) (+-comm 0 m'))))
  prev-plus↦plus⊑Tᵐ m' (suc k) =
        let IH = prev-plus↦plus⊑Tᵐ m' k in
        ⊑-trans IH (⊑-trans (⊑-conj-R1 ⊑-refl) (⊑-reflexive (cong Tᵐ (sym (+-suc m' k)))))

  M = ƛ (# 1 · (# 0 · # 0))

  Ms : (m' : ℕ) → Value
  Mᵐ : (m' : ℕ) → Value
  Mᵐ 0 = ⊥
  Mᵐ (suc m') = (Ms m')  ↦  plusᵐ m' m n rs
  Ms zero = ⊥
  Ms (suc m') = Mᵐ (suc m')  ⊔  Ms m'

  M↓ : (m' : ℕ) {k : ℕ}{lt : suc m ≡ m' + k} → `∅ `, Tᵐ m ⊢ M ↓ Mᵐ m'
  M↓ zero = ⊥-intro
  M↓ (suc m'){k}{lt} = ↦-intro (↦-elim (sub var H) G)
      where
      H : prev-plusᵐ m' m n rs ↦ plusᵐ m' m n rs ⊑ Tᵐ m
      H = let xx = prev-plus↦plus⊑Tᵐ m' k in
         ⊑-trans xx (⊑-reflexive (cong Tᵐ (sym (suc-injective lt))))

      G : ∀{m'} → `∅ `, Tᵐ m `, Ms m' ⊢ (# 0) · (# 0) ↓ prev-plusᵐ m' m n rs
      G {zero} = ⊥-intro
      G {suc m'} = ↦-elim (sub var (⊑-conj-R1 ⊑-refl))
                          (sub var (⊑-conj-R2 ⊑-refl))

  M↓Ms : (m' : ℕ) {k : ℕ}{lt : suc m ≡ m' + k} → `∅ `, Tᵐ m ⊢ M ↓ Ms m'
  M↓Ms zero {k} {lt} = ⊥-intro
  M↓Ms (suc m') {k} {lt} = ⊔-intro (M↓ (suc m') {k}{lt})
                                 (M↓Ms m' {suc k}{trans lt (sym (+-suc m' k))})

  Y↓ : `∅ ⊢ ƛ M · M ↓ Tᵐ m ↦ Dˢ m (ms m n rs) ↦ Dˢ n rs ↦ Dˢ (m + n) rs
  Y↓ = ↦-intro (↦-elim (M↓ (suc m) {0}{cong suc (+-comm 0 m)})
                       (M↓Ms m {1}{+-comm 1 m}))
  
```
