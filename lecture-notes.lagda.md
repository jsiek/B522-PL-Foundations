```
module lecture-notes where
```

Naturals
--------

Concepts: datatype definitions, constructors, `Set`.

```
data Nat : Set where
  zero : Nat
  suc : Nat → Nat
```

Here are some natural numbers:

```
one = suc zero
two = suc (suc zero)
```

The main way to eliminate a datatype in Agda is to define a recursive
function on it.

```
add : Nat → Nat → Nat
add zero n = n
add (suc m) n = suc (add m n)
```

```
three = add two one
```

To talk about equality we import Agda's `≡` operator.

```
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
```

To prove that something is equal to itself, use `refl`.

```
two-plus-one-is-three : add two one ≡ suc (suc (suc zero))
two-plus-one-is-three = refl
```

Proofs about all the naturals numbers
-------------------------------------

To prove something about all the natural numbers,
such as 

    x + y + x ≡ 2 * x + y

for all x and y, your plan A should be to try and prove
it using the laws of algebra, which are provided in the Agda
standard library.

```
open import Data.Nat
open import Data.Nat.Properties
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_; _≡⟨_⟩_; _∎)
open import Relation.Binary.PropositionalEquality using (sym; cong; cong₂)
```

See the Agda standard library module `Algebra.Definitions` for the
definitions of thinks like `RightIdentity`.


```
xyx : (x : ℕ) → (y : ℕ) → x + y + x ≡ 2 * x + y
xyx x y =
  let L = +-identityˡ in
  let R = +-identityʳ in
  begin
    (x + y) + x
  ≡⟨ +-assoc x y x ⟩
    x + (y + x)
  ≡⟨ cong₂ _+_ {x = x} refl (+-comm y x) ⟩
    x + (x + y)
  ≡⟨ sym (+-assoc x x y) ⟩
    (x + x) + y
  ≡⟨ cong₂ _+_ {u = y} (cong₂ _+_ refl (sym (+-identityʳ x))) refl ⟩
    (x + (x + zero)) + y
  ≡⟨ refl ⟩
    2 * x + y
  ∎
```


Induction
---------

If you don't see a way to prove something about all the natural
numbers using the laws of algebra, then your plan B should be to use
induction.

Such situations often arise when you need to prove something about a
function that you have defined. For example, consider the following
silly example of a recursive function that doubles its input.

```
dub : ℕ → ℕ
dub 0 = 0
dub (suc n) = suc (suc (dub n))
```

We prove that `dub` is correct by induction. That is, we write a
recursive function that takes an integer and returns a proof that

    dub n ≡ n + n

The easiest part of a proof-by-induction is the base case, that is,
for zero. If you have trouble with the base case, there's a good
chance that what you're trying to prove is actually false.

The high-point of a proof-by-induction is the use of the induction
hypothesis (IH), that is, when we make a recursive call. Sometimes we
need to do some reasoning before using the induction hypothesis and
sometimes we do some reasoning afterwards.

```
dub-correct : (n : ℕ) → dub n ≡ n + n
dub-correct zero = refl
dub-correct (suc n) =
  let IH = dub-correct n in
  begin
    suc (suc (dub n))
  ≡⟨ cong suc (cong suc IH) ⟩
    suc (suc (n + n))
  ≡⟨ cong suc (sym (+-suc n n)) ⟩
    suc (n + suc n)
  ∎
```

Predicates
----------

```

```




Relations
---------

