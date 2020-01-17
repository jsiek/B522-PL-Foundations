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

The main way to eliminate a datatype in Agda is to define a function
on it. Often, the function is recursive.

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
_ : add two one ≡ suc (suc (suc zero))
_ = refl
```

The Agda standard library defines a data type for natural numbers, named
`ℕ`, just like the definition above.

```
open import Data.Nat
```

Let's define another recursive function that you may be familiar with,
the sum of the numbers up to a given number `n`.

```
gauss : ℕ → ℕ
gauss zero = 0
gauss (suc n) = suc n + gauss n
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
open import Data.Nat.Properties
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_; _≡⟨_⟩_; _∎)
open import Relation.Binary.PropositionalEquality using (sym; cong)
```

The Agda standard library module
[Data.Nat.Properties](https://github.com/agda/agda-stdlib/blob/master/src/Data/Nat/Properties.agda)
includes proofs for many of the laws of algebra for natural numbers.
Some of those laws refer to names, such as `RightIdentity`, that are
defined in the module
[Algebra.Definitions](https://github.com/agda/agda-stdlib/blob/master/src/Algebra/Definitions.agda).

```
_ : (x : ℕ) → (y : ℕ) → x + y + x ≡ 2 * x + y
_ = λ x y → 
  begin
    (x + y) + x
  ≡⟨ +-assoc x y x ⟩
    x + (y + x)
  ≡⟨ cong (λ □ → x + □) (+-comm y x) ⟩
    x + (x + y)
  ≡⟨ sym (+-assoc x x y) ⟩
    (x + x) + y
  ≡⟨ cong (λ □ → (x + □) + y) (sym (+-identityʳ x)) ⟩
    (x + (x + zero)) + y
  ≡⟨ refl ⟩
    2 * x + y
  ∎
```

If the equation only involves simple reasoning about addition and
multiplication, you can instead use Agda's automatic solver.

```
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver

_ : (x : ℕ) → (y : ℕ) → x + y + x ≡ 2 * x + y
_ = solve 2 (λ x y → x :+ y :+ x := con 2 :* x :+ y) refl
```

The recipe for using the solver is that the first argument is the
number of variables mentioned in the equation, the second argument is
a function of those variables that produces an encoding of the
equation. Put a colon in front of each `+` and `*` and replace `≡` with
`:=`.  Also, put `con` in front of each constant, e.g., change `2` to
`con 2`. The third argument has something to do with how to prove the
leftover equations that the solver couldn't prove. Usually `refl`
works. If it doesn't, good luck to you!


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
  ≡⟨ cong (λ □ → suc (suc □)) IH ⟩
    suc (suc (n + n))
  ≡⟨ cong suc (sym (+-suc n n)) ⟩
    suc (n + suc n)
  ∎
```

As a second example, let's prove the formula of Gauss for the sum of
the first `n` natural numbers. Division on natural numbers can be a
bit awkward to work with, so we'll instead multiply the left-hand side
by `2`.

```
gauss-formula : (n : ℕ) → 2 * gauss n ≡ n * suc n
gauss-formula zero = refl
gauss-formula (suc n) =
  let IH : 2 * gauss n ≡ n * suc n
      IH = gauss-formula n in
  begin
    2 * gauss (suc n)
  ≡⟨ refl ⟩
    2 * (suc n + gauss n)
  ≡⟨ *-distribˡ-+ 2 (suc n) (gauss n) ⟩
    2 * (suc n) + 2 * gauss n
  ≡⟨ cong (λ □ → 2 * (suc n) + □) IH ⟩
    2 * (suc n) + n * (suc n)
  ≡⟨ EQ n ⟩
    (suc n) * suc (suc n)
  ∎
  where
  EQ = solve 1 (λ n → (con 2 :* (con 1 :+ n)) :+ (n :* (con 1 :+ n))
         := (con 1 :+ n) :* (con 1 :+ (con 1 :+ n))) refl
```

* The base case is trivial, indeed `2 * 0 ≡ 0 * suc 0`.

* For the induction step, we need to show that

        2 * gauss (suc n) ≡ (suc n) * suc (suc n)

    In the above chain of equations, we expand the
    definition for `gauss (suc n)`, distribute the multiplication
    by `2`, and then apply the induction hypothesis,
    which states that `2 * gauss n ≡ n * suc n`.
    The last step is some simple reasoning about addition and
    multiplication, which is handled by Agda's automatic solver.


Predicates, Inductively Defined
-------------------------------

Recall that a predicate is a statement involving a variable that can
be true or false. In math, a predicate `P` is often represented as a
Boolean-valued function, so `P x ≡ true` if the statement is true of
the object `x` and `P x ≡ false` if it is false.

In Agda, we often uses datatypes to represent predicates.  We define a
datatype named `P` that is parameterized over the appropriate type,
the `ℕ` below. We then say that `P x` is true if we can
construct an object of type `P x`.

```
data Even : ℕ → Set where
  even-0 : Even 0
  even-+2 : (n : ℕ) → Even n → Even (2 + n)
```

The following constructs a value of type `Even 2`, so it's true that
`2` is even.

```
_ : Even 2
_ = even-+2 0 even-0
```

Similarly for the number `4`.

```
_ : Even 4
_ = even-+2 2 (even-+2 0 even-0)
```

Taking this process to its logical conclusion, we prove that every
number of the form `2 * n`, or equivalently `n + n`, is even.
We'll do this by defining a recursive function `even-dub`
that takes a number `n` and produces an object of type
`Even (n + n)`.

To do this, we'll need a simple equation about addition, which we can
obtain using the solver.

```
sn+sn≡n+n+2 : (n : ℕ) → (suc (n + (suc n))) ≡ (suc (suc (n + n)))
sn+sn≡n+n+2 = solve 1 (λ n → (con 1 :+ (n :+ (con 1 :+ n))) := (con 1 :+ (con 1 :+ (n :+ n)))) refl
```

Here's the definition of `even-dub`.

```
even-dub : (n : ℕ) → Even (n + n)
even-dub zero = even-0
even-dub (suc n) rewrite sn+sn≡n+n+2 n =
    let IH : Even (n + n)
        IH = even-dub n in
    even-+2 (n + n) IH 
```

* For the base case, we construct an object of type `Even (0 + 0)`,
  that is `Even 0`, using `even-0`.

* For the induction step, we need to construct an object of type `Even
  (suc (n + suc n))`. We `rewrite` using the equation `sn+sn≡n+n+2` to
  transform this goal to `Even ((n + n) + 2)`. By the induction
  hypothesis (i.e. recursive call to `even-dub`), we have `Even (n +
  n)`, so we conclude by applying the constructor `even-+2`.


If we know a number is `Even`, then it must have been generated by one
of the two rules. We can use the pattern matching associated with
function definitions to reason backwards about the rules.  For
example, if `Even m` and `m` is not zero, then there is a number `n`
two less-than `m` that is also even.

```
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Data.Empty using (⊥-elim)
```

```
inv-Even : (n m : ℕ) → Even m → m ≢ 0 → suc (suc n) ≡ m → Even n
inv-Even n .0 even-0 m≢0 n+2≡m = ⊥-elim (m≢0 refl)
inv-Even n .(suc (suc n')) (even-+2 n' even-m) m≢0 refl = even-m
```

* In the case for `even-0`, we have a contradiction: `m ≡ 0` and `m ≢ 0`.
  We can `⊥-elim` to prove anything from a proof of false, written `⊥`.
  Also, recall that `m ≢ 0` is short for `¬ (m ≡ 0)` and
  negation is shorthand for implication to false, in this case
  `m ≡ 0 → ⊥`. 

* In the case for `even-+2` we know that `m` is `n' + 2`,
  so `n + 2 ≡ n' + 2` and therefore `n = n'` by
  `+-cancelʳ-≡`. We have `even-m : Even n'` and
  the goal is `Even n`, so we conclude by rewriting by 
  `n = n'` and then using `even-m`.

Relations, Inductively Defined
------------------------------

Like predicates, relations can be represented in Agda with data types,
they just have more parameters.

One of the most important relations in Number Theory is the divides
(evenly) relation.  We say that `m` divides `n` if some number of
copies of `m` can be concatenated (added) to form `n`.

```
data _div_ : ℕ → ℕ → Set where
  div-refl : (m : ℕ) → m ≢ 0 → m div m
  div-step : (n m : ℕ) → m div n → m div (m + n)
```

For example, `3 div 3`, `3 div 6`, and `3 div 6`.

```
3-div-3 : 3 div 3
3-div-3 = div-refl 3 λ ()

3-div-6 : 3 div 6
3-div-6 = div-step 3 3 3-div-3

3-div-9 : 3 div 9
3-div-9 = div-step 6 3 3-div-6
```

If `m div n`, then neither `m` nor `n` can be zero.  We can prove these
two facts by eliminating `m div n` with recursive functions.

```
div→m≢0 : (m n : ℕ) → m div n → m ≢ 0
div→m≢0 m .m (div-refl .m m≢0) = m≢0
div→m≢0 m .(m + n) (div-step n .m mn) = div→m≢0 m n mn
```

```
div→n≢0 : (m n : ℕ) → m div n → n ≢ 0
div→n≢0 m .m (div-refl .m m≢0) = m≢0
div→n≢0 m .(m + n) (div-step n .m mn) =
  let IH = div→n≢0 m n mn in
  λ mn0 → IH (m+n≡0⇒n≡0 m mn0)
```

An alternative way to state that a number evenly divides another
number is using multiplication instead of repeated addition.  We shall
prove that if `m div n`, then there exists some number `k` such that
`k * m ≡ n`. In Agda, we use a **dependent product** to express
"there exists". A dependent product is simply a pair where the
**type** of the second part of the pair can refer to the the first
part of the pair.  To express "there exists", the witness of the
existential is the first part of the pair. The type of the second part
of the pair is some formula involving the first part, and the value in
the second part of the pair is a proof of that formula. So to
express "there exists some number `k` such that
`k * m ≡ n`", we use the type

    Σ[ k ∈ ℕ ] k * m ≡ n

where `k` is a name for the first part of the pair,
`ℕ` is it's type, and `k * m ≡ n` is the type
for the second part of the pair.
(This is covered in more depth in Chapter
[Quantifiers](https://plfa.github.io/Quantifiers/)).

```
open import Data.Product using (Σ-syntax) renaming (_,_ to ⟨_,_⟩)
```

We construct a dependent product using the notation `⟨_,_⟩`.
For example, the following proves that there exists
some number `k` such that `k * m ≡ 0`, for any `m`.

```
_ : (m : ℕ) → Σ[ k ∈ ℕ ] k * m ≡ 0
_ = λ m → ⟨ 0 , refl ⟩
```

Getting back to the alternative way to state the divides relation, the
following proof by induction shows that `m div n` implies
that there exists some `k` such that `k * m ≡ n`.

```
div→k*m≡n : (m n : ℕ) → m div n → Σ[ k ∈ ℕ ] k * m ≡ n
div→k*m≡n m .m (div-refl .m x) = ⟨ 1 , +-identityʳ m ⟩
div→k*m≡n m .(m + n) (div-step n .m mn)
    with div→k*m≡n m n mn
... | ⟨ q , q*m≡n ⟩
    rewrite sym q*m≡n =
      ⟨ (suc q) , refl ⟩
```

* For the case `div-refl`, we need to show that `k * m ≡ m`
  for some `k`. That's easy, choose `k ≡ 1`. So we
  form a dependent pair with `1` as the first part
  and a proof of `1 * m ≡ m` as the second part.

* For the case `div-step`, we need to show that `k * m ≡ m + n` for some `k`.
  The induction hypothesis tells us that `q * m ≡ n` for some `q`.
  We can get our hands on this `q` by pattern matching on the
  dependent pair returned by `div→k*m≡n`, using the `with` construct.
  If we replace the `n` in the goal with `q * m`, the goal becomes
  `k * m ≡ m + q * m` which is equivalent to
  `k * m ≡ suc q * m`. We can accomplish this replacement by
  using `rewrite` with the symmetric version of the equation `q * m ≡ n`.
  Finally, we conclude the proof by choosing `suc q` as the witness
  for `k`, and `refl` for the proof that `suc q * m ≡ suc q * m`.

Going in the other direction, if we know that `n ≡ k * m`, then `m div n`
(provided `k` and `m` are not zero).

```
m-div-k*m : (k m : ℕ) → m ≢ 0 → k ≢ 0 → m div (k * m)
m-div-k*m zero m m≢0 k≢0 = ⊥-elim (k≢0 refl)
m-div-k*m (suc zero) m m≢0 k≢0
    rewrite +-identityʳ m = div-refl m m≢0
m-div-k*m (suc (suc k)) m m≢0 k≢0 =
    let IH = m-div-k*m (suc k) m m≢0 λ () in
    div-step (m + k * m) m IH
```

A common property of relations is transitivity.  Indeed, the `div`
relation is transitive. We prove this fact directly using the facts
that we've already proved about `div`. That is, from `m div n` and `n
div p`, we have `k₁ * m ≡ n` and `k₂ * n ≡ p` (by `div→k*m≡n`). We can
substitute `k₁ * m` for `n` in the later formula to obtain `k₂ * k₁ *
m ≡ p`, which shows that `m` divides `p` (by `m-div-k*m`).  However,
to use `m-div-k*m` we have two remaining details to prove.
We need to show that `m ≢ 0` and `k₂ * k₁ ≢ 0`.
We obtain `m ≢ 0` using `div→m≢0`.
Similarly, by `div→n≢0` we know `k₂ * k₁ * m ≢ 0`.  Towards a contradiction, if
`k₂ * k₁ ≡ 0`, then we would also have `k₂ * k₁ * m ≡ 0`, but we know
that is false.

```
div-trans : (m n p : ℕ) → m div n → n div p → m div p
div-trans m n p mn np
    with div→k*m≡n m n mn | div→k*m≡n n p np
... | ⟨ k₁ , k₁*m≡n ⟩ | ⟨ k₂ , k₂*k₁*m≡p ⟩
    rewrite sym k₁*m≡n | sym k₂*k₁*m≡p | sym (*-assoc k₂ k₁ m) =
    m-div-k*m (k₂ * k₁) m m≢0 (k₂*k₁≢0 k₂*k₁*m≢0)
    
    where
    m≢0 = div→m≢0 m (k₁ * m) mn
    k₂*k₁*m≢0 = div→n≢0 (k₁ * m) (k₂ * k₁ * m) np

    k₂*k₁≢0 : k₂ * k₁ * m ≢ 0 → k₂ * k₁ ≢ 0
    k₂*k₁≢0 k₂*k₁*m≢0 k₂*k₁≡0
        rewrite k₂*k₁≡0 = k₂*k₁*m≢0 refl
```

Isomorphism
-----------

```
infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
```

Example: ℕ is isomorphic to the even numbers.

```
even-m→m≡n+n : (m : ℕ) → Even m → Σ[ n ∈ ℕ ] m ≡ n + n
even-m→m≡n+n .0 even-0 = ⟨ 0 , refl ⟩
even-m→m≡n+n .(suc (suc n)) (even-+2 n even-m)
  with even-m→m≡n+n n even-m
... | ⟨ p , refl ⟩ =   
    ⟨ suc p , EQ p ⟩
  where
  EQ : (p : ℕ) → suc (suc (p + p)) ≡ suc (p + suc p)
  EQ = solve 1 (λ p → con 1 :+ (con 1 :+ (p :+ p)) := con 1 :+ (p :+ (con 1 :+ p))) refl
```

```
dub-div2 : ∀ (n : ℕ) → ⌊ n + n /2⌋ ≡ n
dub-div2 zero = refl
dub-div2 (suc n) =
  let IH = dub-div2 n in
  begin
  ⌊ suc (n + suc n) /2⌋        ≡⟨ cong ⌊_/2⌋ (EQ n) ⟩
  ⌊ suc (suc (n + n)) /2⌋      ≡⟨ refl ⟩
  suc ⌊ n + n /2⌋              ≡⟨ cong suc IH ⟩
  suc n
  ∎
  where
  EQ : (n : ℕ) → suc (n + suc n) ≡ suc (suc (n + n))
  EQ = solve 1 (λ n → con 1 :+ (n :+ (con 1 :+ n)) := con 1 :+ (con 1 :+ (n :+ n))) refl

```

```
data IsEven : ℕ → Set
data IsOdd : ℕ → Set

data IsEven where
  is-even : ∀ n m → n ≡ m + m → IsEven n

data IsOdd where
  is-odd : ∀ n m → n ≡ suc (m + m) → IsOdd n

open import Data.Sum

sm+sm≡ss[m+m] : ∀ m → (suc m) + (suc m) ≡ suc (suc (m + m))
sm+sm≡ss[m+m] = solve 1 (λ m → (con 1 :+ m) :+ (con 1 :+ m) := con 1 :+ (con 1 :+ (m :+ m))) refl

even+odd : ∀ (n : ℕ) → IsEven n ⊎ IsOdd n
even+odd zero = inj₁ (is-even 0 0 refl)
even+odd (suc n)
    with even+odd n
... | inj₁ (is-even n m refl) =
      inj₂ (is-odd (suc (m + m)) m refl)
... | inj₂ (is-odd n m refl) =
      inj₁ (is-even (suc (suc (m + m))) (suc m) (sym (sm+sm≡ss[m+m] m)))

data Evens : Set where
  even : (n : ℕ) → .(IsEven n) → Evens

to-evens : ℕ → Evens
to-evens n = even (n + n) (is-even (n + n) n refl)

from-evens : Evens → ℕ
from-evens (even n even-n) = ⌊ n /2⌋

from∘to-evens : ∀ (n : ℕ) → from-evens (to-evens n) ≡ n
from∘to-evens zero = refl
from∘to-evens (suc n) =
  begin
  from-evens (to-evens (suc n))                            ≡⟨ refl ⟩
  from-evens (even ((suc n) + (suc n)) (is-even (suc (n + suc n)) (suc n) refl)) ≡⟨ refl ⟩
  ⌊ (suc n) + (suc n) /2⌋                                  ≡⟨ dub-div2 (suc n) ⟩
  suc n
  ∎ 

Evens≡ : ∀(x y : ℕ).(p : IsEven x).(q : IsEven y) → x ≡ y → (even x p) ≡ (even y q)
Evens≡ x y p q refl = refl  

open import Data.Empty using (⊥)

n+n≢1 : ∀ n → n + n ≢ 1
n+n≢1 zero = λ ()
n+n≢1 (suc n) rewrite +-comm n (suc n) = λ ()

suc[z+z]≢y+y : ∀ z y → suc (z + z) ≡ y + y → ⊥
suc[z+z]≢y+y z y eq =
  let eq2 : 1 + (z + z) ≡ y + y
      eq2 = eq in
  let eq3 : 1 ≡ (y + y) ∸ (z + z)
      eq3 = begin
            1                      ≡⟨ {!!} ⟩
            1 + (z + z) ∸ (z + z)  ≡⟨ {!!} ⟩
            (y + y) ∸ (z + z)
            ∎ in
  {!!}

{-

1 ≡ 2y - 2z ≡ 2(y - z)

-}

odd-not-even : ∀ n → IsEven (suc (n + n)) → ⊥
odd-not-even n (is-even .(suc (n + n)) m x) = {!!}

{-
odd-not-even zero (is-even .1 m 1≡m+m) = n+n≢1 m (sym 1≡m+m)
odd-not-even (suc n) =
  let IH = odd-not-even n in
  λ even+3 → IH {!!}
-}

import Data.Empty.Irrelevant

⌊n/2⌋+⌊n/2⌋≡n : ∀ n → .(IsEven n) → ⌊ n /2⌋ + ⌊ n /2⌋ ≡ n
⌊n/2⌋+⌊n/2⌋≡n n even-n
    with even+odd n
... | inj₁ (is-even n m refl)
    rewrite dub-div2 m = refl
... | inj₂ (is-odd n m refl) =
    Data.Empty.Irrelevant.⊥-elim {!!}

to∘from-evens : ∀ (e : Evens) → to-evens (from-evens e) ≡ e
to∘from-evens (even n even-n) =
  begin
    to-evens ⌊ n /2⌋       ≡⟨ refl ⟩
    even (⌊ n /2⌋ + ⌊ n /2⌋) (is-even (⌊ n /2⌋ + ⌊ n /2⌋) ⌊ n /2⌋ refl)  ≡⟨ Evens≡ (⌊ n /2⌋ + ⌊ n /2⌋) n (is-even (⌊ n /2⌋ + ⌊ n /2⌋) ⌊ n /2⌋ refl) even-n (⌊n/2⌋+⌊n/2⌋≡n n even-n) ⟩
    even n even-n
  ∎

{-
open import Data.Product using (proj₁)

data Evens : Set where
  even : (n : ℕ) → .(Even n) → Evens
  

to-evens : ℕ → Evens
to-evens n = even (n + n) (even-dub n)

from-evens : Evens → ℕ
from-evens (even n even-n) = ⌊ n /2⌋

from∘to-evens : ∀ (n : ℕ) → from-evens (to-evens n) ≡ n
from∘to-evens zero = refl
from∘to-evens (suc n) =
  begin
  from-evens (to-evens (suc n))                            ≡⟨ refl ⟩
  from-evens (even ((suc n) + (suc n)) (even-dub (suc n))) ≡⟨ refl ⟩
  ⌊ (suc n) + (suc n) /2⌋                                  ≡⟨ dub-div2 (suc n) ⟩
  suc n
  ∎ 

⌊n/2⌋+⌈n/2⌉≡n : ∀ n → ⌊ n /2⌋ + ⌈ n /2⌉ ≡ n
⌊n/2⌋+⌈n/2⌉≡n zero    = refl
⌊n/2⌋+⌈n/2⌉≡n (suc n) = begin
  ⌊ suc n /2⌋ + suc ⌊ n /2⌋   ≡⟨ +-comm ⌊ suc n /2⌋ (suc ⌊ n /2⌋) ⟩
  suc ⌊ n /2⌋ + ⌊ suc n /2⌋   ≡⟨ refl ⟩
  suc (⌊ n /2⌋ + ⌊ suc n /2⌋) ≡⟨ cong suc (⌊n/2⌋+⌈n/2⌉≡n n) ⟩
  suc n                       ∎

even-2+n→even-n : ∀ n → .(Even (suc (suc n))) → Even n
even-2+n→even-n n e2n = {!!}

⌊n/2⌋+⌊n/2⌋≡n : ∀ n → .(Even n) → ⌊ n /2⌋ + ⌊ n /2⌋ ≡ n
⌊n/2⌋+⌊n/2⌋≡n zero even-n = refl
⌊n/2⌋+⌊n/2⌋≡n (suc (suc n)) even-2+n =
  begin
  suc (⌊ n /2⌋ + suc ⌊ n /2⌋)      ≡⟨ cong suc (+-suc ⌊ n /2⌋ ⌊ n /2⌋) ⟩
  suc (suc (⌊ n /2⌋ + ⌊ n /2⌋))    ≡⟨ cong (λ □ → suc (suc □)) (⌊n/2⌋+⌊n/2⌋≡n n EN) ⟩
  suc (suc n)
  ∎
  where
  EN : Even n
  EN = even-2+n→even-n n even-2+n

Evens≡ : ∀(x y : ℕ).(p : Even x).(q : Even y) → x ≡ y → (even x p) ≡ (even y q)
Evens≡ x y p q refl = refl  

to∘from-evens : ∀ (e : Evens) → to-evens (from-evens e) ≡ e
to∘from-evens (even n even-n) =
  begin
  to-evens (from-evens (even n even-n))        ≡⟨ refl ⟩
  to-evens ⌊ n /2⌋                             ≡⟨ refl ⟩
  even (⌊ n /2⌋ + ⌊ n /2⌋) (even-dub ⌊ n /2⌋)  ≡⟨ Evens≡ ((⌊ n /2⌋ + ⌊ n /2⌋)) n ((even-dub ⌊ n /2⌋)) even-n (⌊n/2⌋+⌊n/2⌋≡n n even-n) ⟩
  even n even-n
  ∎

ℕ≃Evens : ℕ ≃ Evens
ℕ≃Evens =
  record {
    to = to-evens ; 
    from = from-evens ;
    from∘to = from∘to-evens ;
    to∘from = to∘from-evens }
-}
```


Example: products are commutative upto isomorphism.

```
open import Data.Product renaming (_,_ to ⟨_,_⟩)

×-comm : ∀{A B : Set} → A × B ≃ B × A
×-comm =
  record {
    to = λ { ⟨ x , y ⟩ → ⟨ y , x ⟩ } ;
    from = λ { ⟨ x , y ⟩ → ⟨ y , x ⟩ } ;
    from∘to = λ { ⟨ x , y ⟩ → refl }  ;
    to∘from = λ { ⟨ x , y ⟩ → refl } }
```

