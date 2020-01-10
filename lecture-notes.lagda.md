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
two-plus-one-is-three : add two one ≡ suc (suc (suc zero))
two-plus-one-is-three = refl
```

The Agda standard library defines a data types natural numbers, named
`ℕ`, similar to the definition above.

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
open import Relation.Binary.PropositionalEquality using (sym; cong; cong₂)
```

The Agda standard library module
[Data.Nat.Properties](https://github.com/agda/agda-stdlib/blob/master/src/Data/Nat/Properties.agda)
includes proofs for many of the laws of algebra for natural numbers.
Some of those laws refer to names, such as `RightIdentity`, that are
defined in the module
[Algebra.Definitions](https://github.com/agda/agda-stdlib/blob/master/src/Algebra/Definitions.agda).

```
xyx : (x : ℕ) → (y : ℕ) → x + y + x ≡ 2 * x + y
xyx x y =
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

If the equation only involves simple reasoning about addition and
multiplication, you can instead use Agda's automatic solver.

```
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver

xyx' : (x : ℕ) → (y : ℕ) → x + y + x ≡ 2 * x + y
xyx' = solve 2 (λ x y → x :+ y :+ x := con 2 :* x :+ y) refl
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
  ≡⟨ cong suc (cong suc IH) ⟩
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
  ≡⟨ cong₂ _+_ refl IH ⟩
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
  even-+2 : (n : ℕ) → Even n → Even (n + 2)
```

The following constructs a value of type `Even 2`, so it's true that
`2` is even.

```
Even-2 : Even 2
Even-2 = even-+2 0 even-0
```

Similarly for the number `4`.

```
Even-4 : Even 4
Even-4 = even-+2 2 Even-2
```

Taking this process to its logical conclusion, we prove that every
number of the form `2 * n`, or equivalently `n + n`, is even.
We'll do this by defining a recursive function `even-dub`
that takes a number `n` and produces an object of type
`Even (n + n)`.

To do this, we'll need a simple equation about addition, which we can
obtain using the solver.

```
snsn≡nn2 : (n : ℕ) → ((suc n) + (suc n)) ≡ (n + n) + 2
snsn≡nn2 = solve 1 (λ n → ((con 1 :+ n) :+ (con 1 :+ n)) := (n :+ n) :+ con 2) refl
```

Here's the definition of `even-dub`.

```
even-dub : (n : ℕ) → Even (n + n)
even-dub zero = even-0
even-dub (suc n) rewrite snsn≡nn2 n =
    let IH : Even (n + n)
        IH = even-dub n in
    even-+2 (n + n) IH
```

* For the base case, we construct an object of type `Even (0 + 0)`,
  that is `Even 0`, using `even-0`.

* For the induction step, we need to construct an object of type `Even
  (suc (n + suc n))`. We `rewrite` using the equation `snsn≡nn2` to
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
inv-Even : (n m : ℕ) → Even m → m ≢ 0 → n + 2 ≡ m → Even n
inv-Even n .0 even-0 m≢0 n+2≡m = ⊥-elim (m≢0 refl)
inv-Even n .(n' + 2) (even-+2 n' even-m) m≢0 n+2≡m
    rewrite +-cancelʳ-≡ n n' n+2≡m = even-m
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

One of the most important relations in Number Theory is the (evenly) divides relation.
We say that `m` divides `n` if some number of copies of `m` can be concatenated
(added) to form `n`.

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

If `m div n`, then neither `m` or `n` can be zero.  We can prove these
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
``there exists``. A dependent product is simply a pair where the
**type** of the second part of the pair can refer to the the first
part of the pair.  To express ``there exists``, the witness of the
existential is the first part of the pair. The type of the second part
of the pair is some formula involving the first part, and the value in
the second part of the pair is a proof of that formula. So to
express there exists some number `k` such that
`k * m ≡ n`, we use the type

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
0*m≡0 : (m : ℕ) → Σ[ k ∈ ℕ ] k * m ≡ 0
0*m≡0 m = ⟨ 0 , refl ⟩
```

Getting back to the alternative way to state the divides relation, the
following proof by induction shows that `m div n` implies
that there exists some `k` such that `k * m ≡ n`.

```
div→alt : (m n : ℕ) → m div n → Σ[ k ∈ ℕ ] k * m ≡ n
div→alt m .m (div-refl .m x) = ⟨ 1 , +-identityʳ m ⟩
div→alt m .(m + n) (div-step n .m mn)
    with div→alt m n mn
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
  dependent pair returned by `div→alt`, using the `with` construct.
  If we replace the `n` in the goal with `q * m`, the goal becomes
  `k * m ≡ m + q * m` which is equivalent to
  `k * m ≡ suc q * m`. We can accomplish this replacement by
  using `rewrite` with the symmetric version of the equation `q * m ≡ n`.
  Finally, we conclude the proof by choosing `suc q` as the witness
  for `k`, and `refl` for the proof that `suc q * m ≡ suc q * m`.

```
m-div-skm : (k m : ℕ) → m ≢ 0 → m div (suc k * m)
m-div-skm zero m m≢0 rewrite +-identityʳ m = div-refl m m≢0
m-div-skm (suc k) m m≢0 =
    let IH = m-div-skm k m m≢0 in
    div-step (m + k * m) m IH

m-div-km : (k m : ℕ) → m ≢ 0 → k ≢ 0 → m div (k * m)
m-div-km zero m m0 k0 = ⊥-elim (k0 refl)
m-div-km (suc k) m m0 k0 = m-div-skm k m m0
```

```
div-trans : (m n p : ℕ) → m div n → n div p → m div p
div-trans m n p mn np
    with div→alt m n mn | div→alt n p np
... | ⟨ k₁ , eq₁ ⟩ | ⟨ k₂ , eq₂ ⟩
    rewrite sym eq₁ | sym eq₂ | sym (*-assoc k₂ k₁ m) =
    m-div-km (k₂ * k₁) m m-nz (k21≢0 k21m≢0)
    where
    km-nz = div→m≢0 (k₁ * m) ((k₂ * k₁) * m) np

    m-nz : m ≢ 0
    m-nz refl = km-nz (*-zeroʳ k₁) 

    k21m≢0 : k₂ * k₁ * m ≢ 0
    k21m≢0 = div→n≢0 (k₁ * m) (k₂ * k₁ * m) np

    k21≢0 : k₂ * k₁ * m ≢ 0 → k₂ * k₁ ≢ 0
    k21≢0 eq x rewrite x = eq refl 
```

