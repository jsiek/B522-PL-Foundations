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
open import Relation.Binary.PropositionalEquality using (sym; cong; cong₂)
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
sn+sn≡ss[n+n] : ∀ n → (suc n) + (suc n) ≡ suc (suc (n + n))
sn+sn≡ss[n+n] n rewrite +-comm n (suc n) = refl
```

Here's the definition of `even-dub`.

```
even-dub : (n : ℕ) → Even (n + n)
even-dub zero = even-0
even-dub (suc n) rewrite sn+sn≡ss[n+n] n =
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
mdivn→m≢0 : (m n : ℕ) → m div n → m ≢ 0
mdivn→m≢0 m .m (div-refl .m m≢0) = m≢0
mdivn→m≢0 m .(m + n) (div-step n .m mn) = mdivn→m≢0 m n mn
```

```
mdivn→n≢0 : (m n : ℕ) → m div n → n ≢ 0
mdivn→n≢0 m .m (div-refl .m m≢0) = m≢0
mdivn→n≢0 m .(m + n) (div-step n .m mn) =
  let IH = mdivn→n≢0 m n mn in
  λ mn0 → IH (m+n≡0⇒n≡0 m mn0)
```

An alternative way to state that a number evenly divides another
number is using multiplication instead of repeated addition.  We shall
prove that if `m div n`, then there exists some number `k` such that
`k * m ≡ n`. In Agda, we use a **dependent product type** to express
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
mdivn→k*m≡n : (m n : ℕ) → m div n → Σ[ k ∈ ℕ ] k * m ≡ n
mdivn→k*m≡n m .m (div-refl .m x) = ⟨ 1 , +-identityʳ m ⟩
mdivn→k*m≡n m .(m + n) (div-step n .m mn)
    with mdivn→k*m≡n m n mn
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
  dependent pair returned by `mdivn→k*m≡n`, using the `with` construct.
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
div p`, we have `k₁ * m ≡ n` and `k₂ * n ≡ p` (by `mdivn→k*m≡n`). We can
substitute `k₁ * m` for `n` in the later formula to obtain `k₂ * k₁ *
m ≡ p`, which shows that `m` divides `p` (by `m-div-k*m`).  However,
to use `m-div-k*m` we have two remaining details to prove.
We need to show that `m ≢ 0` and `k₂ * k₁ ≢ 0`.
We obtain `m ≢ 0` using `mdivn→m≢0`.
Similarly, by `mdivn→n≢0` we know `k₂ * k₁ * m ≢ 0`.  Towards a contradiction, if
`k₂ * k₁ ≡ 0`, then we would also have `k₂ * k₁ * m ≡ 0`, but we know
that is false.

```
open import Relation.Binary.PropositionalEquality using (subst)

div-trans : (m n p : ℕ) → m div n → n div p → m div p
div-trans m n p mn np
    with mdivn→k*m≡n m n mn | mdivn→k*m≡n n p np
... | ⟨ k₁ , k₁*m≡n ⟩ | ⟨ k₂ , k₂*k₁*m≡p ⟩
    rewrite sym k₁*m≡n | sym k₂*k₁*m≡p | sym (*-assoc k₂ k₁ m) =
    let m≢0 = (mdivn→m≢0 m (k₁ * m) mn) in
    let k₂*k₁≢0 = (λ k₂*k₁≡0 → mdivn→n≢0 (k₁ * m) (k₂ * k₁ * m) np
         (subst (λ □ → □ * m ≡ 0) (sym k₂*k₁≡0) refl)) in
    m-div-k*m (k₂ * k₁) m m≢0 k₂*k₁≢0
```

Equality
--------

Review:

* `≡` is an equivalence relation: `refl`, `sym`, `trans`
* `cong`

```
open import Relation.Binary.PropositionalEquality using (refl; sym; trans)
```

Example of `refl`:

```
0≡0+0 : 0 ≡ 0 + 0
0≡0+0 = refl
```

Example of `sym`:

```
0+0≡0 : 0 + 0 ≡ 0
0+0≡0 = sym 0≡0+0
```

Example of `cong`:

```
0+0≡0+0+0 : 0 + 0 ≡ 0 + (0 + 0)
0+0≡0+0+0 = cong (λ □ → 0 + □) 0≡0+0
```

Example of `trans`:

```
0≡0+0+0 : 0 ≡ 0 + 0 + 0
0≡0+0+0 = trans 0≡0+0 0+0≡0+0+0
```

* `subst`

  Example:

```
open import Relation.Binary.PropositionalEquality using (subst)

even-dub' : (n m : ℕ) → m + m ≡ n → Even n
even-dub' n m eq = subst (λ □ → Even □) eq (even-dub m)
```

* Chains of equations

```
_ : 0 ≡ 0 + 0 + 0
_ =
  begin
  0            ≡⟨ 0≡0+0 ⟩
  0 + 0        ≡⟨ 0+0≡0+0+0 ⟩
  0 + 0 + 0
  ∎
```

* Rewriting

  Revisiting the proof of `even-dub'`, using `rewrite`
  instead of `subst`.

```
even-dub'' : (n m : ℕ) → m + m ≡ n → Even n
even-dub'' n m eq rewrite (sym eq) = even-dub m
```

Isomorphism
-----------

Two types `A` and `B` are *isomorphic* if there exist a pair of
functions that map back and forth between the two types, and doing a
round trip starting from either `A` or `B` brings you back to where
you started, that is, composing the two functions in either order is
the identity function.

```
infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
```

Example: products are commutative upto isomorphism.

```
open import Data.Product using (_×_)

×-comm : ∀{A B : Set} → A × B ≃ B × A
×-comm =
  record {
    to = λ { ⟨ x , y ⟩ → ⟨ y , x ⟩ } ;
    from = λ { ⟨ x , y ⟩ → ⟨ y , x ⟩ } ;
    from∘to = λ { ⟨ x , y ⟩ → refl }  ;
    to∘from = λ { ⟨ x , y ⟩ → refl } }
```

Example: ℕ is isomorphic to the even numbers.

Here is another definition of the even numbers.
It's also helpful to define the odd numbers.

```
data IsEven : ℕ → Set
data IsOdd : ℕ → Set

data IsEven where
  is-even : ∀ n m → n ≡ m + m → IsEven n

data IsOdd where
  is-odd : ∀ n m → n ≡ suc (m + m) → IsOdd n
```

We define the type `Evens` as a wrapper around the even numbers. We
mark the proof of `IsEven n` as *irrelevant*, with a period, so that
the equality of two Evens does not require the two proofs of `IsEven`
to be equal.

```
data Evens : Set where
  even : (n : ℕ) → .(IsEven n) → Evens
```

To form the isomorphim, we define the following two functions for
converting a number to an even one, by multiplying by two, and for
converting back, by dividing by two (rounding down).

```
to-evens : ℕ → Evens
to-evens n = even (n + n) (is-even (n + n) n refl)

from-evens : Evens → ℕ
from-evens (even n even-n) = ⌊ n /2⌋

```
We shall first prove that `from ∘ to` is the identity.
The following equation is helpful in proving that fact.

```
⌊n+n/2⌋≡n : ∀ (n : ℕ) → ⌊ n + n /2⌋ ≡ n
⌊n+n/2⌋≡n zero = refl
⌊n+n/2⌋≡n (suc n) =
  let IH = ⌊n+n/2⌋≡n n in
  begin
  ⌊ suc (n + suc n) /2⌋        ≡⟨ cong ⌊_/2⌋ (sn+sn≡ss[n+n] n) ⟩
  ⌊ suc (suc (n + n)) /2⌋      ≡⟨ refl ⟩
  suc ⌊ n + n /2⌋              ≡⟨ cong suc IH ⟩
  suc n
  ∎
```

Now we prove that `from ∘ to` is the identity, by induction on `n`.

```
from∘to-evens : ∀ (n : ℕ) → from-evens (to-evens n) ≡ n
from∘to-evens zero = refl
from∘to-evens (suc n) =
  begin
  from-evens (to-evens (suc n))                ≡⟨ refl ⟩
  from-evens (even ((suc n) + (suc n)) P)      ≡⟨ refl ⟩
  ⌊ (suc n) + (suc n) /2⌋                      ≡⟨ ⌊n+n/2⌋≡n (suc n) ⟩
  suc n
  ∎
  where P = is-even ((suc n) + (suc n)) (suc n) refl
```

The other direction, proving that `to ∘ from` is the identity, is more difficult.
We shall need the following equation

```
⌊n/2⌋+⌊n/2⌋≡n : ∀ n → (IsEven n) → ⌊ n /2⌋ + ⌊ n /2⌋ ≡ n
⌊n/2⌋+⌊n/2⌋≡n n (is-even .n m refl) rewrite ⌊n+n/2⌋≡n m = refl
```

However, in the context where we need it, we know that `n` is even but
only in a proof irrelevant way. So we need a way to convert a proof
irrelevant `IsEven n` to a proof relevant one. One of the few ways
that we are allowed to use a proof irrelevant fact is in proving a
contradiction. So let us assume `IsEven n` (irrelevantly).  Then we
prove that every number is either even or odd (relevantly), and that
even and odd are mutually exclusive.  In case the number is even, we
have our relevant evidence that is is even. In case the number is odd,
then we know is not even, and we have a contradiction with the
irrelevant fact that it is even. In general, whenever you have a
decidable predicate, you can convert from knowing it irrelevantly to
knowing it relevantly using this recipe.

We start by proving that every number `n` is either even or odd, by
induction on `n`.

```
open import Data.Sum

even⊎odd : ∀ (n : ℕ) → IsEven n ⊎ IsOdd n
even⊎odd zero = inj₁ (is-even 0 0 refl)
even⊎odd (suc n)
    with even⊎odd n
... | inj₁ (is-even n m refl) =
      inj₂ (is-odd (suc (m + m)) m refl)
... | inj₂ (is-odd n m refl) =
      inj₁ (is-even (suc (suc (m + m))) (suc m) (sym (sn+sn≡ss[n+n] m)))
```

Not only is every number either even or odd, but those two properties
are mutually exclusive. In the following we prove that if a number is
odd, it is not even. To do this we need the following fact, which we
prove by induction on both `n` and `m`.

```
2*n≢1+2*m : ∀ (n m : ℕ) → n + n ≢ suc (m + m)
2*n≢1+2*m (suc n) zero eq rewrite +-comm n (suc n)
    with eq
... | ()
2*n≢1+2*m (suc n) (suc m) eq rewrite +-comm n (suc n) | +-comm m (suc m) =
    let IH = 2*n≢1+2*m n m in
    IH (suc-injective (suc-injective eq))

open import Relation.Nullary using (¬_)

IsOdd→¬IsEven : ∀ n → IsOdd n → ¬ IsEven n
IsOdd→¬IsEven n (is-odd .n m refl) (is-even .n m₁ eq) = 2*n≢1+2*m m₁ m (sym eq)
```

Now we can convert an irrelevant `IsEven n` to a relevant one.

```
import Data.Empty.Irrelevant

IsEven-irrelevant→IsEven : ∀ n → .(IsEven n) → IsEven n
IsEven-irrelevant→IsEven n even-n 
    with even⊎odd n
... | inj₁ even-n' = even-n'
... | inj₂ odd-n = Data.Empty.Irrelevant.⊥-elim (IsOdd→¬IsEven n odd-n even-n)
```

To show that two `Evens` are equal, it suffices to show that the
underlying numbers are equal (because the proofs of `IsEven` are
irrelevant).

```
Evens≡ : ∀{x y : ℕ} .{p : IsEven x} .{q : IsEven y}
       → x ≡ y
       → (even x p) ≡ (even y q)
Evens≡ {x} {y} {p} {q} refl = refl  
```

Now we can prove that `to ∘ from` is the identity.

```
to∘from-evens : ∀ (e : Evens) → to-evens (from-evens e) ≡ e
to∘from-evens (even n even-n) = Evens≡ (⌊n/2⌋+⌊n/2⌋≡n n even-n-rlvnt)
  where even-n-rlvnt = IsEven-irrelevant→IsEven n even-n
```

Putting all these pieces together, we have that ℕ is isomorphic to
`Evens`, which is rather odd because ℕ contains numbers that are not
even. Yeah infinity!

```
ℕ≃Evens : ℕ ≃ Evens
ℕ≃Evens =
  record {
    to = to-evens ;
    from = from-evens ;
    from∘to = from∘to-evens ;
    to∘from = to∘from-evens }
```


Connectives
-----------

Propositions as Types:

* conjunction is product,
* disjunction is sum,
* true is unit type,
* false is empty type,
* implication is function type.

```
postulate P Q R S : Set
```

Conjunction:

```
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

_ : P × Q → Q × P
_ = λ pq → ⟨ proj₂ pq , proj₁ pq ⟩
```

Disjunction:

```
open import Data.Sum using (_⊎_; inj₁; inj₂)

_ : P ⊎ Q → Q ⊎ P
_ = λ { (inj₁ p) → (inj₂ p);
        (inj₂ q) → (inj₁ q)}
```

True:

```
open import Data.Unit using (⊤; tt)

_ : ⊤
_ = tt

_ : (⊤ → P) → P
_ = λ ⊤→P → ⊤→P tt
```

False:

```
open import Data.Empty using (⊥; ⊥-elim)

0≢1+n : ∀ {n} → 0 ≢ suc n
0≢1+n ()

_ : 0 ≡ 1 → P
_ = λ 0≡1 → ⊥-elim (0≢1+n 0≡1)
```

Implication:

```
_ : (P → Q) × (R → Q) → ((P ⊎ R) → Q)
_ = λ pq-rq → λ{ (inj₁ p) → (proj₁ pq-rq) p ;
                 (inj₂ r) → (proj₂ pq-rq) r }
```

alternatively, using function definitions and pattern matching

```
f : (P → Q) × (R → Q) → ((P ⊎ R) → Q)
f ⟨ pq , rq ⟩ (inj₁ p) = pq p
f ⟨ pq , rq ⟩ (inj₂ r) = rq r
```

Negation:

Negation is shorthand for "implies false".

```
_ : (¬ P) ≡ (P → ⊥)
_ = refl
```


Quantifiers
-----------

As we have seen, universal quantification (for all) is represented
using dependent function types.

```
_ : ∀{P : Set}{Q R : P → Set} →
     (∀ (x : P) → Q x) ⊎ (∀ (x : P) → R x)
  →  ∀ (x : P) → Q x ⊎ R x
_ = λ { (inj₁ ∀x,qx) p → inj₁ (∀x,qx p);
        (inj₂ ∀x,rx) p → inj₂ (∀x,rx p) }
```

Existential quantification is represented using dependent product types.
Recall that in a dependent product type, the type of the second part
can refer to the first part.

Normal product type:

   A × B

Dependent product type:

  Σ[ x ∈ A ] B x

The values of dependent product types are good old pairs: `⟨ v₁ , v₂ ⟩`,
where `v₁ : A` and `v₂ : B v₁`.

The following example implements a disjoint union `A or B` using a
dependent pair.  The first part is a tag, false or true, that says
whether the payload (the second part) has type `A` or `B`,
respectively.

```
open import Data.Bool using (Bool; true; false)

select : (A : Set) → (B : Set) → Bool → Set
select A B false = A
select A B true = B

_or_ : Set → Set → Set
A or B = Σ[ flag ∈ Bool ] select A B flag

forty-two : ℕ or (ℕ → ℕ)
forty-two = ⟨ false , 42 ⟩

inc : ℕ or (ℕ → ℕ)
inc = ⟨ true , suc ⟩

inject₁ : ∀{A B : Set} → A → A or B
inject₁ a = ⟨ false , a ⟩

inject₂ : ∀{A B : Set} → B → A or B
inject₂ b = ⟨ true , b ⟩

case : ∀{A B C : Set} → A or B → (A → C) → (B → C) → C
case ⟨ false , a ⟩ ac bc = ac a
case ⟨ true , b ⟩ ac bc = bc b
```

```
_ : 42 ≡ case forty-two (λ n → n) (λ f → f 0)
_ = refl

_ : 1 ≡ case inc (λ n → n) (λ f → f 0)
_ = refl
```

Example proofs about existentials:

```
∀∃-currying1 : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ (x : A) → B x → C)
  → (Σ[ x ∈ A ] B x) → C
∀∃-currying1 f ⟨ x , y ⟩ = f x y

∀∃-currying2 : ∀ {A : Set} {B : A → Set} {C : Set}
  → ((Σ[ x ∈ A ] B x) → C)
  → (∀ (x : A) → B x → C)
∀∃-currying2 g x y = g ⟨ x , y ⟩
``` 

Decidable
---------

An alternative way to represent a relation is Agda is with the
relations characteristic function. That is, a function that takes the
two elements and returns true or false, depending on whether the
elements are in the relation.

```
less-eq : ℕ → ℕ → Bool
less-eq zero n = true
less-eq (suc m) zero = false
less-eq (suc m) (suc n) = less-eq m n
```

In some sense, such a function is better than going with a data type
because it also serves as a decision procedure. However, for some
relations it is difficult or even impossible to come up with such a
function.

Sometimes its nice to link your decision procedure to the relation
defined by a data type, building the correctness of your decision
procedure into its type. The `Dec` type let's you do this.

```
open import Relation.Nullary using (Dec; yes; no)
open import Data.Nat using (_≤_)

less-eq? : (m n : ℕ) → Dec (m ≤ n)
less-eq? zero n = yes z≤n
less-eq? (suc m) zero = no (λ ())
less-eq? (suc m) (suc n)
    with less-eq? m n
... | yes m≤n = yes (s≤s m≤n)
... | no ¬m≤n = no λ sm≤sn → ¬m≤n (≤-pred sm≤sn)
```

