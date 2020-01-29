```
module lecture-notes-part1 where
```

# Naturals

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

## Proofs about all the naturals numbers

To prove something about all the natural numbers,
such as 

    x + y + x ≡ 2 * x + y

for all x and y, your plan A should be to try and prove
it using the laws of algebra, which are provided in the Agda
standard library.

```
open import Data.Nat.Properties
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
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


# Induction

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


# Predicates, Inductively Defined

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

```
even-dub : (n : ℕ) → Even (n + n)
even-dub zero = even-0
even-dub (suc n) rewrite +-comm n (suc n) =
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


# Relations, Inductively Defined

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

A common property of relations is transitivity.  Indeed, the `div`
relation is transitive. To prove this we need the following standard
fact about divides and addition.

```
div-+ : ∀ l m n → l div m → l div n → l div (m + n)
div-+ l .l n (div-refl .l l≢0) ln = div-step n l ln
div-+ l .(l + m) n (div-step m .l lm) ln
   rewrite +-assoc l m n =
   let IH = div-+ l m n lm ln in
   div-step (m + n) l IH
```
* In the case for `div-refl`, we have `m ≡ l` so we need to
  prove that `l div (l + n)`, which we do directly with `div-step`.

* In the case for `div-step`, we need to prove that `l div ((l + m) + n)`,
  which we re-associate to `l div (l + (m + n))`.
  The induction hypothesis gives us `l div (m + n)`,
  so we conclude by applying `div-step`.

We prove that `div` is transitive by induction on the derivation
of `m div n`.

```
div-trans : ∀ l m n → l div m → m div n → l div n
div-trans l m .m lm (div-refl .m m≢0) = lm
div-trans l m .(m + n) lm (div-step n .m mn) =
  let IH:ln = div-trans l m n lm mn in
  div-+ l m n lm IH:ln
```
* In the case for `div-refl`, we have `n ≡ m`
  so we need to prove `l div m`, which we already know.

* In the case for `div-step`, we need to prove
  that `l div (m + n)`
  and the induction hypothesis for `m div n` gives us
  `l div n`. So using this with the assumption that
  `l div m`, we apply `div-+` to conclude that
  `l div (m + n)`.


# Equality

`≡` is just a relation defined as a data type, as in the above examples.

It has one constructor named `refl` that says anything is equal to
itself.

## `≡` is an equivalence relation and a congruence

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

## `subst`

  Example:

```
open import Relation.Binary.PropositionalEquality using (subst)

even-dub' : (n m : ℕ) → m + m ≡ n → Even n
even-dub' n m eq = subst (λ □ → Even □) eq (even-dub m)
```

## Chains of equations

```
_ : 0 ≡ 0 + 0 + 0
_ =
  begin
  0            ≡⟨ 0≡0+0 ⟩
  0 + 0        ≡⟨ 0+0≡0+0+0 ⟩
  0 + 0 + 0
  ∎
```

## Rewriting

  Revisiting the proof of `even-dub'`, using `rewrite`
  instead of `subst`.

```
even-dub'' : (n m : ℕ) → m + m ≡ n → Even n
even-dub'' n m eq rewrite (sym eq) = even-dub m
```


# Isomorphism

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

## Example: products are commutative upto isomorphism.

(Note that we're using implicit parameters for the first time.)

```
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

×-comm : ∀{A B : Set} → A × B ≃ B × A
×-comm =
  record {
    to = λ { ⟨ x , y ⟩ → ⟨ y , x ⟩ } ;
    from = λ { ⟨ x , y ⟩ → ⟨ y , x ⟩ } ;
    from∘to = λ { ⟨ x , y ⟩ → refl }  ;
    to∘from = λ { ⟨ x , y ⟩ → refl } }
```

## Example: `((A → B) × (A → B) ≃ ((A × Bool) → B))`

Two functions can always be merged into a single function
with an extra Boolean parameter. The proof of this isomorphism
requires the principle of extensionality.

```
open import Data.Bool using (Bool; true; false)

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
```

## Example: ℕ is isomorphic to the even numbers.

Here is another definition of the even numbers.

```
data IsEven : ℕ → Set where
  is-even : ∀ n m → n ≡ m + m → IsEven n
```

We define the type `Evens` as a wrapper around the even numbers
that combines the number with a proof that it is even.

```
data Evens : Set where
  even : (n : ℕ) → (IsEven n) → Evens
```

We convert from natural numbers to evens by multiplying by 2.  Going
the other way, it is tempting to divide by 2 using the operator
`⌊_/2⌋`. However, a simpler approach is to recognize that a value of
`Evens` carries with it a witness `m` that is half of `n`, so we can
just return `m`.

```
ℕ≃Evens : ℕ ≃ Evens
ℕ≃Evens =
  record {
    to = λ n → even (n + n) (is-even (n + n) n refl) ;
    from = λ { (even n (is-even n m refl)) → m } ;
    from∘to = λ x → refl ;
    to∘from = λ { (even n (is-even n m refl)) → refl } }
```

# Connectives

Propositions as Types:

* true is unit type,
* implication is function type.
* conjunction is product (i.e. pair),
* disjunction is sum (i.e. disjoint union),
* false is empty type,

In this setting, a proposition is true if the corresponding type is
inhabited. So we can prove that a proposition is true by constructing
an inhabitant of the corresponding type.

For purposes of discussion, we'll use the letters `P`, `Q`, `R`, and `S`
for arbitrary propositions.

```
variable P Q R S : Set
```

## True

True is the unit type, written `⊤`.

It has one constructor `tt` that has no parameters,
so it is trivial to prove `⊤`.

```
open import Data.Unit using (⊤; tt)

_ : ⊤
_ = tt
```

## Implication

Implication is the function type.

So its constructor is lambda abstraction
and the eliminator is application.

```
_ : P → P
_ = λ p → p
```

Any proposition `P` is isomorphic to `⊤ → P`.

```
_ : (⊤ → P) → P
_ = λ f → f tt

_ : P → (⊤ → P)
_ = λ p → λ tt → p
```

## Conjunction

Logical "and" is the pair type, written `P × Q`.

It has one constructor `⟨_,_⟩` that takes two arguments,
one for `P` and the other for `Q`.

It has two eliminators (accessors) `proj₁` and `proj₂`,
that return the proofs of `P` and of `Q`, respectively.

```
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

_ : P × Q → Q × P
_ = λ pq → ⟨ proj₂ pq , proj₁ pq ⟩
```

## Disjunction

Logical "or" is the disjoint union type, written `P ⊎ Q`.

It has two constructors, `inl` and `inr` that take one parameter.

Elimination is by pattern matching.

```
open import Data.Sum using (_⊎_; inj₁; inj₂)

_ : P ⊎ Q → Q ⊎ P
_ = λ { (inj₁ p) → (inj₂ p);
        (inj₂ q) → (inj₁ q)}

_ : (P → Q) × (R → Q) → ((P ⊎ R) → Q)
_ = λ pq,rq → λ{ (inj₁ p) → (proj₁ pq,rq) p ;
                 (inj₂ r) → (proj₂ pq,rq) r }
```

Alternatively, one can use top-level function definitions and pattern
matching:

```
f : (P → Q) × (R → Q) → ((P ⊎ R) → Q)
f ⟨ pq , rq ⟩ (inj₁ p) = pq p
f ⟨ pq , rq ⟩ (inj₂ r) = rq r
```

## False

False is the empty type, written `⊥`.

It has no constructors. However, it can appears as the return type of
a function whose input is absurd, as in the following example.

```
open import Data.Empty using (⊥)

0≡1→⊥ : 0 ≡ 1 → ⊥
0≡1→⊥ = λ ()
```

False has one eliminator, `⊥-elim`, which has type `∀{P} → ⊥ → P`.
So one can prove anything from false.

```
open import Data.Empty using (⊥-elim)

_ : 0 ≡ 1 → P
_ = λ 0≡1 → ⊥-elim (0≡1→⊥ 0≡1)
```

## Negation

Negation is shorthand for "implies false".
Thus, one can prove false from a contradiction.

```
open import Relation.Nullary using (¬_)

_ : (¬ P) ≡ (P → ⊥)
_ = refl

_ : P → (¬ P) → ⊥
_ = λ p ¬p → ¬p p
```


# Quantifiers

As we have seen, universal quantification (for all) is represented
using dependent function types.

You use (eliminate) a dependent function simply by applying it to an
argument.

```
postulate Human : Set
postulate Mortal : Human → Set
postulate Socrates : Human
postulate all-Humans-mortal : (p : Human) → Mortal p
postulate all-Humans-mortal' : ∀ p → Mortal p               -- equivalent
postulate all-Humans-mortal'' : ∀ (p : Human) → Mortal p    -- equivalent

_ : Mortal Socrates
_ = all-Humans-mortal Socrates
```

You prove a universally quantifies formula by writing a function of
the appropriate type.

```
*-0ʳ : ∀ n → n * 0 ≡ 0
*-0ʳ n rewrite *-comm n 0 = refl
```

The following shows how universals can distribute with disjunction.

```
_ : ∀{P : Set}{Q R : P → Set}
    → (∀ (x : P) → Q x)  ⊎  (∀ (x : P) → R x)
    → ∀ (x : P) → Q x ⊎ R x
_ = λ { (inj₁ ∀x:P,Qx) p → inj₁ (∀x:P,Qx p);
        (inj₂ ∀x:P,Rx) p → inj₂ (∀x:P,Rx p) }
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

∃ x. P x

Σ[ x ∈ ℕ ] P x

To express "there exists", the witness of the existential is the first
part of the pair. The type of the second part of the pair is some
formula involving the first part, and the value in the second part of
the pair is a proof of that formula.

```
open import Data.Product using (Σ-syntax)
```

The following example implements a disjoint union type `A or B` using
a dependent pair.  The first part is a tag, false or true, that says
whether the payload (the second part) has type `A` or type `B`,
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

Example proofs about existentials and universals:

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

Example use of existentials for even numbers:

An alternative way to state that a number evenly divides another
number is using multiplication instead of repeated addition.  We shall
prove that if `m div n`, then there exists some number `k` such that
`k * m ≡ n`.  To express "there exists some number `k` such that `k *
m ≡ n`", we use the dependent produce type

    Σ[ k ∈ ℕ ] k * m ≡ n

where `k` is a name for the first part of the pair,
`ℕ` is it's type, and `k * m ≡ n` is the type
for the second part of the pair.
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


Decidable
---------

An alternative way to represent a relation is Agda is with the
relation's characteristic function. That is, a function that takes the
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
procedure into its type. The `Dec` type let's you do this by including
both the true/false regarding whether the relation holds for the input
but also the proof that it holds or that its negation holds.

```
open import Relation.Nullary using (Dec; yes; no)
open import Data.Nat using (_≤_)

less-eq? : (m n : ℕ) → Dec (m ≤ n)
less-eq? zero n = yes z≤n
less-eq? (suc m) zero = no (λ ())
less-eq? (suc m) (suc n)
    with less-eq? m n
... | yes m≤n = yes (s≤s m≤n)
... | no m≰n = no λ { (s≤s m≤n) →  m≰n m≤n }
```


Lists
-----

Agda provides Lisp-style lists, with nil and cons, spelled `[]` and `_∷_`.
For example:

```
open import Data.List using (List; []; _∷_; map; unzip)

_ : List ℕ
_ = 1 ∷ 2 ∷ []
```

Agda provides lots of standard functions on lists, such as append
(`_++_`), `map`, `foldr`, `foldl`, `zip`, `unzip`, `reverse`,
`splitAt`, and many more. The Agda standard library also provides many
theorems about these functions.  We shall study some examples that use
some of these functions and theorems.

Consider the operation that rotates the elements of a list to the left
by `k` positions, with wrap-around. For example,

    rotate (1 ∷ 2 ∷ 3 ∷ []) 2 ≡ (3 ∷ 1 ∷ 2 ∷ [])

One clever way to rotate a list is to split it into two parts, reverse
each part, append them, and then reverse again.

```
open import Data.List using (reverse; splitAt; _++_)

rotate : ∀ {A : Set} → List A → ℕ → List A
rotate xs k
    with splitAt k xs
... | ⟨ ls , rs ⟩ =
    let ls' = reverse ls in
    let rs' = reverse rs in
    reverse (ls' ++ rs')
```

Here are a few examples of `rotate` in action.

```
_ : rotate (1 ∷ 2 ∷ 3 ∷ []) 1 ≡ (2 ∷ 3 ∷ 1 ∷ [])
_ = refl

_ : rotate (1 ∷ 2 ∷ 3 ∷ []) 2 ≡ (3 ∷ 1 ∷ 2 ∷ [])
_ = refl

_ : rotate (1 ∷ 2 ∷ 3 ∷ []) 3 ≡ (1 ∷ 2 ∷ 3 ∷ [])
_ = refl
```

One way to think about `rotate` is in terms of swapping the part of
the list at the front with the rest of the list at the back. In the
following, the first three elements, `a , b , c`, are moved to the
back, swapping places with the `d , e`.

    rotate ([ a , b , c ] ++ [ d , e ]) 3
          ≡ [ d , e ] ++ [ a , b , c ]

With this view in mind, we prove that `rotate` is correct using some
equations from the Agda standard library about `reverse` and `append`.

```
open import Data.List.Properties using (reverse-++-commute; reverse-involutive)

rotate-correct : ∀ {A : Set} {xs ys zs : List A} {k : ℕ}
   → splitAt k xs ≡ ⟨ ys , zs ⟩
   → rotate xs k ≡ zs ++ ys
rotate-correct {A}{xs}{ys}{zs} sk rewrite sk =
  begin
     reverse (reverse ys ++ reverse zs)   ≡⟨ cong reverse (sym (reverse-++-commute zs ys)) ⟩
     reverse (reverse (zs ++ ys))         ≡⟨ reverse-involutive (zs ++ ys) ⟩
     zs ++ ys
  ∎
```

Next consider a simplified version of the `map-compose` theorem from
the standard library. It says that mapping functions `f` then `g` over
a list is equivalent to mapping the composition `g ∘ f` over the list.

```
open import Function using (_∘_)

map-compose : ∀{A B C : Set}{g : B → C} {f : A → B}
              → (xs : List A)
              → map (g ∘ f) xs ≡ map g (map f xs)
map-compose []       = refl
map-compose (x ∷ xs) = cong (_ ∷_) (map-compose xs)
```

There are many more operations and theorems in the works of Richard
Bird concerning the interactions between lists, functions, pairs, and
sums. In the following we will introduce a couple of these operations
and prove some theorems about them.  To begin, we define the fork (`▵`)
and cross (`⊗`) functions.

```
_▵_ : ∀{A B C : Set} → (A → B) → (A → C) → A → B × C
(f ▵ g) a = ⟨ (f a) , (g a) ⟩

_⊗_ : ∀{A B C D : Set} → (A → B) → (C → D) → A × C → B × D
(f ⊗ g) ⟨ a , c ⟩ = ⟨ f a , g c ⟩
```

Recall that `unzip` converts a list of pairs `xs` into a pair of
lists.  One way to implement `unzip` is to 1) `map` the `proj₁`
function over `xs`, 2) `map` the `proj₂` over `xs` and 3) pair the two
resulting lists. This can be expressed using fork in the following
way.

```
unzip-slow : {A B : Set} → List (A × B) → List A × List B
unzip-slow xs = ((map proj₁) ▵ (map proj₂)) xs
```

This implementation of `unzip` is obviously correct but not very
efficient because it makes two passes over the list of pairs. The real
implementation is more clever and makes only a single pass over the
list of pairs, as shown below. (The `unzip` in the Agda standard
library is equivalent to the following `unzip-fast`, but it is
implemented in terms of a more general function named `unzipWith`.)

```
unzip-fast : {A B : Set} → List (A × B) → List A × List B
unzip-fast [] = ⟨ [] , [] ⟩
unzip-fast (⟨ a , b ⟩ ∷ xs) =
  let ⟨ as , bs ⟩ = unzip-fast xs in
  ⟨ a ∷ as , b ∷ bs ⟩
```

The fast and slow versions of `unzip` are equivalent, which is
straightforward to prove by induction on the input list `xs`.

```
unzip≡▵map : ∀{A B : Set}
           → (xs : List (A × B))
           → unzip xs ≡ ((map proj₁) ▵ (map proj₂)) xs
unzip≡▵map {A} {B} [] =  begin
  unzip []                    ≡⟨⟩
  ⟨ [] , [] ⟩                 ≡⟨⟩
  (map proj₁ ▵ map proj₂) []  ∎
unzip≡▵map {A} {B} (⟨ a , b ⟩ ∷ xs) =              begin
  unzip (⟨ a , b ⟩ ∷ xs)                           ≡⟨⟩
  ⟨ a ∷ proj₁ (unzip xs) , b ∷ proj₂ (unzip xs) ⟩  ≡⟨ cong₂ ⟨_,_⟩ IH1 IH2 ⟩
  ⟨ a ∷ map proj₁ xs , b ∷ map proj₂ xs ⟩          ≡⟨⟩
  (map proj₁ ▵ map proj₂) (⟨ a , b ⟩ ∷ xs)
  ∎
  where
  IH = unzip≡▵map xs
  IH1 = cong (λ □ → a ∷ (proj₁ □)) IH
  IH2 = cong (λ □ → b ∷ (proj₂ □)) IH
```

The cross of `map f` and `map g` commutes with `unzip` in the
following sense, which we prove with a direct equational proof.
(No induction needed.)

```
⊗-distrib-unzip : ∀{A B C D} {f : A → B} {g : C → D}
    → (xs : List (A × C))
    → (map f ⊗ map g) (unzip xs) ≡ unzip (map (f ⊗ g) xs)
⊗-distrib-unzip {A}{B}{C}{D}{f}{g} xs =                        begin
  (map f ⊗ map g) (unzip xs)                                   ≡⟨ cong (map f ⊗ map g) (unzip≡▵map xs) ⟩
  (map f ⊗ map g) (((map proj₁) ▵ (map proj₂)) xs)             ≡⟨⟩
  ⟨ (map f ∘ map proj₁) xs , (map g ∘ map proj₂) xs ⟩          ≡⟨ cong₂ ⟨_,_⟩ (sym (map-compose xs)) (sym (map-compose xs)) ⟩
  ⟨ map (f ∘ proj₁) xs , map (g ∘ proj₂) xs ⟩                  ≡⟨⟩
  ⟨ map (proj₁ ∘ (f ⊗ g)) xs , map (proj₂ ∘ (f ⊗ g)) xs ⟩      ≡⟨ cong₂ ⟨_,_⟩ (map-compose xs) (map-compose xs) ⟩ 
  ⟨ map proj₁ (map (f ⊗ g) xs) , map proj₂ (map (f ⊗ g) xs) ⟩  ≡⟨⟩ 
  (map proj₁ ▵ map proj₂) (map (f ⊗ g) xs)                     ≡⟨ sym (unzip≡▵map (map (f ⊗ g) xs)) ⟩ 
  unzip (map (f ⊗ g) xs)                                       ∎
```
The above proof proceeds as follows.
1. Apply `unzip≡▵map` to replace `unzip` with a fork and two maps.
2. To get `xs` next to the maps, we unfold the definition of fork .
3. To fuse `f` and `proj₁` on the  left and `g` and `proj₂` on the right,
   we apply `map-compose` in reverse.
4. Use the definition of cross to change `f ∘ proj₁` into
   `proj₁ ∘ (f ⊗ g)`, and similarly for `g ∘ proj₂`.
5. Apply `map-compose`, separating `proj₁` from `f ⊗ g` on the
   left and `proj₂` from `f ⊗ g` on the right.
6. Apply `unzip≡▵map` a second time, in reverse,
   to replace the fork and two maps with `unzip`.

