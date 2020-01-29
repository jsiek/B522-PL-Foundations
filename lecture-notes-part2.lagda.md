```
module lecture-notes-part2 where
```

# Simply Typed Lambda Calculus


## Imports

```
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.List using (List; _∷_; [])
```

## Syntax

The traditional on-paper syntax is

    L,M,N ::= x | λ x. M | L M
            | 0 | suc 0 | case L { zero: M | suc x: N }
            | μ x. M

We'll define terms in Agda as follows.

```
Id : Set
Id = String

infix  5  ƛ_⇒_
infix  5  μ_⇒_
infixl 7  _·_
infix  8  `suc_
infix  9  `_

data Term : Set where
  `_                      :  Id → Term
  ƛ_⇒_                    :  Id → Term → Term
  _·_                     :  Term → Term → Term
  `zero                   :  Term
  `suc_                   :  Term → Term
  case_[zero⇒_|suc_⇒_]    :  Term → Term → Id → Term → Term
  μ_⇒_                    :  Id → Term → Term
```

Example: the addition function defined by recursion. 

```
plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
         case ` "m"
           [zero⇒ ` "n"
           |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]
```

## Church Numerals

```
zeroᶜ : Term
zeroᶜ =  ƛ "s" ⇒ ƛ "z" ⇒ ` "z"

oneᶜ : Term
oneᶜ =  ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · ` "z"

twoᶜ : Term
twoᶜ =  ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

plusᶜ : Term
plusᶜ =  ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
         ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (` "n")
```

Example:

    twoᶜ · sucᶜ · `zero —→ `suc (`suc `zero)


## Bound and Free Variables

Def. A variable occurence x is bound in term M if there is an
enclosing binding for x in M.

Def. A variable occurence x is free in term M if there is not an
enclosing binding for x in M.

Examples:

    λ s. λ z. s (s z)       s and z are bound
    λ z. s (s z)            s is free, z is bound
    s (s z)                 s and z are free
    (λ x. x) x              inner x is bound, outer x is free

Changing the name of a bound variable consistently should not
change the program.

    λ x. x
   
acts the same as
   
    λ y. y

## Values

A value is a term that has no more computation to perform.
In the STLC, that's λ and the natural numbers.

```
data Value : Term → Set where

  V-ƛ : ∀ {x N}
      ---------------
    → Value (ƛ x ⇒ N)

  V-zero :
      -----------
      Value `zero

  V-suc : ∀ {V}
    → Value V
      --------------
    → Value (`suc V)
```

## Function Application by Substitution


Example of two function applications:

      (ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) · sucᶜ · `zero
    —→
      (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
    —→
      sucᶜ · (sucᶜ · `zero)

In general, the β reduction rule explains how function application
works via substitution.

    (λ x. N) M
    —→
    N[x := M]

where `N[x := M]` means replace `x` with `M` inside `N`.


## Hypothetical Problem: Free-Variable Capture

For kicks, let's do the inner application first, of
`(λ y. ...)` to `x`.

      (λ x. (λ y. (λ x. x + y)) x) 1 2
    —→
      (λ x. (λ x. x + x)) 1 2
    —→    
      (λ x. x + x) 2
    —→    
      2 + 2
    —→    
      4

Is that the correct answer?

Would we get the same answer if we did the outer application first?

      (λ x. (λ y. (λ x. x + y)) x) 1 2
    —→
      ((λ y. (λ x. x + y)) 1) 2
    —→
      (λ x. x + 1) 2
    —→
      2 + 1
    —→
      3

No!

Would we get the same answer if we renamed the inner x?

      (λ x. (λ y. (λ z. z + y)) x) 1 2
    —→
      (λ x. (λ y. (λ z. z + y)) x) 1 2
    —→
      (λ x. (λ z. z + x)) 1 2
    —→
      (λ z. z + 1) 2
    —→
      2 + 1
    —→
      3

No!

In the STLC, we'll do outer applications first, which avoids the
problem of free-variable capture.

An alternative solution is to rename bound variables, as we did with
`z` above.


## Substitution

```
infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _          =  V
... | no  _          =  ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _          =  ƛ x ⇒ N
... | no  _          =  ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ]   =  L [ y := V ] · M [ y := V ]
(`zero) [ y := V ]   =  `zero
(`suc M) [ y := V ]  =  `suc M [ y := V ]
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
... | yes _          =  case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no  _          =  case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _          =  μ x ⇒ N
... | no  _          =  μ x ⇒ N [ y := V ]
```

## Reduction

On paper, we would write the reduction rules as follows:

    (λ x. N) V —→ N[x:=V]       (β)

    L —→ L′
    ----------- ξ-·₁
    L M —→ L′ M

    M —→ M′
    ----------- ξ-·₂
    V M —→ V M′

    ...

Here are the rules defined as a relation in Agda.

```
infix 4 _—→_

data _—→_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L′ M}
    → L —→ L′
      -----------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M —→ M′
      -----------------
    → V · M —→ V · M′

  β-ƛ : ∀ {x N V}
    → Value V
      ------------------------------
    → (ƛ x ⇒ N) · V —→ N [ x := V ]

  ξ-suc : ∀ {M M′}
    → M —→ M′
      ------------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {x L L′ M N}
    → L —→ L′
      -----------------------------------------------------------------
    → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]

  β-zero : ∀ {x M N}
      ----------------------------------------
    → case `zero [zero⇒ M |suc x ⇒ N ] —→ M

  β-suc : ∀ {x V M N}
    → Value V
      ---------------------------------------------------
    → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]

  β-μ : ∀ {x M}
      ------------------------------
    → μ x ⇒ M —→ M [ x := μ x ⇒ M ]
```
