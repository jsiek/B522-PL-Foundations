## Imports

```
open import Agda.Primitive using (lzero)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; z≤n; s≤s; _<?_){- ; _≤′_; ≤′-refl; ≤′-step; _<′_)-}
open import Data.Nat.Properties
  using (m≤m+n; m≤n+m; ≤-step; ≤-pred; n≤1+n; 1+n≰n; ≤-refl; +-comm; +-assoc;
         +-mono-≤; ≤-reflexive; ≤∧≢⇒<) {-≤⇒≤′; ≤′⇒≤; ≤-trans)-}
open Data.Nat.Properties.≤-Reasoning
  using (_≤⟨_⟩_)
  renaming (begin_ to begin≤_; _∎ to _QED)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
   renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
   using (_≡_; _≢_; refl; sym; inspect; [_]; cong; cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning
   using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import FiniteSet

module Unification
    (Op : Set)
    (op-eq? : (x : Op) → (y : Op) → Dec (x ≡ y))
    (arity : Op → ℕ) where

open import FirstOrderTerms Op op-eq? arity
```

## Introduction to Unification

This chapter lays the groundwork for the chapter on unification-based
type inference ([TypeInference](./TypeInference.lagda.md)).  Type
inference produces equations over types, such as

    α = β ⇒ Nat
    Bool = β

where the α and β are _unknown type variables_ that need to be
solved. For the example, a solution to the above equations is

    α = Bool ⇒ Nat
    β = Bool

From a syntactic point of view, types are an instance of a more
general construction known as _first-order terms_, which are
recursively defined to include variables, and function symbols applied
to zero or more first-order terms.
The module [FirstOrderTerms](./FirstOrderTerms.lagda.md)
defines first-order terms, substitution, and properties about them.
The module also defines a predicate `IdemSubst` for _idempotent substitutions_
which are substitutions σ such that

    subst σ (sust σ M) ≡ subst σ M

The `IdemSubst` predicate does not directly state this property, but
instead places restrictions on the form of a substitution to make sure
it is idempotent. We make use of `IdemSubst` in several of the proofs
in this chapter.

Equations over first-order terms can be solved using _unification_. In
this chapter we study a particularly lucid unification algorithm by
Martelli and Montanari (TOPLAS 1982).

We represent an equation as a pair of terms, and a set of equations as
a list of pairs of terms. We introduce the notation `L ≐ M` for
an equation between two terms.

```
Equations : Set
Equations = List (Term × Term)

infix 4 _≐_
pattern _≐_ L M = ⟨ L , M ⟩
```

We use the following helper function for adding a bunch of new equations.

```
private
  append-eqs : ∀{n} → Vec Term n → Vec Term n → Equations → Equations
  append-eqs {zero} Ms Ls eqs = eqs
  append-eqs {suc n} (M ∷ Ms) (L ∷ Ls) eqs = (M ≐ L) ∷ append-eqs Ms Ls eqs
```

The goal of a unification algorithm is to find a substitution σ that,
when applied to both sides of each equation, makes the two sides
syntacticaly equal. In such a case we say that the substitution σ
_unifies_ the equations.

```
_unifies_ : Equations → Equations → Set
σ unifies [] = ⊤
σ unifies ((L ≐ M) ∷ eqs) = (subst σ L ≡ subst σ M)  ×  σ unifies eqs
```

The unification algorithm of Martelli and Montanari considers one
equation at a time from the list of equations `eqs` and performs one
of the following actions. In the process, the algorithm accumulates
the solution, a substitution σ.

1. Remove trivial equations:

        (` x ≐ ` x) ∷ eqs , σ    becomes    eqs , σ

2. Eliminate a variable via substitution:

        (` x ≐ M) ∷ eqs , σ    becomes    [ M / x] eqs , (` x ≐ M) ∷ [ M / x] σ
    
   and
   
        (M ≐ ` x) ∷ eqs , σ    becomes    [ M / x] eqs , (` x ≐ M) ∷ [ M / x] σ

   provided that `x ∉ vars M` (this is known as the _occurs check_).
   Otherwise report that there are no solutions.

3. Decompose an equality on function symbols

        (f ⦅ M₁ ... Mᵤ ⦆ ≐ f' ⦅ L₁ ... Lᵤ ⦆) ∷ eqs , σ    becomes    (M₁ ≐ L₁) ∷ ... ∷ (Mᵤ ≐ Lᵤ) ∷ eqs , σ

   provided that `f ≡ f'`. Otherwise report that there are no solutions.


The rest of this Chapter defines a `unify` function that implements
the algorithm of Martelli and Montanari and proves that it is correct.
We first prove some necessary properties about `unifies`, in
particular, that `unifies` is reflexive, that `unifies` is preserved
and reflected by substitution, and that there are no unifiers for an
equation of the form `x ≐ M` when `x` occurs in `M`. Then we turn to
the proof of termination of Martelli and Montanari's unification
algorithm, defining a measure function and proving lemmas that show
the measure decreases for each of the recursive calls. Those lemmas
then enable the definition of the `unify` function by well-founded
recursion on the measure. Finally, we prove that `unify` is correct,
which is to say that `unify` is sound and complete:

1. (Soundness) If it returns a substitution σ, then σ unifies the equations.
2. (Completeness) If it returns `no-solution`, then
   there are no substitutions that unify the equations.

## Properties of Unifiers


### The unifies relation is reflexive

We shall prove that

    σ unifies σ

provided that σ is idempotent.  The proof is by induction on σ and the
base case is trivial.  For the induction step, we need to show that

    σ' unifies σ'
    → (` x ≐ M) ∷ σ'  unifies  (` x ≐ M) ∷ σ'

So we need to show that

    (1)  subst ((` x ≐ M) ∷ σ') (` x) ≡ subst ((` x ≐ M) ∷ σ') M
    (2)  (` x ≐ M) ∷ σ'  unifies σ'

For the proof of (1), we have

    subst ((` x ≐ M) ∷ σ') (` x)  ≡    (definition of subst)
    M                             ≡    (σ is idempotent)
    ((` x ≐ M) ∷ σ') M                   

We generalize (2) to the upcoming lemma named `no-vars→ext-unifies`,
which separates the two occurences of σ' into separate variables,
enabling a proof by induction. The proof requires another lemma,
`ext-subst`, which states that extending a substitution with an
equation `x ≐ M` does not change the result of applying the
substitution to a term `L` if  `x` does not occur in `L` or in `σ`.

```
private
  ext-subst : ∀{σ}{x}{M}{L}
     → x ∉ vars L  →  x ∉ vars-eqs σ
     → subst ((` x ≐ M) ∷ σ) L ≡ subst σ L
  ext-subst-vec : ∀{σ}{x}{M}{n}{Ls : Vec Term n}
     → x ∉ vars-vec Ls  →  x ∉ vars-eqs σ
     → subst-vec ((` x ≐ M) ∷ σ) Ls ≡ subst-vec σ Ls
  ext-subst {σ} {x} {M} {` y} x∉L x∉σ
      with x ≟ y
  ... | yes refl = ⊥-elim (x∉L (x∈⁅x⁆ x))
  ... | no xy = subst-var-neq xy
  ext-subst {σ} {x} {M} {op ⦅ Ls ⦆} x∉L x∉σ =
      cong (λ □ → op ⦅ □ ⦆) (ext-subst-vec {σ}{x}{M}{Ls = Ls} x∉L x∉σ)
  ext-subst-vec {σ} {x} {M} {zero} {Ls} x∉Ls x∉σ = refl
  ext-subst-vec {σ} {x} {M} {suc n} {L ∷ Ls} x∉L∪Ls x∉σ =
      cong₂ _∷_ (ext-subst {σ}{x}{M}{L} (λ x∈L → x∉L∪Ls (p⊆p∪q _ _ x∈L)) x∉σ)
                (ext-subst-vec {σ}{x}{M}{n}{Ls} (λ x∈Ls → x∉L∪Ls (q⊆p∪q _ _ x∈Ls)) x∉σ)
```

In the following proof of `no-vars→ext-unifies`, the important
reasoning happens in the last part of the where clause, in the proof
that

    subst σ L ≡ subst σ N
    → subst ((` x ≐ M) ∷ σ) L ≡ subst ((` x ≐ M) ∷ σ) N

Working from right-to-left in the goal, we apply the `ext-subst` lemma,
then the premise, and then the `ext-subst` lemma again but in reverse.

```
private
  no-vars→ext-unifies : ∀{σ}{x}{M}{eqs}
     → σ unifies eqs
     → x ∉ vars-eqs eqs
     → x ∉ vars-eqs σ
     → ((` x ≐ M) ∷ σ) unifies eqs
  no-vars→ext-unifies {σ} {x} {M} {[]} σeqs x∉eqs x∉σ = tt
  no-vars→ext-unifies {σ} {x} {M} {(L ≐ N) ∷ eqs} ⟨ σL=σN , σeqs ⟩ x∉L∪N∪eqs x∉σ =
    let IH = no-vars→ext-unifies {σ} {x} {M} {eqs} σeqs x∉eqs x∉σ in
    ⟨ [x=M]σL=[x=M]σN , IH ⟩
      where
      x∉L : x ∉ vars L
      x∉L = λ x∈L → x∉L∪N∪eqs (p⊆p∪q _ _ x∈L ) 
      x∉N : x ∉ vars N
      x∉N = λ x∈N →
          let x∈L∪N∪eqs = p⊆r→p⊆q∪r _ _ _ (p⊆p∪q _ _) x∈N in
          x∉L∪N∪eqs x∈L∪N∪eqs
      x∉eqs : x ∉ vars-eqs eqs
      x∉eqs = λ x∈eqs →
        let x∈L∪N∪eqs = p⊆r→p⊆q∪r _ _ _ (p⊆r→p⊆q∪r _ _ _ ⊆-refl) x∈eqs in
        x∉L∪N∪eqs x∈L∪N∪eqs
        
      [x=M]σL=[x=M]σN =
          begin
              subst ((` x ≐ M) ∷ σ) L
          ≡⟨ ext-subst {σ}{x}{M}{L} x∉L x∉σ ⟩
              subst σ L
          ≡⟨ σL=σN ⟩
              subst σ N
          ≡⟨ sym (ext-subst {σ}{x}{M}{N} x∉N x∉σ) ⟩
              subst ((` x ≐ M) ∷ σ) N
          ∎
```

The following formalizes the proof of the reflexivity property.

```
  unifies-refl : ∀{σ} → IdemSubst σ → σ unifies σ
  unifies-refl {[]} empty = tt
  unifies-refl {(` x ≐ M) ∷ σ'} (insert x∉M x∉σ' M∩σ⊆∅ SΣ) =
      ⟨ G1 , G2 ⟩
      where
      H = begin⊆
              vars M ∩ (⁅ x ⁆ ∪ dom σ')
          ⊆⟨ ⊆-reflexive (∪-distribˡ-∩ {vars M}) ⟩
              (vars M ∩ ⁅ x ⁆) ∪ (vars M ∩ dom σ')
          ⊆⟨ p⊆r→q⊆s→p∪q⊆r∪s (x∉p→p∩⁅x⁆⊆∅ _ _ x∉M) M∩σ⊆∅ ⟩
              ∅ ∪ ∅
          ⊆⟨ ⊆-reflexive (p∪∅≡p _) ⟩
              ∅
          ■
      G1 = begin
               subst ((` x ≐ M) ∷ σ') (` x)
           ≡⟨ subst-var-eq {x}{M}{σ'} ⟩
               M
           ≡⟨ sym (M∩domσ⊆∅→subst-id H) ⟩
               subst ((` x ≐ M) ∷ σ') M
           ∎
      IH : σ' unifies σ'
      IH = unifies-refl {σ'} SΣ
      G2 : ((` x ≐ M) ∷ σ') unifies σ'
      G2 = no-vars→ext-unifies IH x∉σ' x∉σ'
```

### Substitution preserves unifiers

Next we prove that substitution preserves unifiers.

      subst θ (` x) ≡ subst θ M
    → θ unifies eqs
    → θ unifies ([ M / x ] eqs)

To do so, we'll need to prove that substitution preserves the
unification of each equation.

      subst σ (` x) ≡ subst σ M
    → subst σ L ≡ subst σ N
    → subst σ ([ x := M ] L) ≡ subst σ ([ x := M ] N)

We prove this as a corollary of the following lemma, which establishes that
a substitution `σ` always unifies both `N` and `[ x := M ] N` under the
assumption that `subst σ x ≡ subst σ M`.

```
  subst-invariant : ∀{N}{x}{σ}{M}
    → subst σ (` x) ≡ subst σ M
    → subst σ N ≡ subst σ ([ x := M ] N)
  subst-vec-invariant : ∀{n}{Ns : Vec Term n}{z}{σ}{M}
    → subst σ (` z) ≡ subst σ M
    → subst-vec σ Ns ≡ subst-vec σ ([ z ::= M ] Ns)
  subst-invariant {` x} {z} {σ} {M} σzM
      with z ≟ x
  ... | yes refl = σzM
  ... | no zx = refl
  subst-invariant {op ⦅ Ns ⦆} {z} {σ} {M} σzM =
      cong (λ □ → op ⦅ □ ⦆) (subst-vec-invariant σzM)
  subst-vec-invariant {zero} {Ns} σzM = refl
  subst-vec-invariant {suc n} {N ∷ Ns}{z}{σ}{M} σzM
      rewrite subst-invariant {N}{z}{σ}{M} σzM
      | subst-vec-invariant {n} {Ns}{z}{σ}{M} σzM = refl
```

To prove that substitution preserves the unification of one equation,
we reason equationally in three steps, applying `subst-invariant` in
reverse, then the second premise, and then `subst-invariant` in the
forward direction.

```
  subst-pres-equation : ∀{L}{N}{x}{σ}{M}
    → subst σ (` x) ≡ subst σ M
    → subst σ L ≡ subst σ N
    → subst σ ([ x := M ] L) ≡ subst σ ([ x := M ] N)
  subst-pres-equation {L}{N}{x}{σ}{M} σxM σLM =
      begin
          subst σ ([ x := M ] L)
      ≡⟨ sym (subst-invariant {L} σxM) ⟩
          subst σ L
      ≡⟨ σLM ⟩
          subst σ N
      ≡⟨ subst-invariant {N} σxM ⟩
          subst σ ([ x := M ] N)
      ∎
```

The proof that substitution preserves unifiers follows by a
straightforward proof by induction.

```
  subst-pres : ∀{eqs σ x M}
    → subst σ (` x) ≡ subst σ M
    → σ unifies eqs
    → σ unifies ([ M / x ] eqs)
  subst-pres {[]} eq σeqs = tt
  subst-pres {(L ≐ N) ∷ eqs} {σ}{x}{M} eq ⟨ σLM , σeqs ⟩ =
    ⟨ subst-pres-equation {L = L}{N = N} eq σLM , (subst-pres {eqs} eq σeqs) ⟩
```

The `append-eqs` operation also preserves unifiers.

```
  append-pres : ∀{n}{Ms Ls : Vec Term n}{eqs}{σ}
     → σ unifies eqs
     → subst-vec σ Ms ≡ subst-vec σ Ls
     → σ unifies append-eqs Ms Ls eqs
  append-pres {zero} {Ms} {Ls} σeqs σMsLs = σeqs
  append-pres {suc n} {M ∷ Ms} {L ∷ Ls} σeqs σMLMsLs
      with ∷≡-inversion σMLMsLs
  ... | ⟨ σML , σMsLs ⟩ = ⟨ σML , (append-pres σeqs σMsLs) ⟩
```

### Substitution reflects unifiers

Substitution also reflects unifiers. Thankfully, this is also a
corollary of the `subst-invariant` lemma. We prove that substitution
reflects the unification of one equation in a sequence of three
steps, similar to the proof of `subst-pres-equation`.

```
  subst-reflect-equation : ∀{L}{N}{z}{θ}{M}
    → subst θ (` z) ≡ subst θ M
    → subst θ ([ z := M ] L) ≡ subst θ ([ z := M ] N)
    → subst θ L ≡ subst θ N
  subst-reflect-equation {L}{N}{z}{θ}{M} θzM θLM =
      begin
          subst θ L
      ≡⟨ subst-invariant {L} θzM ⟩
          subst θ ([ z := M ] L)
      ≡⟨ θLM ⟩
          subst θ ([ z := M ] N)
      ≡⟨ sym (subst-invariant {N} θzM) ⟩
          subst θ N
      ∎
```

The proof that substitution reflects unifiers follows by a
straightforward proof by induction.

```
  subst-reflect : ∀{eqs θ x M}
    → θ unifies ([ M / x ] eqs)
    → subst θ (` x) ≡ subst θ M
    → θ unifies eqs
  subst-reflect {[]} {θ} {x} {M} θ[M/x]eqs θx=θM = tt
  subst-reflect {⟨ L , N ⟩ ∷ eqs} {θ} {x} {M} ⟨ θ[x:=M]L=θ[x:=M]N , θ[M/x]eqs ⟩ θx=θM =
      ⟨ subst-reflect-equation {L = L}{N} θx=θM θ[x:=M]L=θ[x:=M]N ,
        subst-reflect {eqs}{θ}{x}{M} θ[M/x]eqs θx=θM ⟩
```

The `append-eqs` operation reflects unifiers.

```
  subst-vec-reflect : ∀{n}{Ms Ls : Vec Term n}{eqs}{θ}
     → θ unifies append-eqs Ms Ls eqs
     → (subst-vec θ Ms ≡ subst-vec θ Ls)  × θ unifies eqs
  subst-vec-reflect {zero} {[]} {[]} {eqs} {θ} θMs,Ls,eqs = ⟨ refl , θMs,Ls,eqs ⟩
  subst-vec-reflect {suc n} {M ∷ Ms} {L ∷ Ls} {eqs} {θ} ⟨ θM=θL , θMs,Ls,eqs ⟩ 
      with subst-vec-reflect {n} {Ms} {Ls} {eqs} {θ} θMs,Ls,eqs
  ... | ⟨ θMs=θLs , θeqs ⟩ =     
      ⟨ cong₂ _∷_ θM=θL θMs=θLs , θeqs ⟩
```

### A failed occurs-check implies no solutions

An equation of the form `x ≐ f ⦅ Ms ⦆` where `x ∈ vars (f ⦅ Ms ⦆)` has no unifiers.
We shall prove this by contradiction, assuming that there is a unifier `σ`
and deriving false. From `subst σ x ≡ subst σ (f ⦅ Ms ⦆)`, we know that
the number of operators (aka. function symbols) in `subst σ x`
must be the same as the number of operators in `subst σ (f ⦅ Ms ⦆)`.
However, we shall prove a lemma that if `x ∈ vars (f ⦅ Ms ⦆)`,
then the number of operators in `subst σ x` is strictly less than
the number of operators in `subst σ (f ⦅ Ms ⦆)`. After all,
`f` counts for one operator and `subst σ Ms` contains
at least one copy of `subst σ x`. Thus we have a contradiction. 

We begin by defining functions for counting the number of operators in
a term, in a vector of terms, and in a list of equations.

```
  num-ops : Term → ℕ
  num-ops-vec : ∀{n} → Vec Term n → ℕ
  num-ops (` x) = 0
  num-ops (op ⦅ Ms ⦆) = suc (num-ops-vec Ms)
  num-ops-vec {zero} Ms = 0
  num-ops-vec {suc n} (M ∷ Ms) = num-ops M + num-ops-vec Ms

  num-ops-eqs : Equations → ℕ
  num-ops-eqs [] = 0
  num-ops-eqs ((L ≐ M) ∷ eqs) = num-ops L + num-ops M + num-ops-eqs eqs
```

We define the following function for identifying terms that are
operator applications.

```
  is-op : Term → Set
  is-op (` x) = ⊥
  is-op (op ⦅ Ms ⦆) = ⊤
```

The main lemma proves that if `x ∈ vars M`, the number of operators in
`subst σ x` is less than the number of operators in `subst σ M`.
The proof is a straightforward induction on the term `M`.

```
  num-ops-less : ∀ {M}{x σ}
     → x ∈ vars M  →  is-op M
     → num-ops (subst σ (` x)) < num-ops (subst σ M)
  num-ops-less-vec : ∀ {n}{Ms : Vec Term n}{x σ}
     → x ∈ vars-vec Ms
     → num-ops (subst σ (` x)) ≤ num-ops-vec (subst-vec σ Ms)
  num-ops-less {op ⦅ Ms ⦆}{x}{σ} x∈Ms opM =
     s≤s (num-ops-less-vec {Ms = Ms}{x}{σ} x∈Ms)
  num-ops-less-vec {zero} {[]} {x} {σ} x∈Ms = ⊥-elim (∉∅ {x} x∈Ms)
  num-ops-less-vec {suc n} {(` y) ∷ Ms} {x} {σ} x∈MMs
      with ∈p∪q→∈p⊎∈q x∈MMs
  ... | inj₁ x∈M
      with x ≟ y
  ... | yes refl = m≤m+n (num-ops (subst σ (` y))) (num-ops-vec (subst-vec σ Ms))
  ... | no xy = ⊥-elim ((x∉⁅y⁆ x y xy) x∈M)
  num-ops-less-vec {suc n} {(` y) ∷ Ms} {x} {σ} x∈MMs
      | inj₂ x∈Ms =
      let IH = num-ops-less-vec {n} {Ms}{x}{σ} x∈Ms in
      begin≤
          num-ops (subst σ (` x))
      ≤⟨ IH ⟩
          num-ops-vec (subst-vec σ Ms)
      ≤⟨ m≤n+m _ _ ⟩
          num-ops (subst σ (` y)) + num-ops-vec (subst-vec σ Ms)
      QED
  num-ops-less-vec {suc n} {(op ⦅ Ls ⦆) ∷ Ms} {x} {σ} x∈MMs
      with ∈p∪q→∈p⊎∈q x∈MMs
  ... | inj₁ x∈M =
      let σx<1+σLS = num-ops-less {(op ⦅ Ls ⦆)}{x}{σ} x∈M tt in
      begin≤
          num-ops (subst σ (` x))
      ≤⟨ ≤-pred σx<1+σLS ⟩
          num-ops-vec (subst-vec σ Ls)
      ≤⟨ m≤m+n _ _ ⟩
          num-ops-vec (subst-vec σ Ls) + num-ops-vec (subst-vec σ Ms)
      ≤⟨ n≤1+n _ ⟩
          suc (num-ops-vec (subst-vec σ Ls) + num-ops-vec (subst-vec σ Ms))
      QED
  num-ops-less-vec {suc n} {M ∷ Ms} {x} {σ} x∈MMs
      | inj₂ x∈Ms =
      let IH = num-ops-less-vec {n} {Ms}{x}{σ} x∈Ms in
      begin≤
          num-ops (subst σ (` x))
      ≤⟨ IH ⟩
          num-ops-vec (subst-vec σ Ms)
      ≤⟨ m≤n+m _ _ ⟩
          num-ops (subst σ M) + num-ops-vec (subst-vec σ Ms)
      QED
```

Thus, if `x ∈ vars M`, there is no solution to `x ≐ M`.

```
  occurs-no-soln : ∀{σ x M}
    → x ∈ vars M → is-op M
    → subst σ (` x) ≢ subst σ M
  occurs-no-soln {σ} x∈M opM σxM
      with num-ops-less {σ = σ} x∈M opM
  ... | σx<σM rewrite σxM =
        ⊥-elim (1+n≰n σx<σM)
```

## Proof of Termination

We use well-founded recursion to define the unification function.  We
shall show that a lexicographic ordering of three numbers decreases
with each recursive call. The numbers are

1. the number of variables in the equations,
2. the number of operators in the equations,
3. the number of equations.

We prove that this particular lexicographic ordering is well-founded
using the facts that products are well-founded (from the
`LexicographicOrdering` module) and that less-than is well-founded
(from `Data.Nat.Induction`).

```
  measure : Equations → Equations → ℕ × ℕ × ℕ
  measure eqs θ = ⟨ ∣ vars-eqs eqs ∣ , ⟨ num-ops-eqs eqs , suc (length eqs) ⟩ ⟩

  open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
  open import LexicographicOrdering using (×-Lex; ×-wellFounded)
  open import Induction.WellFounded using (WellFounded)
  open import Relation.Binary using (Rel)

  _<₃_ : Rel (ℕ × ℕ × ℕ) _
  _<₃_ = ×-Lex _≡_ _<_ (×-Lex _≡_ _<_ _<_)

  <₃-wellFounded : WellFounded _<₃_
  <₃-wellFounded = ×-wellFounded <-wellFounded
                     (×-wellFounded <-wellFounded <-wellFounded)
```

We define the following convenience functions for proving that one
triple is lexicogrpahically less than another triple.

```
  first-< : ∀ {k l m k' l' m'}
          → k < k'
          → ⟨ k , ⟨ l , m ⟩ ⟩ <₃ ⟨ k' , ⟨ l' , m' ⟩ ⟩
  first-< k<k' = inj₁ k<k'

  second-< : ∀ {k l m k' l' m'}
          → k ≤ k' → l < l'
          → ⟨ k , ⟨ l , m ⟩ ⟩ <₃ ⟨ k' , ⟨ l' , m' ⟩ ⟩
  second-< {k}{k' = k'} k≤k' l<l'
      with k ≟ k'
  ... | yes refl = inj₂ ⟨ refl , inj₁ l<l' ⟩
  ... | no k≢k' = inj₁ (≤∧≢⇒< k≤k' k≢k')

  third-< : ∀ {k l m k' l' m'}
          → k ≤ k' → l ≤ l' → m < m'
          → ⟨ k , ⟨ l , m ⟩ ⟩ <₃ ⟨ k' , ⟨ l' , m' ⟩ ⟩
  third-< {k}{l}{k' = k'}{l'} k≤k' l≤l' m<m'
      with k ≟ k'
  ... | no k≢k' = inj₁ (≤∧≢⇒< k≤k' k≢k')
  ... | yes refl
      with l ≟ l'
  ... | no l≢l' = inj₂ ⟨ refl , (inj₁ (≤∧≢⇒< l≤l' l≢l')) ⟩
  ... | yes refl = inj₂ ⟨ refl , (inj₂ ⟨ refl , m<m' ⟩) ⟩
```

When we remove a trivial equation, of the form `x ≐ x`, the number of
variables and the number of operators either decrease or stays the
same. Of course, the number of equations decreases by one.

```
  measure1 : ∀{eqs}{θ}{x} → measure eqs θ <₃ measure ((` x ≐ ` x) ∷ eqs) θ
  measure1 {eqs}{θ}{x} = third-< vars≤ ≤-refl eqs<
      where
      vars≤ : ∣ vars-eqs eqs ∣ ≤ ∣ vars-eqs ((` x ≐ ` x) ∷ eqs) ∣
      vars≤ =
          begin≤
              ∣ vars-eqs eqs ∣
          ≤⟨ ∣q∣≤∣p∪q∣ {⁅ x ⁆} {vars-eqs eqs} ⟩
              ∣ ⁅ x ⁆ ∪ vars-eqs eqs ∣
          ≤⟨ ∣q∣≤∣p∪q∣ {⁅ x ⁆} {⁅ x ⁆ ∪  vars-eqs eqs} ⟩
              ∣ ⁅ x ⁆ ∪ ⁅ x ⁆ ∪ vars-eqs eqs ∣
          ≤⟨ ≤-refl ⟩
              ∣ vars-eqs ((` x ≐ ` x) ∷ eqs) ∣
          QED
      eqs< : suc (length eqs) < suc (length ((` x ≐ ` x) ∷ eqs))
      eqs< = s≤s (s≤s ≤-refl)
```

When we eliminate a variable by substitution, we reduce the number of
variables in the equation. 

```
  vars-eqs-sub-less : ∀{M x eqs}
     → ¬ x ∈ vars M
     → ∣ vars-eqs ([ M / x ] eqs) ∣ < ∣ vars-eqs ((` x ≐ M) ∷ eqs) ∣
  vars-eqs-sub-less {M}{x}{eqs} x∉M =
      begin≤
          suc ∣ vars-eqs ([ M / x ] eqs) ∣
      ≤⟨ s≤s (p⊆q⇒∣p∣≤∣q∣ (vars-eqs-subst-∪ {eqs}{x}{M})) ⟩
          suc ∣ vars M ∪ (vars-eqs eqs - ⁅ x ⁆) ∣
      ≤⟨ ≤-reflexive (cong (λ □ → suc ∣ □ ∣) (distrib-∪-2 (vars M) _ _ (x∉p→p∩⁅x⁆⊆∅ _ _ x∉M))) ⟩
          suc ∣ (vars M ∪ vars-eqs eqs) - ⁅ x ⁆ ∣
      ≤⟨ ∣p-x∣<∣p∪x∣ _ _ ⟩
          ∣ (vars M ∪ vars-eqs eqs) ∪ ⁅ x ⁆ ∣
      ≤⟨ ≤-reflexive (cong (λ □ → ∣ □ ∣) (∪-comm _ _)) ⟩
          ∣ ⁅ x ⁆ ∪ vars M ∪ vars-eqs eqs ∣
      ≤⟨ ≤-refl ⟩
          ∣ vars-eqs ((` x ≐ M) ∷ eqs) ∣
      QED
```

For an equation of the form `x ≐ M`, the above lemma directly shows
that the measure decreases.

```
  measure2 : ∀{eqs}{θ}{M}{x}
     → x ∉ vars M
     → measure ([ M / x ] eqs) ((` x ≐ M) ∷ [ M / x ] θ)
       <₃ measure ((` x ≐ M) ∷ eqs) θ
  measure2{eqs}{θ}{M}{x} x∉M = (first-< (vars-eqs-sub-less {M}{x}{eqs} x∉M))
```

For an equation of the form `M ≐ x`, we do a little extra work to flip
around the conclusion of the lemma `vars-eqs-sub-less` to match what
is needed in this case.

```
  measure3 : ∀{eqs}{θ}{M}{x}
     → x ∉ vars M
     → measure  ([ M / x ] eqs) ((` x ≐ M) ∷ [ M / x ] θ)
       <₃ measure ((M ≐ ` x) ∷ eqs) θ
  measure3 {eqs}{θ}{M}{x} x∉M
      with vars-eqs-sub-less {M}{x}{eqs} x∉M
  ... | vars< 
      rewrite sym (∪-assoc ⁅ x ⁆ (vars M) (vars-eqs eqs))
      | ∪-comm ⁅ x ⁆ (vars M)
      | ∪-assoc (vars M) ⁅ x ⁆ (vars-eqs eqs) = 
     first-< vars< 
```

When we decompose an equality between two function symbol
applications, the number of variables stays the same.  This is because
the result of `append-eqs` is an equation with the same variables as
there are in its input.

```
  var-eqs-append-≡ : ∀ {n} (Ms Ls : Vec Term n) eqs
     → vars-eqs (append-eqs Ms Ls eqs) ≡ vars-vec Ms ∪ vars-vec Ls ∪ vars-eqs eqs
  var-eqs-append-≡ {zero} [] [] eqs rewrite ∅∪p≡p (vars-eqs eqs) | ∅∪p≡p (vars-eqs eqs) = refl
  var-eqs-append-≡ {suc n} (M ∷ Ms) (L ∷ Ls) eqs 
      rewrite ∪-assoc (vars L) (vars-vec Ls) (vars-eqs eqs)
      | ∪-assoc (vars M) (vars-vec Ms) (vars L ∪ vars-vec Ls ∪ vars-eqs eqs)
      | sym (∪-assoc (vars-vec Ms) (vars L) (vars-vec Ls ∪ vars-eqs eqs))
      | ∪-comm (vars-vec Ms) (vars L) 
      | ∪-assoc (vars L) (vars-vec Ms) (vars-vec Ls ∪ vars-eqs eqs)
      | var-eqs-append-≡ {n} Ms Ls eqs =
      refl
```

When we decompose an equality between two function symbol
applications, the number of operators is reduced by one.  Towards
proving that, we first prove that the result of `append-eqs` is an
equation with the same number of operators as there are in its input.

```
  num-ops-append : ∀ {n} (Ms Ls : Vec Term n) eqs
     → num-ops-eqs (append-eqs Ms Ls eqs) ≡ num-ops-vec Ms + num-ops-vec Ls + num-ops-eqs eqs
  num-ops-append {zero} [] [] eqs = refl
  num-ops-append {suc n} (M ∷ Ms) (L ∷ Ls) eqs
      rewrite num-ops-append {n} Ms Ls eqs =
      G (num-ops M) (num-ops L) (num-ops-vec Ms) (num-ops-vec Ls) (num-ops-eqs eqs)
      where
      open +-*-Solver
      G : (nM nL nMs nLs neqs : ℕ)
          → (nM + nL) + ((nMs + nLs) + neqs) ≡ ((nM + nMs) + (nL + nLs)) + neqs
      G = solve 5 (λ nM nL nMs nLs neqs →
            (nM :+ nL) :+ ((nMs :+ nLs) :+ neqs) := ((nM :+ nMs) :+ (nL :+ nLs)) :+ neqs) refl
```

Putting these two pieces together, we prove that decomposing an
equality between two function symbol applications causes the measure
to decrease.

```
  measure4 : ∀{eqs}{θ}{op}{Ms Ls : Vec Term (arity op)}
     → measure (append-eqs Ms Ls eqs) θ
       <₃ measure ((op ⦅ Ms ⦆ ≐ op ⦅ Ls ⦆) ∷ eqs) θ
  measure4 {eqs}{θ}{op}{Ms}{Ls} = second-< vars≤ ops<
      where
      vars≤ : ∣ vars-eqs (append-eqs Ms Ls eqs) ∣ ≤ ∣ vars-vec Ms ∪ vars-vec Ls ∪ vars-eqs eqs ∣
      vars≤ rewrite var-eqs-append-≡ Ms Ls eqs = p⊆q⇒∣p∣≤∣q∣ ⊆-refl

      ops< : num-ops-eqs (append-eqs Ms Ls eqs) < suc (num-ops-vec Ms + suc (num-ops-vec Ls) + num-ops-eqs eqs)
      ops< rewrite num-ops-append Ms Ls eqs
           | +-comm (num-ops-vec Ms) (suc (num-ops-vec Ls))
           | +-comm (num-ops-vec Ls) (num-ops-vec Ms) = s≤s (≤-step ≤-refl)
```

## The Unify Function


The `unify` function will take as input a list of equations and either
return a substitution or an indication that there are no solutions to
the equations. We define the following `Result` data type for these
purposes.

```
data Result : Set where
  finished : Substitution → Result
  no-solution : Result
```

We define `unify` in terms of the following recursive helper function,
`unify-rec`, that takes two extra parameters. The parameter `σ` is the
substitution that has been accumulated so far, and that will
eventually become the solution.  The parameter of data type `Acc _<₃_
(measure eqs σ)` is used to ensure that the measure decreases on
recursive calls. This data type has one constructor, `acc`, with one
parameter, which we name `rec` below. When we apply `rec` to a proof
that the measure decreases, we get another instance of `Acc` that is
an appropriate argument for the recursive call to `unify-rec`.

To define `unify-rec`, we first pattern match on `eqs`. If it is
empty, then unification is finished and we return the current
substitution. If `eqs` is not empty, we pattern match on the first
equation. If it is an equation between two variables, we either
eliminate the equation (if the two variables are equal), or we
eliminate one of the variables by substitution.  If the equation is
between a variable and an operator application, we eliminate the
variable by substitution. However, we first check to see whether the
variable occurs inside the operator application, in which case we halt
with no solution. Finally, if the equation is between two operator
applications, we check whether the two operators are equal.  If not,
there is no solution. Otherwise, we append the corresponding sub-terms
to the equations and recursively call `unify-rec`.


```
private
  unify-rec : (eqs : Equations) → (σ : Substitution)
            → Acc _<₃_ (measure eqs σ) → Result
  unify-rec [] σ rec = finished σ
  unify-rec ((` x ≐ ` y) ∷ eqs) σ (acc rec)
      with x ≟ y
  ... | yes refl = unify-rec eqs σ (rec _ (measure1 {eqs}{σ}))
  ... | no xy =
      let eqs' = [ ` y / x ] eqs in
      let σ' = (` x ≐ ` y) ∷ [ ` y / x ] σ in
      unify-rec eqs' σ' (rec _ (measure2{eqs}{σ} (x∉⁅y⁆ _ _ xy)))
  unify-rec ((` x ≐ op ⦅ Ms ⦆) ∷ eqs) σ (acc rec)
      with occurs? x (op ⦅ Ms ⦆)
  ... | yes x∈M = no-solution
  ... | no x∉M =
      let eqs' = [ op ⦅ Ms ⦆ / x ] eqs in
      let σ' = (` x ≐ op ⦅ Ms ⦆) ∷ [ op ⦅ Ms ⦆ / x ] σ in
      unify-rec eqs' σ' (rec _ (measure2{eqs}{σ} x∉M))
  unify-rec ((op ⦅ Ms ⦆ ≐ ` x) ∷ eqs) σ (acc rec)
      with occurs? x (op ⦅ Ms ⦆)
  ... | yes x∈M = no-solution
  ... | no x∉M =
      let eqs' = [ op ⦅ Ms ⦆ / x ] eqs in
      let σ' = (` x ≐ op ⦅ Ms ⦆) ∷ [ op ⦅ Ms ⦆ / x ] σ in
      unify-rec eqs' σ' (rec _ (measure3{eqs}{σ} x∉M))
  unify-rec ((op ⦅ Ms ⦆ ≐ op' ⦅ Ls ⦆) ∷ eqs) σ (acc rec)
      with op-eq? op op'
  ... | yes refl = unify-rec (append-eqs Ms Ls eqs) σ (rec _ (measure4 {eqs}{σ}))
  ... | no neq = no-solution
```

With `unify-rec` complete, it is straightforward to define the `unify`
function. We apply `unify-rec` to the empty substitution and a proof
that `<₃` is well founded.

```
unify : (eqs : Equations) → Result
unify eqs = unify-rec eqs [] (<₃-wellFounded (measure eqs []))
```

## Proof that Unify is Correct

We shall now prove that the `unify` function is correct, i.e., that it
is sound and complete with respect to `unifies`:

1. (Soundness) If `unify` returns a substitution σ,
  then σ unifies the equations.
2. (Completeness) If `unify` returns `no-solution`, then
   there are no substitutions that unify the equations.

The `unify` function merely kicks things off, and all the real
work is done in `unify-rec`. So we shall prove a soundness lemma
and a completeness lemma for `unify-rec`.

The `unify-rec` function has two preconditions:

1. the current substitution σ is idempotent, and
2. the variables in the domain of σ do not occur in the current equations
   (because we've eliminated them).

In the proofs of these soundness and completeness lemmas, to invoke
the induction hypothesis, we need to establish the above two
preconditions for the new substitution and the new set of
equations. Regarding idempotency, we shall use the `insert-subst`
lemma from the module
[`TermSubstUnify`](./TermSubstUnify.lagda.md). To satisfy one of the
premises of that lemma, we sometimes need the following simple lemma
that commutes the union of two sets.

```
private
  M∪x∪eqs : ∀ {M}{x}{eqs}{σ}
     → (vars M ∪ ⁅ x ⁆ ∪ vars-eqs eqs) ∩ dom σ ⊆ ∅
     → (⁅ x ⁆ ∪ vars M ∪ vars-eqs eqs) ∩ dom σ ⊆ ∅
  M∪x∪eqs {M}{x}{eqs}{σ} prem
      rewrite sym (∪-assoc (vars M) ⁅ x ⁆ (vars-eqs eqs))
      | ∪-comm (vars M) ⁅ x ⁆
      | ∪-assoc ⁅ x ⁆ (vars M) (vars-eqs eqs)
      = prem
```

We have some work to do regarding point 2, that the variables in the
domain of the new substitution do not occur in the new list of
equations.

When we remove a trivial equation of the form `x ≐ x`, the
substitution σ remains unchanged so its obvious that the domain of σ
is still disjoint from the variables in the remaining equations.

```
  xx-eqs∩dom⊆∅ : ∀ {x eqs σ}
     → vars-eqs ((` x ≐ ` x) ∷ eqs) ∩ dom σ ⊆ ∅
     → vars-eqs eqs ∩ dom σ ⊆ ∅
  xx-eqs∩dom⊆∅ {x}{eqs}{σ} prem
      rewrite sym (∪-assoc ⁅ x ⁆ ⁅ x ⁆ (vars-eqs eqs)) =
      begin⊆
      vars-eqs eqs ∩ dom σ                        ⊆⟨ p⊆r→q⊆s→p∩q⊆r∩s (q⊆p∪q _ _) ⊆-refl  ⟩
      ((⁅ x ⁆ ∪ ⁅ x ⁆) ∪ vars-eqs eqs) ∩ dom σ    ⊆⟨ prem ⟩
      ∅
      ■
```

When we eliminate a variable by substitution (equations of the form
`x ≐ M` or `M ≐ x` with `M ≡ op ⦅ Ms ⦆`),
the new substition is `(x ≐ M) ∷ [ M / x ] σ` and the new equations are
`[ M / x ] eqs`, so we need to show that

    vars-eqs ([ M / x ] eqs) ∩ (⁅ x ⁆ ∪ dom ([ M / x ] σ)) ⊆ ∅

assuming that

    vars-eqs ((x ≐ M) ∷ eqs) ∩ dom σ ⊆ ∅

which is to say

    (⁅ x ⁆ ∪ vars M ∪ vars-eqs eqs) ∩ dom σ ⊆ ∅

First, notice that because `x ∉ dom σ`,

    dom ([ M / x ] σ) ≡ dom σ

which is lemma `subst-dom` in [FirstOrderTerms](./FirstOrderTerms.lagda.md).
We use the following mini-lemma to derive `x ∉ dom σ`
from `(⁅ x ⁆ ∪ vars M ∪ vars-eqs eqs) ∩ dom σ ⊆ ∅`.

```
  [x∪p]∩q⊆∅→x∉q : ∀{x p q} → (⁅ x ⁆ ∪ p) ∩ q ⊆ ∅ → x ∉ q
  [x∪p]∩q⊆∅→x∉q {x}{p}{q} xpq x∈q =
      let x∈∅ = xpq {x} (proj₂ (∈∩ _ _ _) ⟨ (p⊆p∪q _ _ (x∈⁅x⁆ x)) , x∈q ⟩) in
      ⊥-elim (∉∅ x∈∅)
```
So it remains to prove

    vars-eqs ([ M / x ] eqs) ∩ (⁅ x ⁆ ∪ dom σ) ⊆ ∅

By the lemma `vars-eqs-subst-∪` in [FirstOrderTerms](./FirstOrderTerms.lagda.md),
we know that `vars-eqs ([ M / x ] eqs) ⊆ vars M  ∪ (vars-eqs eqs - ⁅ x ⁆)`,
so we just need to show that

    (vars M  ∪ (vars-eqs eqs - ⁅ x ⁆)) ∩ (⁅ x ⁆ ∪ dom σ) ⊆ ∅

If we distribute the intersection, we have

    (vars M  ∩ (⁅ x ⁆ ∪ dom σ))  ∪  ((vars-eqs eqs - ⁅ x ⁆) ∩ (⁅ x ⁆ ∪ dom σ)) ⊆ ∅

and therefore need to show

    (1)  vars M  ∩ (⁅ x ⁆ ∪ dom σ) ⊆ ∅
    (2)  (vars-eqs eqs - ⁅ x ⁆) ∩ (⁅ x ⁆ ∪ dom σ) ⊆ ∅

We prove (1) from `x ∉ M` and `vars M ∩ dom σ ⊆ ∅`.
We prove (2) from `vars-eqs eqs ∩ dom σ ⊆ ∅`.
The following is the Agda formalization of this proof.

```
  eqs∩x∪σ⊆∅ : ∀{x}{M}{σ}{eqs}
     → x ∉ vars M
     → (⁅ x ⁆ ∪ vars M ∪ vars-eqs eqs) ∩ dom σ ⊆ ∅
     → vars-eqs ([ M / x ] eqs) ∩ (⁅ x ⁆ ∪ dom ([ M / x ] σ)) ⊆ ∅
  eqs∩x∪σ⊆∅ {x}{M}{σ}{eqs} x∉M eqs∩domσ⊆∅ {- {y} y∈ -}
      rewrite subst-dom {x}{M}{σ} ([x∪p]∩q⊆∅→x∉q eqs∩domσ⊆∅) =
      begin⊆
          vars-eqs ([ M / x ] eqs) ∩ (⁅ x ⁆ ∪ dom σ)
      ⊆⟨ p⊆r→q⊆s→p∩q⊆r∩s (vars-eqs-subst-∪ {eqs = eqs}{M = M}) ⊆-refl ⟩
          (vars M  ∪ (vars-eqs eqs - ⁅ x ⁆)) ∩ (⁅ x ⁆ ∪ dom σ)
      ⊆⟨ ⊆-reflexive ∪-distrib-∩ ⟩
          (vars M ∩ (⁅ x ⁆ ∪ dom σ)) ∪ ((vars-eqs eqs - ⁅ x ⁆) ∩ (⁅ x ⁆ ∪ dom σ))
      ⊆⟨ p⊆r→q⊆s→p∪q⊆r∪s G1 G2 ⟩
          ∅ ∪ ∅
      ⊆⟨ ⊆-reflexive (p∪∅≡p _) ⟩
          ∅
      ■
      where
      G1a : vars M ∩ dom σ ⊆ ∅
      G1a rewrite ∪-distrib-∩ {⁅ x ⁆}{vars M ∪ vars-eqs eqs}{dom σ}
          | ∪-distrib-∩ {vars M}{vars-eqs eqs}{dom σ} =
            proj₁ (p∪q⊆∅→p⊆∅×q⊆∅ _ _ (proj₂ (p∪q⊆∅→p⊆∅×q⊆∅ _ _ eqs∩domσ⊆∅)))
      G1 : vars M  ∩ (⁅ x ⁆ ∪ dom σ) ⊆ ∅
      G1 = begin⊆
               vars M  ∩ (⁅ x ⁆ ∪ dom σ)
           ⊆⟨ ⊆-reflexive ∪-distribˡ-∩ ⟩
               (vars M ∩ ⁅ x ⁆) ∪ (vars M ∩ dom σ)
           ⊆⟨  p⊆r→q⊆s→p∪q⊆r∪s (x∉p→p∩⁅x⁆⊆∅ _ _ x∉M) G1a ⟩
               ∅ ∪ ∅
           ⊆⟨ ⊆-reflexive (p∪∅≡p _) ⟩
               ∅
           ■
      G2a : vars-eqs eqs ∩ dom σ ⊆ ∅
      G2a rewrite ∪-distrib-∩ {⁅ x ⁆}{vars M ∪ vars-eqs eqs}{dom σ}
          | ∪-distrib-∩ {vars M}{vars-eqs eqs}{dom σ} =
            proj₂ (p∪q⊆∅→p⊆∅×q⊆∅ _ _ (proj₂ (p∪q⊆∅→p⊆∅×q⊆∅ _ _ eqs∩domσ⊆∅)))
      G2 : (vars-eqs eqs - ⁅ x ⁆) ∩ (⁅ x ⁆ ∪ dom σ) ⊆ ∅
      G2 = begin⊆
               (vars-eqs eqs - ⁅ x ⁆) ∩ (⁅ x ⁆ ∪ dom σ)
           ⊆⟨ [p-q]∩[q∪r]⊆p∩r ⟩
               vars-eqs eqs ∩ dom σ
           ⊆⟨ G2a ⟩
               ∅
           ■
```

When we decompose an equality between two function symbol
applications, the substitution remains the same but we append the
corresponding sub-terms to the list of equations. The fact that
the domain of the substitution is disjoint from the variables in
the new equations follows from the lemma `var-eqs-append-≡`
that we proved above.

```
  MsLseqs∩domσ⊆∅ : ∀{n}{Ms Ls : Vec Term n}{eqs}{σ}
     → (vars-vec Ms ∪ vars-vec Ls ∪ vars-eqs eqs) ∩ dom σ ⊆ ∅
     → vars-eqs (append-eqs Ms Ls eqs) ∩ dom σ ⊆ ∅
  MsLseqs∩domσ⊆∅ {n}{Ms}{Ls}{eqs}{σ} prem =
     begin⊆
         vars-eqs (append-eqs Ms Ls eqs) ∩ dom σ
     ⊆⟨ p⊆r→q⊆s→p∩q⊆r∩s (⊆-reflexive (var-eqs-append-≡ {n} Ms Ls eqs)) ⊆-refl ⟩
         (vars-vec Ms ∪ vars-vec Ls ∪ vars-eqs eqs) ∩ dom σ
     ⊆⟨ prem ⟩
         ∅
     ■
```

We are now ready to prove that `unify-rec` is sound, i.e., that the
output substitution unifies the input equations and substitutions,
provided that hte input substitution is idempotent and the domain of
the input substitution is disjoint from the variables in the
equations. The explanation of the proof follows the below Agda code.

```
  unify-rec-sound : ∀{eqs}{σ}{σ'}{ac}
     → IdemSubst σ
     → vars-eqs eqs ∩ dom σ ⊆ ∅
     → unify-rec eqs σ ac ≡ finished σ'
     → σ' unifies eqs × σ' unifies σ
  unify-rec-sound {[]} {σ}{σ'}{ac} Sσ eqs∩domσ⊆∅ refl = ⟨ tt , unifies-refl Sσ ⟩
  unify-rec-sound {⟨ ` x , ` y ⟩ ∷ eqs} {σ} {σ'} {acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡σ'
      with x ≟ y 
  ... | yes refl
      with unify-rec-sound {eqs}{σ}{σ'} {rs _ (measure1 {eqs}{σ'})}
              Sσ (xx-eqs∩dom⊆∅ {x}{eqs}{σ} eqs∩domσ⊆∅) unify[eqs,σ]≡σ'
  ... | ⟨ σ'eqs , σ'σ ⟩ =
        ⟨ ⟨ G1a , G1b ⟩ , G2 ⟩
      where
      G1a : subst σ' (` x) ≡ subst σ' (` x)
      G1a = refl
      G1b : σ' unifies eqs
      G1b = σ'eqs
      G2 : σ' unifies σ
      G2 = σ'σ
  unify-rec-sound {⟨ ` x , ` y ⟩ ∷ eqs} {σ} {σ'} {acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡σ'
      | no xy
      with unify-rec-sound {[ ` y / x ] eqs}{(⟨ ` x , ` y ⟩ ∷ [ ` y / x ] σ)}{σ'}
               {rs _ (measure2{eqs}{σ'} (x∉⁅y⁆ _ _ xy))}
               (insert-subst {x}{` y}{σ}{eqs} (x∉⁅y⁆ x y xy) eqs∩domσ⊆∅ Sσ)
               (eqs∩x∪σ⊆∅ {x}{` y}{σ}{eqs} (x∉⁅y⁆ x y xy) eqs∩domσ⊆∅)
               unify[eqs,σ]≡σ'
  ... | ⟨ σ'[y/x]eqs , ⟨ σ'x=σ'y , σ'[y/x]σ ⟩ ⟩ =
        ⟨ ⟨ G1a , G1b ⟩ , G2 ⟩
      where
      G1a : subst σ' (` x) ≡ subst σ' (` y)
      G1a = σ'x=σ'y
      G1b : σ' unifies eqs
      G1b = subst-reflect σ'[y/x]eqs σ'x=σ'y
      G2 : σ' unifies σ
      G2 = subst-reflect σ'[y/x]σ σ'x=σ'y
  unify-rec-sound {⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ eqs} {σ} {σ'}{acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡σ'
      with occurs? x (op ⦅ Ms ⦆)
  ... | yes x∈M
      with unify[eqs,σ]≡σ'
  ... | ()    
  unify-rec-sound {⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ eqs} {σ} {σ'}{acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡σ'
      | no x∉M 
      with unify-rec-sound {([ op ⦅ Ms ⦆ / x ] eqs)} {(⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ [ op ⦅ Ms ⦆ / x ] σ)} {σ'}
               {rs _ (measure2{eqs}{σ} x∉M)}
               (insert-subst {x}{op ⦅ Ms ⦆}{σ}{eqs} x∉M eqs∩domσ⊆∅ Sσ)
               (eqs∩x∪σ⊆∅ {x}{op ⦅ Ms ⦆}{σ}{eqs} x∉M eqs∩domσ⊆∅)
               unify[eqs,σ]≡σ'
  ... | ⟨ σ'[M/x]eqs , ⟨ σ'xM , σ'[M/x]σ ⟩ ⟩ =
      ⟨ ⟨ G1a , G1b ⟩ , G2 ⟩
      where
      G1a : subst σ' (` x) ≡ subst σ' (op ⦅ Ms ⦆)
      G1a = σ'xM
      G1b : σ' unifies eqs
      G1b = subst-reflect σ'[M/x]eqs σ'xM
      G2 : σ' unifies σ
      G2 = subst-reflect σ'[M/x]σ σ'xM
  unify-rec-sound {⟨ op ⦅ Ms ⦆ , ` x ⟩ ∷ eqs} {σ} {σ'}{acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡σ'
      with occurs? x (op ⦅ Ms ⦆)
  ... | yes x∈M
      with unify[eqs,σ]≡σ'
  ... | ()    
  unify-rec-sound {⟨ op ⦅ Ms ⦆ , ` x ⟩ ∷ eqs} {σ} {σ'}{acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡σ'
      | no x∉M
      with unify-rec-sound {([ op ⦅ Ms ⦆ / x ] eqs)} {(⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ [ op ⦅ Ms ⦆ / x ] σ)} {σ'}
               {rs _ (measure3{eqs}{σ'} x∉M)}
               ((insert-subst {x}{op ⦅ Ms ⦆}{σ}{eqs} x∉M (M∪x∪eqs {op ⦅ Ms ⦆}{x}{eqs}{σ} eqs∩domσ⊆∅) Sσ))
               (eqs∩x∪σ⊆∅ {x}{op ⦅ Ms ⦆}{σ}{eqs} x∉M (M∪x∪eqs {op ⦅ Ms ⦆}{x}{eqs}{σ} eqs∩domσ⊆∅))
               unify[eqs,σ]≡σ'
  ... | ⟨ σ'[M/x]eqs , ⟨ σ'xM , σ'[M/x]σ ⟩ ⟩ =
      ⟨ ⟨ G1a , G1b ⟩ , G2 ⟩
      where
      G1a : subst σ' (op ⦅ Ms ⦆) ≡ subst σ' (` x)
      G1a = sym σ'xM
      G1b : σ' unifies eqs
      G1b = subst-reflect σ'[M/x]eqs σ'xM
      G2 : σ' unifies σ
      G2 = subst-reflect σ'[M/x]σ σ'xM
  unify-rec-sound {⟨ op ⦅ Ms ⦆ , op' ⦅ Ls ⦆ ⟩ ∷ eqs} {σ} {σ'}{acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡σ'
      with op-eq? op op'
  ... | yes refl
      with unify-rec-sound {append-eqs Ms Ls eqs}{σ}{σ'}{rs _ (measure4{eqs}{σ'})} Sσ
               (MsLseqs∩domσ⊆∅ {Ms = Ms}{Ls = Ls}{σ = σ} eqs∩domσ⊆∅) unify[eqs,σ]≡σ'
  ... | ⟨ σ'Ms,Ls,eqs , σ'σ ⟩
      with subst-vec-reflect {Ms = Ms}{Ls} σ'Ms,Ls,eqs
  ... | ⟨ σ'Ms=σ'Ls , σ'eqs ⟩ =
      ⟨ ⟨ G1a  , G1b ⟩ , G2 ⟩
      where
      G1a : (op ⦅ subst-vec σ' Ms ⦆) ≡ (op ⦅ subst-vec σ' Ls ⦆)
      G1a = cong (λ □ → op ⦅ □ ⦆) σ'Ms=σ'Ls
      G1b : σ' unifies eqs
      G1b = σ'eqs
      G2 : σ' unifies σ
      G2 = σ'σ
  unify-rec-sound {⟨ op ⦅ Ms ⦆ , op' ⦅ Ls ⦆ ⟩ ∷ eqs} {σ} {σ'}{acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡σ'
      | no neq
      with unify[eqs,σ]≡σ'
  ... | ()    
```

We use induction on the same measure that was used for proving the
termination of `unify-rec`.  We proceed by cases on the equations
`eqs`.

* If there are no more equations, then we trivially have `σ unifies []`
  and we have `σ unifies σ` because the `unifies` relation is
  reflexive (Lemma `unifies-refl`).

* If there are some equations to process, we proceed by cases on the
  first one.

    * Case `(x ≐ x) ∷ eqs`. 
        We need to show that

            (1a) subst σ' x ≡ subst σ' x
            (1b) σ' unifies eqs
            (2) σ' unifies σ

       (1a) is proved by refl.  We invoke the induction hypothesis,
       using lemmas `measure1` and `xx-eqs∩dom⊆∅` to satify its
       premises, to obtain (1b) and (2).
     
    * Case `(x ≐ y) ∷ eqs` and `x ≢ y`.
        We need to show that

            (1a) subst σ' x ≡ subst σ' y
            (1b) σ' unifies eqs
            (2) σ' unifies σ

        We invoke the induction hypothesis, using lemmas `measure2`,
        `insert-subst`, and `eqs∩x∪σ⊆∅` to satisfy its premises, to
        obtain

            (3) σ' unifies ([ y / x ] eqs)
            (4a) subst σ' x ≡ subst σ' y
            (4b) σ' unifies [ y / x ] σ

        So (1a) is satisfied by (4a).
        We prove (1b) by lemma `subst-reflect`, using (3) and (4a).
        We also prove (2) by lemma `subst-reflect`, using (4b) and (4a).

    * Cases `(x ≐ M) ∷ eqs` and `(M ≐ x) ∷ eqs` where `M ≡ op ⦅ Ms ⦆`.
        If `x ∈ vars M`, then `unify-rec eqs σ ac ≡ no-solution`, but that contradicts
        the premise that `unify-rec eqs σ ac ≡ finished σ'`.
        So `x ∉ vars M`. The proofs proceeds similarly to the case for `x ≐ y`.
        We need to show that

            (1a) subst σ' x ≡ subst σ' M
            (1b) σ' unifies eqs
            (2) σ' unifies σ

        We invoke the induction hypothesis, using lemmas `measure2`,
        `insert-subst`, and `eqs∩x∪σ⊆∅` to satisfy its premises,
        to obtain
        
            (3) σ' unifies ([ M / x ] eqs)
            (4a) subst σ' x ≡ subst σ' M
            (4b) σ' unifies [ M / x ] σ

        So (1a) is satisfied by (4a).
        We prove (1b) by lemma `subst-reflect`, using (3) and (4a).
        We also prove (2) by lemma `subst-reflect`, using (4b) and (4a).

    * Case (`op ⦅ Ms ⦆ ≐ op' ⦅ Ls ⦆)`.
        If `op ≢ op'`, then we have `unify-rec eqs σ ac ≡ no-solution`, but that contradicts
        the premise that `unify-rec eqs σ ac ≡ finished σ'`. So `op ≡ op'`.
        
        We need to show that

            (1a) subst σ' (op ⦅ Ms ⦆) ≡ subst σ' (op ⦅ Ls ⦆)
            (1b) σ' unifies eqs
            (2) σ' unifies σ

        We invoke the induction hypothesis, using lemmas `measure4` and
        `MsLseqs∩domσ⊆∅` to satisfy its premises,
        to obtain
        
            (3) σ' unifies append-eqs Ms Ls eqs
            (4) σ' unifies σ

        So (2) is satisfied by (4).
        We apply lemma `subst-vec-reflect` to (3) to obtain (1a) and (1b).

The soundness theorem follows directly from `unify-rec-sound`.

```
unify-sound : ∀ eqs σ
   → unify eqs ≡ finished σ
   → σ unifies eqs
unify-sound eqs σ unify-eqs-σ =
    proj₁ (unify-rec-sound {eqs}{[]}{σ}{M} empty G unify-eqs-σ)
    where
    M : Acc _<₃_ (measure eqs [])
    M = <₃-wellFounded (measure eqs [])
    G : vars-eqs eqs ∩ ∅ ⊆ ∅
    G rewrite p∩∅≡∅ (vars-eqs eqs) = λ z → z
```

We turn to the proof of the completeness theorem.  The proof is quite
similar to the soundness theorem.  We first prove a completeness lemma
for `unify-rec` and the completeness theorem is a corollary.  For
`unify-rec`, we shall prove that if `unify-rec eqs σ ac ≡ no-solution`
then there is no substitution θ that unifies eqs and σ. This proof is
quite similar to the proof of the soundness lemma for `unify-rec`.  We
again use induction on the same measure that was used for proving the
termination of `unify-rec` and we proceed by cases on the equations
`eqs`.  The proofs differ primarily in two respects.

1. In the cases where `unify-rec` returns `no-solution` we have to
   show that no solution exists. In particular, if the occurs-check
   fails, then we use lemma `occurs-no-soln`. If the operators are not
   equal (`op ⦅ Ms ⦆ ≐ op' ⦅ Ls ⦆` and `op ≢ op'`), then we
   immediately have a contradction.

2. Instead of using the lemma that says substitution reflects unifiers, we
   use the lemma that says substitution preserves unifiers.

```
private
  unify-rec-complete : ∀{eqs}{σ}{ac}
     → IdemSubst σ
     → vars-eqs eqs ∩ dom σ ⊆ ∅
     → unify-rec eqs σ ac ≡ no-solution
     → ∀ θ → ¬ (θ unifies eqs × θ unifies σ)
  unify-rec-complete {⟨ ` x , ` y ⟩ ∷ eqs} {σ} {acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡no θ ⟨ ⟨ θxy , θeqs ⟩ , θσ ⟩
      with x ≟ y
  ... | yes refl =
      unify-rec-complete {eqs}{σ} {rs _ (measure1 {eqs}{θ})}
          Sσ (xx-eqs∩dom⊆∅ {x}{eqs}{σ} eqs∩domσ⊆∅) unify[eqs,σ]≡no θ ⟨ θeqs , θσ ⟩ 
  ... | no xy =
      let eqs' = [ ` y / x ] eqs in
      let σ' = ⟨ ` x , ` y ⟩ ∷ [ ` y / x ] σ in
      unify-rec-complete {eqs'}{σ'}{rs _ (measure2{eqs}{θ} (x∉⁅y⁆ _ _ xy))}
          (insert-subst {x}{` y}{σ}{eqs} (x∉⁅y⁆ x y xy) eqs∩domσ⊆∅ Sσ)
          (eqs∩x∪σ⊆∅ {x}{` y}{σ}{eqs} (x∉⁅y⁆ x y xy) eqs∩domσ⊆∅)
          unify[eqs,σ]≡no θ ⟨ subst-pres θxy θeqs , ⟨ θxy , (subst-pres θxy θσ) ⟩ ⟩
  unify-rec-complete {⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ eqs} {σ} {acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡no θ ⟨ ⟨ θxM , θeqs ⟩ , θσ ⟩
      with occurs? x (op ⦅ Ms ⦆)
  ... | yes x∈M = occurs-no-soln {M = op ⦅ Ms ⦆} x∈M tt θxM
  ... | no x∉M =
      let eqs' = [ op ⦅ Ms ⦆ / x ] eqs in
      let σ' = ⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ [ op ⦅ Ms ⦆ / x ] σ in
      unify-rec-complete {eqs'}{σ'}{rs _ (measure2{eqs}{θ} x∉M)}
          (insert-subst {x}{op ⦅ Ms ⦆}{σ}{eqs} x∉M eqs∩domσ⊆∅ Sσ)
          (eqs∩x∪σ⊆∅ {x}{op ⦅ Ms ⦆}{σ}{eqs} x∉M eqs∩domσ⊆∅)
          unify[eqs,σ]≡no θ ⟨ subst-pres θxM θeqs , ⟨ θxM , (subst-pres θxM θσ) ⟩ ⟩
  unify-rec-complete {⟨ op ⦅ Ms ⦆ , ` x ⟩ ∷ eqs} {σ} {acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡no θ ⟨ ⟨ θMx , θeqs ⟩ , θσ ⟩
      with occurs? x (op ⦅ Ms ⦆)
  ... | yes x∈M = occurs-no-soln {M = op ⦅ Ms ⦆} x∈M tt (sym θMx)
  ... | no x∉M =
      let eqs' = [ op ⦅ Ms ⦆ / x ] eqs in
      let σ' = ⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ [ op ⦅ Ms ⦆ / x ] σ in
      unify-rec-complete {eqs'}{σ'}{rs _ (measure3{eqs}{θ} x∉M)}
          (insert-subst {x}{op ⦅ Ms ⦆}{σ}{eqs} x∉M (M∪x∪eqs {op ⦅ Ms ⦆}{x}{eqs}{σ} eqs∩domσ⊆∅) Sσ)
          (eqs∩x∪σ⊆∅ {x}{op ⦅ Ms ⦆}{σ}{eqs} x∉M (M∪x∪eqs {op ⦅ Ms ⦆}{x}{eqs}{σ} eqs∩domσ⊆∅))
          unify[eqs,σ]≡no θ ⟨ subst-pres (sym θMx) θeqs , ⟨ (sym θMx) , (subst-pres (sym θMx) θσ) ⟩ ⟩
  unify-rec-complete {⟨ op ⦅ Ms ⦆ , op' ⦅ Ls ⦆ ⟩ ∷ eqs} {σ} {acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡no θ ⟨ ⟨ θML , θeqs ⟩ , θσ ⟩
      with op-eq? op op'
  ... | yes refl =    
      unify-rec-complete {append-eqs Ms Ls eqs}{σ}{rs _ (measure4{eqs}{θ})} Sσ
          (MsLseqs∩domσ⊆∅ {Ms = Ms}{Ls = Ls}{σ = σ} eqs∩domσ⊆∅) unify[eqs,σ]≡no θ
          ⟨ append-pres {Ms = Ms}{Ls = Ls} θeqs (Ms≡-inversion θML) , θσ ⟩
  unify-rec-complete {⟨ op ⦅ Ms ⦆ , op' ⦅ Ls ⦆ ⟩ ∷ eqs} {σ} {acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡no θ ⟨ ⟨ θML , θeqs ⟩ , θσ ⟩
      | no neq = neq (op≡-inversion θML)
```

The completeness theorem for `unify` follows directly from the
lemma `unify-rec-complete`.

```
unify-complete :  ∀ eqs
   → unify eqs ≡ no-solution
   → ∀ θ → ¬ θ unifies eqs
unify-complete eqs unify[eqs]=no θ θeqs =
    unify-rec-complete {eqs}{[]}{M} empty G unify[eqs]=no θ ⟨ θeqs , tt ⟩
    where
    M : Acc _<₃_ (measure eqs [])
    M = (<₃-wellFounded (measure eqs []))
    G : vars-eqs eqs ∩ ∅ ⊆ ∅
    G rewrite p∩∅≡∅ (vars-eqs eqs) = λ z → z
```



