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

open import FirstOrderTerms Op op-eq? arity public
```

## Introduction to Unification

This chapter lays the groundwork for Chapter
[HM-TypeInference](https://plfa.github.io/HM-TypeInference)
on Hindley-Milner type inference. In that chapter,
we produce equations over types, such as

    α = β ⇒ Nat
    Nat = β

where the α and β are _unknown type variables_ that need to be solved
for.  For the above example, a solution is

    α = Nat ⇒ Nat
    β = Nat

In general, equations over syntactic structures can be solved using
unification algorithms. In this chapter we study a particularly lucid
algorithm by Martelli and Montanari. It is not the most efficient
algorithm for unification; see the Chapter Notes for pointers to those
algorithms.


```
Equations : Set
Equations = List (AST × AST)
```

Definition of what it means to unify a list of equations.

```
_unifies_ : Equations → Equations → Set
θ unifies [] = ⊤
θ unifies (⟨ M , L ⟩ ∷ eqs) = subst θ M ≡ subst θ L  ×  θ unifies eqs
```

## Properties of Unifiers


### Unifies is reflexive

```
ext-subst : ∀{θ}{x}{M}{L}
   → x ∉ vars L
   → x ∉ vars-eqs θ
   → subst (⟨ ` x , M ⟩ ∷ θ) L ≡ subst θ L
ext-subst-vec : ∀{θ}{x}{M}{n}{Ls : Vec AST n}
   → x ∉ vars-vec Ls
   → x ∉ vars-eqs θ
   → subst-vec (⟨ ` x , M ⟩ ∷ θ) Ls ≡ subst-vec θ Ls

ext-subst {θ} {x} {M} {` y} x∉L x∉θ
    with x ≟ y
... | yes refl = ⊥-elim (x∉L (x∈⁅x⁆ x))
... | no xy = G
    where
    G : subst (⟨ ` x , M ⟩ ∷ θ) (` y)  ≡ subst θ (` y)
    G
        with y ≟ x
    ... | yes refl = ⊥-elim (xy refl)
    ... | no yx = refl
ext-subst {θ} {x} {M} {op ⦅ Ls ⦆} x∉L x∉θ = cong (λ □ → op ⦅ □ ⦆) (ext-subst-vec {θ}{x}{M}{Ls = Ls} x∉L x∉θ)

ext-subst-vec {θ} {x} {M} {zero} {Ls} x∉Ls x∉θ = refl
ext-subst-vec {θ} {x} {M} {suc n} {L ∷ Ls} x∉L∪Ls x∉θ =
    cong₂ _∷_ (ext-subst {θ}{x}{M}{L} (λ x∈L → x∉L∪Ls (p⊆p∪q (vars L) (vars-vec Ls) x∈L)) x∉θ)
              (ext-subst-vec {θ} {x} {M} {n} {Ls} (λ x∈Ls → x∉L∪Ls (q⊆p∪q (vars L) (vars-vec Ls) x∈Ls)) x∉θ)
```

```
no-vars→ext-unifies : ∀{θ}{x}{M}{eqs}
   → θ unifies eqs
   → x ∉ vars-eqs eqs
   → x ∉ vars-eqs θ
   → (⟨ ` x , M ⟩ ∷ θ) unifies eqs
no-vars→ext-unifies {θ} {x} {M} {[]} θeqs x∉eqs x∉θ = tt
no-vars→ext-unifies {θ} {x} {M} {⟨ L , N ⟩ ∷ eqs} ⟨ θL=θN , θeqs ⟩ x∉L∪N∪eqs x∉θ =
  let IH = no-vars→ext-unifies {θ} {x} {M} {eqs} θeqs x∉eqs x∉θ in
  ⟨ L=N , IH ⟩
    where
    x∉L : x ∉ vars L
    x∉L = λ x∈L → x∉L∪N∪eqs (p⊆p∪q (vars L) (vars N ∪ vars-eqs eqs) x∈L ) 
    x∉N : x ∉ vars N
    x∉N = λ x∈N →
        let x∈L∪N∪eqs = p⊆r→p⊆q∪r _ _ _ (p⊆p∪q _ _) x∈N in
        x∉L∪N∪eqs x∈L∪N∪eqs
    x∉eqs : x ∉ vars-eqs eqs
    x∉eqs = λ x∈eqs →
      let x∈L∪N∪eqs = p⊆r→p⊆q∪r _ _ _ (p⊆r→p⊆q∪r _ _ _ ⊆-refl) x∈eqs in
      x∉L∪N∪eqs x∈L∪N∪eqs
    L=N : subst (⟨ ` x , M ⟩ ∷ θ) L ≡ subst (⟨ ` x , M ⟩ ∷ θ) N
    L=N = begin
        subst (⟨ ` x , M ⟩ ∷ θ) L     ≡⟨ ext-subst {θ}{x}{M}{L} x∉L x∉θ ⟩
        subst θ L                     ≡⟨ θL=θN ⟩
        subst θ N                     ≡⟨ sym (ext-subst {θ}{x}{M}{N} x∉N x∉θ) ⟩
        subst (⟨ ` x , M ⟩ ∷ θ) N
        ∎
```

```

unifies-refl : ∀{θ} → IdemSubst θ → θ unifies θ
unifies-refl {[]} empty = tt
unifies-refl {⟨ ` x , M ⟩ ∷ θ} (insert x∉M x∉θ M∩θ⊆∅ SΘ) =
    ⟨ G1 , G2 ⟩
    where
    IH : θ unifies θ
    IH = unifies-refl {θ} SΘ 
    H : vars M ∩ (⁅ x ⁆ ∪ dom θ) ⊆ ∅
    H {y} y∈
        rewrite ∪-distribˡ-∩ {vars M} {⁅ x ⁆} {dom θ}
        with (proj₁ (∈∪ _ _ _)) y∈
    ... | inj₁ y∈Mx
        with (proj₁ (∈∩ _ _ _)) y∈Mx
    ... | ⟨ y∈M , y∈x ⟩
        with x∈⁅y⁆→x≡y _ _ y∈x
    ... | refl = ⊥-elim (x∉M y∈M)
    H {y} y∈
        | inj₂ y∈M∩θ = M∩θ⊆∅ y∈M∩θ
    G1 : subst (⟨ ` x , M ⟩ ∷ θ) (` x) ≡ subst (⟨ ` x , M ⟩ ∷ θ) M
    G1 = begin
        subst (⟨ ` x , M ⟩ ∷ θ) (` x)     ≡⟨ subst-var-eq {x}{M}{θ} ⟩
        M                                 ≡⟨ sym (M∩domθ⊆∅→subst-id (insert x∉M x∉θ M∩θ⊆∅ SΘ) H) ⟩
        subst (⟨ ` x , M ⟩ ∷ θ) M
        ∎

    G2 : (⟨ ` x , M ⟩ ∷ θ) unifies θ
    G2 = no-vars→ext-unifies IH x∉θ x∉θ
```

### Substitution preserves unifiers

```
subst-vec-sub1 : ∀{n}{Ns : Vec AST n}{z}{θ}{M}
  → subst θ (` z) ≡ subst θ M
  → subst-vec θ Ns ≡ subst-vec θ ([ z ::= M ] Ns)

subst-sub1 : ∀{N}{z}{θ}{M}
  → subst θ (` z) ≡ subst θ M
  → subst θ N ≡ subst θ ([ z := M ] N)
subst-sub1 {` x} {z} {θ} {M} θzM
    with z ≟ x
... | yes refl = θzM
... | no zx = refl
subst-sub1 {op ⦅ Ns ⦆} {z} {θ} {M} θzM =
    cong (λ □ → op ⦅ □ ⦆) (subst-vec-sub1 θzM)

subst-vec-sub1 {zero} {Ns} θzM = refl
subst-vec-sub1 {suc n} {N ∷ Ns}{z}{θ}{M} θzM
    rewrite subst-sub1 {N}{z}{θ}{M} θzM
    | subst-vec-sub1 {n} {Ns}{z}{θ}{M} θzM = refl
```

```
subst-sub : ∀{L}{N}{z}{θ}{M}
  → subst θ (` z) ≡ subst θ M
  → subst θ L ≡ subst θ N
  → subst θ ([ z := M ] L) ≡ subst θ ([ z := M ] N)
subst-sub {L}{N}{z}{θ}{M} θzM θLM =   begin
    subst θ ([ z := M ] L)    ≡⟨ sym (subst-sub1 {L} θzM) ⟩
    subst θ L                 ≡⟨ θLM ⟩
    subst θ N                 ≡⟨ subst-sub1 {N} θzM ⟩
    subst θ ([ z := M ] N)    ∎
```

```
subst-pres : ∀{eqs θ x M}
  → subst θ (` x) ≡ subst θ M
  → θ unifies eqs
  → θ unifies ([ M / x ] eqs)
subst-pres {[]} eq θeqs = tt
subst-pres {⟨ L , N ⟩ ∷ eqs} {θ}{x}{M} eq ⟨ θLM , θeqs ⟩ =
  ⟨ subst-sub {L = L}{N = N} eq θLM , (subst-pres {eqs} eq θeqs) ⟩
```

```
subst-vec-pres : ∀{n}{Ms Ls : Vec AST n}{eqs}{θ}
   → θ unifies eqs
   → subst-vec θ Ms ≡ subst-vec θ Ls
   → θ unifies append-eqs Ms Ls eqs
subst-vec-pres {zero} {Ms} {Ls} θeqs θMsLs = θeqs
subst-vec-pres {suc n} {M ∷ Ms} {L ∷ Ls} θeqs θMLMsLs
    with ∷≡-inversion θMLMsLs
... | ⟨ θML , θMsLs ⟩ = ⟨ θML , (subst-vec-pres θeqs θMsLs) ⟩
```

### Substitution reflects unifiers

```
subst-ref : ∀{L}{N}{z}{θ}{M}
  → subst θ (` z) ≡ subst θ M
  → subst θ ([ z := M ] L) ≡ subst θ ([ z := M ] N)
  → subst θ L ≡ subst θ N
subst-ref {L}{N}{z}{θ}{M} θzM θLM = begin
    subst θ L                ≡⟨ subst-sub1 {L} θzM ⟩
    subst θ ([ z := M ] L)   ≡⟨ θLM ⟩
    subst θ ([ z := M ] N)   ≡⟨ sym (subst-sub1 {N} θzM) ⟩
    subst θ N   ∎
```

```
subst-reflect : ∀{eqs θ x M}
  → θ unifies ([ M / x ] eqs)
  → subst θ (` x) ≡ subst θ M
  → θ unifies eqs
subst-reflect {[]} {θ} {x} {M} θ[M/x]eqs θx=θM = tt
subst-reflect {⟨ L , N ⟩ ∷ eqs} {θ} {x} {M} ⟨ θ[x:=M]L=θ[x:=M]N , θ[M/x]eqs ⟩ θx=θM =
    ⟨ subst-ref {L = L}{N} θx=θM θ[x:=M]L=θ[x:=M]N , subst-reflect {eqs}{θ}{x}{M} θ[M/x]eqs θx=θM ⟩
```

```
subst-vec-reflect : ∀{n}{Ms Ls : Vec AST n}{eqs}{θ}
   → θ unifies append-eqs Ms Ls eqs
   → (subst-vec θ Ms ≡ subst-vec θ Ls)  × θ unifies eqs
subst-vec-reflect {zero} {[]} {[]} {eqs} {θ} θMs,Ls,eqs = ⟨ refl , θMs,Ls,eqs ⟩
subst-vec-reflect {suc n} {M ∷ Ms} {L ∷ Ls} {eqs} {θ} ⟨ θM=θL , θMs,Ls,eqs ⟩ 
    with subst-vec-reflect {n} {Ms} {Ls} {eqs} {θ} θMs,Ls,eqs
... | ⟨ θMs=θLs , θeqs ⟩ =     
    ⟨ cong₂ _∷_ θM=θL θMs=θLs , θeqs ⟩
```

### A failed occurs-check implies no solutions

```
num-ops-vec : ∀{n} → Vec AST n → ℕ

num-ops : AST → ℕ
num-ops (` x) = 0
num-ops (op ⦅ Ms ⦆) = suc (num-ops-vec Ms)

num-ops-vec {zero} Ms = 0
num-ops-vec {suc n} (M ∷ Ms) = num-ops M + num-ops-vec Ms

num-ops-eqs : Equations → ℕ
num-ops-eqs [] = 0
num-ops-eqs (⟨ L , M ⟩ ∷ eqs) = num-ops L + num-ops M + num-ops-eqs eqs

is-op : AST → Set
is-op (` x) = ⊥
is-op (op ⦅ Ms ⦆) = ⊤

num-ops-less-vec : ∀ {n}{Ms : Vec AST n}{x θ}
   → x ∈ vars-vec Ms
   → num-ops (subst θ (` x)) ≤ num-ops-vec (subst-vec θ Ms)

num-ops-less : ∀ {M}{x θ}
   → x ∈ vars M
   → is-op M
   → num-ops (subst θ (` x)) < num-ops (subst θ M)
num-ops-less {op ⦅ Ms ⦆}{x}{θ} x∈Ms opM =
   s≤s (num-ops-less-vec {Ms = Ms}{x}{θ} x∈Ms)

num-ops-less-vec {zero} {[]} {x} {θ} x∈Ms = ⊥-elim (∉∅ {x} x∈Ms)
num-ops-less-vec {suc n} {(` y) ∷ Ms} {x} {θ} x∈MMs
    with ∈p∪q→∈p⊎∈q x∈MMs
... | inj₁ x∈M
    with x ≟ y
... | yes refl = m≤m+n (num-ops (subst θ (` y))) (num-ops-vec (subst-vec θ Ms))
... | no xy = ⊥-elim ((x∉⁅y⁆ x y xy) x∈M)
num-ops-less-vec {suc n} {(` y) ∷ Ms} {x} {θ} x∈MMs
    | inj₂ x∈Ms =
    let IH = num-ops-less-vec {n} {Ms}{x}{θ} x∈Ms in
    begin≤
    num-ops (subst θ (` x))         ≤⟨ IH ⟩
    num-ops-vec (subst-vec θ Ms)    ≤⟨ m≤n+m _ _ ⟩
    num-ops (subst θ (` y)) + num-ops-vec (subst-vec θ Ms)
    QED
num-ops-less-vec {suc n} {(op ⦅ Ls ⦆) ∷ Ms} {x} {θ} x∈MMs
    with ∈p∪q→∈p⊎∈q x∈MMs
... | inj₁ x∈M =
    let θx<1+θLS = num-ops-less {(op ⦅ Ls ⦆)}{x}{θ} x∈M tt in
    begin≤
       num-ops (subst θ (` x))       ≤⟨ ≤-pred θx<1+θLS ⟩
       num-ops-vec (subst-vec θ Ls)  ≤⟨ m≤m+n _ _ ⟩
       num-ops-vec (subst-vec θ Ls) + num-ops-vec (subst-vec θ Ms) ≤⟨ n≤1+n _ ⟩
       suc (num-ops-vec (subst-vec θ Ls) + num-ops-vec (subst-vec θ Ms))
      QED
num-ops-less-vec {suc n} {M ∷ Ms} {x} {θ} x∈MMs
    | inj₂ x∈Ms =
    let IH = num-ops-less-vec {n} {Ms}{x}{θ} x∈Ms in
    begin≤
    num-ops (subst θ (` x))         ≤⟨ IH ⟩
    num-ops-vec (subst-vec θ Ms)    ≤⟨ m≤n+m _ _ ⟩
    num-ops (subst θ M) + num-ops-vec (subst-vec θ Ms)
    QED

occurs-no-soln : ∀{θ x M}
  → x ∈ vars M → is-op M
  → subst θ (` x) ≢ subst θ M
occurs-no-soln {θ} x∈M opM θxM
    with num-ops-less {θ = θ} x∈M opM
... | θx<θM rewrite θxM =
      ⊥-elim (1+n≰n θx<θM)
```




## Proof of Termination

We use well-founded recursion to define the unification function.  We
shall show that a lexicographic ordering of three numbers decreases
with each recursive call. The numbers are

1. the number of variables in the equations,
2. the number of operators (non-variable nodes) in the equations,
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

Substitution reduces the number of variables in an equation.

```
vars-eqs-sub-less : ∀{M x eqs}
   → ¬ x ∈ vars M
   → ∣ vars-eqs ([ M / x ] eqs) ∣ < ∣ ⁅ x ⁆ ∪ vars M ∪ vars-eqs eqs ∣
vars-eqs-sub-less {M}{x}{eqs} x∉M = begin≤
         suc ∣ vars-eqs ([ M / x ] eqs) ∣          ≤⟨ s≤s (p⊆q⇒∣p∣≤∣q∣ (vars-eqs-subst-∪ {eqs}{x}{M})) ⟩
         suc ∣ vars M ∪ (vars-eqs eqs - ⁅ x ⁆) ∣   ≤⟨ ≤-reflexive (cong (λ □ → suc ∣ □ ∣) (distrib-∪-2 (vars M) (vars-eqs eqs) ⁅ x ⁆ G2)) ⟩
         suc ∣ (vars M ∪ vars-eqs eqs) - ⁅ x ⁆ ∣   ≤⟨ ∣p-x∣<∣p∪x∣ (vars M ∪ vars-eqs eqs) x ⟩
         ∣ (vars M ∪ vars-eqs eqs) ∪ ⁅ x ⁆ ∣       ≤⟨ ≤-reflexive (cong (λ □ → ∣ □ ∣) (∪-comm _ _)) ⟩
         ∣ ⁅ x ⁆ ∪ vars M ∪ vars-eqs eqs ∣
         QED
    where
    G2 : vars M ∩ ⁅ x ⁆ ⊆ ∅
    G2 {z} z∈M∩x
        with x∈⁅y⁆→x≡y z x (∈p∩q→∈q z∈M∩x)
    ... | refl =
        let z∈M = ∈p∩q→∈p z∈M∩x in
        ⊥-elim (x∉M z∈M)
```



```
var-eqs-append-≡ : ∀ {n} (Ms Ls : Vec AST n) eqs
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

{- obsolete -}
var-eqs-append-⊆ : ∀ {n} (Ms Ls : Vec AST n) eqs
   → vars-eqs (append-eqs Ms Ls eqs) ⊆ vars-vec Ms ∪ vars-vec Ls ∪ vars-eqs eqs
var-eqs-append-⊆ {zero} [] [] eqs x∈eqs
    rewrite ∅∪p≡p (vars-eqs eqs) | ∅∪p≡p (vars-eqs eqs) = x∈eqs
var-eqs-append-⊆ {suc n} (M ∷ Ms) (L ∷ Ls) eqs {x} x∈M∪L∪app-Ms-Ls-eqs
    rewrite sym (∪-assoc (vars M) (vars L) (vars-eqs (append-eqs Ms Ls eqs)))
    with ∈p∪q→∈p⊎∈q x∈M∪L∪app-Ms-Ls-eqs
... | inj₁ x∈M∪L = sub x∈M∪L
    where
    sub : vars M ∪ vars L ⊆ (vars M ∪ vars-vec Ms) ∪ (vars L ∪ vars-vec Ls) ∪ vars-eqs eqs
    sub = p⊆r→q⊆r→p∪q⊆r _ _ _ (p⊆q→p⊆q∪r _ _ _ (p⊆q→p⊆q∪r _ _ _ ⊆-refl))
            (p⊆r→p⊆q∪r _ _ _ (p⊆q→p⊆q∪r _ _ _ (p⊆q→p⊆q∪r _ _ _ ⊆-refl)))
    
... | inj₂ x∈app-Ms-Ls-eqs
    rewrite ∪-assoc (vars L) (vars-vec Ls) (vars-eqs eqs)
    | ∪-assoc (vars M) (vars-vec Ms) (vars L ∪ vars-vec Ls ∪ vars-eqs eqs)
    | sym (∪-assoc (vars-vec Ms) (vars L) (vars-vec Ls ∪ vars-eqs eqs))
    | ∪-comm (vars-vec Ms) (vars L) 
    | ∪-assoc (vars L) (vars-vec Ms) (vars-vec Ls ∪ vars-eqs eqs)
    | sym (∪-assoc (vars M) (vars L) (vars-vec Ms ∪ vars-vec Ls ∪ vars-eqs eqs)) =
    let IH = var-eqs-append-⊆ {n} Ms Ls eqs {x} x∈app-Ms-Ls-eqs in
    q⊆p∪q (vars M ∪ vars L) (vars-vec Ms ∪ vars-vec Ls ∪ vars-eqs eqs) {x} IH 

open import Data.Nat.Solver using (module +-*-Solver)

num-ops-append : ∀ {n} (Ms Ls : Vec AST n) eqs
   → num-ops-eqs (append-eqs Ms Ls eqs) ≡ num-ops-vec Ms + num-ops-vec Ls + num-ops-eqs eqs
num-ops-append {zero} [] [] eqs = refl
num-ops-append {suc n} (M ∷ Ms) (L ∷ Ls) eqs
    rewrite num-ops-append {n} Ms Ls eqs = G (num-ops M) (num-ops L) (num-ops-vec Ms) (num-ops-vec Ls) (num-ops-eqs eqs)
    where
    open +-*-Solver
    G : (nM nL nMs nLs neqs : ℕ) → (nM + nL) + ((nMs + nLs) + neqs) ≡ ((nM + nMs) + (nL + nLs)) + neqs
    G = solve 5 (λ nM nL nMs nLs neqs →
          (nM :+ nL) :+ ((nMs :+ nLs) :+ neqs) := ((nM :+ nMs) :+ (nL :+ nLs)) :+ neqs) refl
```

```
measure1 : ∀{eqs}{θ}{x} → measure eqs θ <₃ measure (⟨ ` x , ` x ⟩ ∷ eqs) θ
measure1 {eqs}{θ}{x} = third-< vars≤ ≤-refl (s≤s (s≤s ≤-refl))
    where
    vars≤ : ∣ vars-eqs eqs ∣ ≤ ∣ vars-eqs (⟨ ` x , ` x ⟩ ∷ eqs) ∣
    vars≤ =                                       begin≤
          ∣ vars-eqs eqs ∣                         ≤⟨ ∣q∣≤∣p∪q∣ {⁅ x ⁆} {vars-eqs eqs} ⟩
          ∣ ⁅ x ⁆ ∪ vars-eqs eqs ∣                 ≤⟨ ∣q∣≤∣p∪q∣ {⁅ x ⁆} {⁅ x ⁆ ∪  vars-eqs eqs} ⟩
          ∣ ⁅ x ⁆ ∪ ⁅ x ⁆ ∪ vars-eqs eqs ∣         ≤⟨ ≤-refl ⟩
          ∣ vars-eqs (⟨ ` x , ` x ⟩ ∷ eqs) ∣       QED
```

```
measure2 : ∀{eqs}{θ}{M}{x}
   → x ∉ vars M
   → measure ([ M / x ] eqs) (⟨ ` x , M ⟩ ∷ [ M / x ] θ)
     <₃ measure (⟨ ` x , M ⟩ ∷ eqs) θ
measure2{eqs}{θ}{M}{x} x∉M = (first-< (vars-eqs-sub-less {M}{x}{eqs} x∉M))
```

```
measure3 : ∀{eqs}{θ}{op}{Ms}{x}
   → x ∉ vars (op ⦅ Ms ⦆)
   → measure  ([ op ⦅ Ms ⦆ / x ] eqs) (⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ [ op ⦅ Ms ⦆ / x ] θ)
     <₃ measure (⟨ op ⦅ Ms ⦆ , ` x ⟩ ∷ eqs) θ
measure3 {eqs}{θ}{op}{Ms}{x} x∉M
    with vars-eqs-sub-less {op ⦅ Ms ⦆}{x}{eqs} x∉M
... | vars< 
    rewrite sym (∪-assoc ⁅ x ⁆ (vars-vec Ms) (vars-eqs eqs))
    | ∪-comm ⁅ x ⁆ (vars-vec Ms)
    | ∪-assoc (vars-vec Ms) ⁅ x ⁆ (vars-eqs eqs) = 
   first-< vars< 
```

```
measure4 : ∀{eqs}{θ}{op}{Ms Ls : Vec AST (arity op)}
   → measure (append-eqs Ms Ls eqs) θ
     <₃ measure (⟨ op ⦅ Ms ⦆ , op ⦅ Ls ⦆ ⟩ ∷ eqs) θ
measure4 {eqs}{θ}{op}{Ms}{Ls} = second-< vars≤ ops<
    where
    vars≤ : ∣ vars-eqs (append-eqs Ms Ls eqs) ∣ ≤ ∣ vars-vec Ms ∪ vars-vec Ls ∪ vars-eqs eqs ∣
    vars≤ = p⊆q⇒∣p∣≤∣q∣ (var-eqs-append-⊆ Ms Ls eqs)
    
    ops< : num-ops-eqs (append-eqs Ms Ls eqs) < suc (num-ops-vec Ms + suc (num-ops-vec Ls) + num-ops-eqs eqs)
    ops< rewrite num-ops-append Ms Ls eqs
         | +-comm (num-ops-vec Ms) (suc (num-ops-vec Ls))
         | +-comm (num-ops-vec Ls) (num-ops-vec Ms) = s≤s (≤-step ≤-refl)

```

## The Unify Function



```
data Result : Set where
  finished : Equations → Result
  no-solution : Result

unify-rec : (eqs : Equations) → (θ : Equations)
          → Acc _<₃_ (measure eqs θ) → Result
unify-rec [] θ rec = finished θ
unify-rec (⟨ ` x , ` y ⟩ ∷ eqs) θ (acc rec)
    with x ≟ y
... | yes refl = unify-rec eqs θ (rec _ (measure1 {eqs}{θ}))
... | no xy =
    let eqs' = [ ` y / x ] eqs in
    let θ' = ⟨ ` x , ` y ⟩ ∷ [ ` y / x ] θ in
    unify-rec eqs' θ' (rec _ (measure2{eqs}{θ} (x∉⁅y⁆ _ _ xy)))
unify-rec (⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ eqs) θ (acc rec)
    with occurs? x (op ⦅ Ms ⦆)
... | yes x∈M = no-solution
... | no x∉M =
    let eqs' = [ op ⦅ Ms ⦆ / x ] eqs in
    let θ' = ⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ [ op ⦅ Ms ⦆ / x ] θ in
    unify-rec eqs' θ' (rec _ (measure2{eqs}{θ} x∉M))
unify-rec (⟨ op ⦅ Ms ⦆ , ` x ⟩ ∷ eqs) θ (acc rec)
    with occurs? x (op ⦅ Ms ⦆)
... | yes x∈M = no-solution
... | no x∉M =
    let eqs' = [ op ⦅ Ms ⦆ / x ] eqs in
    let θ' = ⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ [ op ⦅ Ms ⦆ / x ] θ in
    unify-rec eqs' θ' (rec _ (measure3{eqs}{θ} x∉M))
unify-rec (⟨ op ⦅ Ms ⦆ , op' ⦅ Ls ⦆ ⟩ ∷ eqs) θ (acc rec)
    with op-eq? op op'
... | yes refl = unify-rec (append-eqs Ms Ls eqs) θ (rec _ (measure4 {eqs}{θ}))
... | no neq = no-solution

unify : (eqs : Equations) → Result
unify eqs = unify-rec eqs [] (<₃-wellFounded (measure eqs []))
```

## Proof that Unify is Correct

We shall prove that the `unify` function is correct in that

1. (Soundness) If it returns a substitution θ, then θ unifies the equations.
2. (Completeness) if it returns `no-solution`, then
   there are no substitutions that unify the equations.

The `unify` function merely kicks things off, and all the real
work is done in `unify-rec`. So we shall prove a soundness lemma
and a compelteness lemma for `unify-rec`.

The `unify-rec` function has two preconditions:

1. the current substitution θ is idempotent, and
2. the current equations no longer contain the variables in the domain of θ.

In the proofs of soundness and completeness, to invoke the induction
hypothesis, we need to establish the above two preconditions for the
new substitution and the new set of equations. Regarding idempotency,
we shall use the `insert-subst` lemma from the module
[`TermSubstUnify`](./TermSubstUnify.lagda.md). To satisfy one of the
premises of that lemma, we sometimes need the following simple lemma
that commutes the union of two sets.

```
M∪x∪eqs : ∀ {M}{x}{eqs}{σ}
   → (vars M ∪ ⁅ x ⁆ ∪ vars-eqs eqs) ∩ dom σ ⊆ ∅
   → (⁅ x ⁆ ∪ vars M ∪ vars-eqs eqs) ∩ dom σ ⊆ ∅
M∪x∪eqs {M}{x}{eqs}{σ} prem
    rewrite sym (∪-assoc (vars M) ⁅ x ⁆ (vars-eqs eqs))
    | ∪-comm (vars M) ⁅ x ⁆
    | ∪-assoc ⁅ x ⁆ (vars M) (vars-eqs eqs)
    = prem
```

We have some work to do regarding point 2 (that the current equations
does not contain any variables in the domain of θ).

UNDER CONSTRUCTION

```
xx-eqs∩dom⊆∅ : ∀ {x eqs σ}
   → (⁅ x ⁆ ∪ ⁅ x ⁆ ∪ vars-eqs eqs) ∩ dom σ ⊆ ∅
   → vars-eqs eqs ∩ dom σ ⊆ ∅
xx-eqs∩dom⊆∅ {x}{eqs}{σ} prem
    rewrite sym (∪-assoc ⁅ x ⁆ ⁅ x ⁆ (vars-eqs eqs)) =
    begin⊆
    vars-eqs eqs ∩ dom σ                        ⊆⟨ p⊆r→q⊆s→p∩q⊆r∩s (q⊆p∪q _ _) ⊆-refl  ⟩
    ((⁅ x ⁆ ∪ ⁅ x ⁆) ∪ vars-eqs eqs) ∩ dom σ    ⊆⟨ prem ⟩
    ∅
    ■
```

```
[x∪p]∩q⊆∅→x∉q : ∀{x p q} → (⁅ x ⁆ ∪ p) ∩ q ⊆ ∅ → x ∉ q
[x∪p]∩q⊆∅→x∉q {x}{p}{q} xpq x∈q =
    let x∈∅ = xpq {x} (proj₂ (∈∩ _ _ _) ⟨ (p⊆p∪q _ _ (x∈⁅x⁆ x)) , x∈q ⟩) in
    ⊥-elim (∉∅ x∈∅)

eqs∩x∪σ⊆∅ : ∀{x}{M}{σ}{eqs}
   → x ∉ vars M
   → (⁅ x ⁆ ∪ vars M ∪ vars-eqs eqs) ∩ dom σ ⊆ ∅
   → vars-eqs ([ M / x ] eqs) ∩ (⁅ x ⁆ ∪ dom ([ M / x ] σ)) ⊆ ∅
eqs∩x∪σ⊆∅ {x}{M}{σ}{eqs} x∉M eqs∩domσ⊆∅ {y} y∈
    rewrite subst-dom {x}{M}{σ} ([x∪p]∩q⊆∅→x∉q eqs∩domσ⊆∅)
    with proj₁ (∈∩ y _ _) y∈
... | ⟨ y∈[M/x]eqs , y∈[x]∪domσ ⟩
    with proj₁ (∈∪ y _ _) (vars-eqs-subst-∪ {eqs}{x}{M} y∈[M/x]eqs)
... | inj₂ y∈eqs-x
    with proj₁ (∈∪ y _ _) y∈[x]∪domσ
... | inj₁ y∈[x] rewrite (x∈⁅y⁆→x≡y _ _ y∈[x]) = ⊥-elim (x∉p-⁅x⁆ _ _ y∈eqs-x)
... | inj₂ y∈domσ = eqs∩domσ⊆∅ {y} (proj₂ (∈∩ y _ _) ⟨ y∈[x]∪M∪eqs , y∈domσ ⟩)
    where
    y∈eqs : y ∈ vars-eqs eqs
    y∈eqs = p-q⊆p _ _ y∈eqs-x
    y∈[x]∪M∪eqs : y ∈ ⁅ x ⁆ ∪ vars M ∪ vars-eqs eqs
    y∈[x]∪M∪eqs = p⊆r→p⊆q∪r _ _ _ (q⊆p∪q _ _) y∈eqs
eqs∩x∪σ⊆∅ {x}{M}{σ}{eqs} x∉M eqs∩domσ⊆∅ {y} y∈
    | ⟨ y∈[M/x]eqs , y∈[x]∪domσ ⟩
    | inj₁ y∈M
    with proj₁ (∈∪ y _ _) y∈[x]∪domσ
... | inj₁ y∈[x] rewrite x∈⁅y⁆→x≡y _ _ y∈[x] = ⊥-elim (x∉M y∈M)
... | inj₂ y∈domσ = eqs∩domσ⊆∅ {y} (proj₂ (∈∩ y _ _) ⟨ G , y∈domσ ⟩)
    where
    G : y ∈ ⁅ x ⁆ ∪ vars M ∪ vars-eqs eqs
    G = p⊆r→p⊆q∪r _ _ _ (p⊆p∪q _ _) y∈M
```


```
MsLseqs∩domσ⊆∅ : ∀{n}{Ms Ls : Vec AST n}{eqs}{σ}
   → (vars-vec Ms ∪ vars-vec Ls ∪ vars-eqs eqs) ∩ dom σ ⊆ ∅
   → vars-eqs (append-eqs Ms Ls eqs) ∩ dom σ ⊆ ∅
MsLseqs∩domσ⊆∅ {n}{Ms}{Ls}{eqs}{σ} prem =
   begin⊆
     vars-eqs (append-eqs Ms Ls eqs) ∩ dom σ              ⊆⟨ p⊆r→q⊆s→p∩q⊆r∩s (var-eqs-append-⊆ Ms Ls eqs) ⊆-refl ⟩
     (vars-vec Ms ∪ vars-vec Ls ∪ vars-eqs eqs) ∩ dom σ   ⊆⟨ prem ⟩
     ∅
   ■
```



```
unify-rec-sound : ∀{eqs}{σ}{θ}{ac}
   → IdemSubst σ
   → vars-eqs eqs ∩ dom σ ⊆ ∅
   → unify-rec eqs σ ac ≡ finished θ
   → θ unifies eqs × θ unifies σ
unify-rec-sound {[]} {σ}{θ}{ac} Sσ eqs∩domσ⊆∅ refl = ⟨ tt , unifies-refl Sσ ⟩
unify-rec-sound {⟨ ` x , ` y ⟩ ∷ eqs} {σ} {θ} {acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡θ
    with x ≟ y 
... | yes refl
    with unify-rec-sound {eqs}{σ}{θ} {rs _ (measure1 {eqs}{θ})}
            Sσ (xx-eqs∩dom⊆∅ {x}{eqs}{σ} eqs∩domσ⊆∅) unify[eqs,σ]≡θ
... | ⟨ θeqs , θσ ⟩ =    
      ⟨ ⟨ refl , θeqs ⟩ , θσ ⟩
unify-rec-sound {⟨ ` x , ` y ⟩ ∷ eqs} {σ} {θ} {acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡θ
    | no xy
    with unify-rec-sound {[ ` y / x ] eqs}{(⟨ ` x , ` y ⟩ ∷ [ ` y / x ] σ)}{θ}
             {rs _ (measure2{eqs}{θ} (x∉⁅y⁆ _ _ xy))}
             (insert-subst {x}{` y}{σ}{eqs} (x∉⁅y⁆ x y xy) eqs∩domσ⊆∅ Sσ)
             (eqs∩x∪σ⊆∅ {x}{` y}{σ}{eqs} (x∉⁅y⁆ x y xy) eqs∩domσ⊆∅)
             unify[eqs,σ]≡θ
... | ⟨ θeqs , ⟨ θx=θy , θσ ⟩ ⟩ =     
       ⟨ ⟨ θx=θy , subst-reflect θeqs θx=θy ⟩ , subst-reflect θσ θx=θy ⟩
unify-rec-sound {⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ eqs} {σ} {θ}{acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡θ
    with occurs? x (op ⦅ Ms ⦆)
... | yes x∈M
    with unify[eqs,σ]≡θ
... | ()    
unify-rec-sound {⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ eqs} {σ} {θ}{acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡θ
    | no x∉M 
    with unify-rec-sound {([ op ⦅ Ms ⦆ / x ] eqs)} {(⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ [ op ⦅ Ms ⦆ / x ] σ)} {θ}
             {rs _ (measure2{eqs}{σ} x∉M)}
             (insert-subst {x}{op ⦅ Ms ⦆}{σ}{eqs} x∉M eqs∩domσ⊆∅ Sσ)
             (eqs∩x∪σ⊆∅ {x}{op ⦅ Ms ⦆}{σ}{eqs} x∉M eqs∩domσ⊆∅)
             unify[eqs,σ]≡θ
... | ⟨ θeqs , ⟨ θxM , θσ ⟩ ⟩ =
    ⟨ ⟨ θxM , subst-reflect θeqs θxM ⟩ , subst-reflect θσ θxM ⟩
unify-rec-sound {⟨ op ⦅ Ms ⦆ , ` x ⟩ ∷ eqs} {σ} {θ}{acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡θ
    with occurs? x (op ⦅ Ms ⦆)
... | yes x∈M
    with unify[eqs,σ]≡θ
... | ()    
unify-rec-sound {⟨ op ⦅ Ms ⦆ , ` x ⟩ ∷ eqs} {σ} {θ}{acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡θ
    | no x∉M
    with unify-rec-sound {([ op ⦅ Ms ⦆ / x ] eqs)} {(⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ [ op ⦅ Ms ⦆ / x ] σ)} {θ}
             {rs _ (measure3{eqs}{θ} x∉M)}
             ((insert-subst {x}{op ⦅ Ms ⦆}{σ}{eqs} x∉M (M∪x∪eqs {op ⦅ Ms ⦆}{x}{eqs}{σ} eqs∩domσ⊆∅) Sσ))
             (eqs∩x∪σ⊆∅ {x}{op ⦅ Ms ⦆}{σ}{eqs} x∉M (M∪x∪eqs {op ⦅ Ms ⦆}{x}{eqs}{σ} eqs∩domσ⊆∅))
             unify[eqs,σ]≡θ
... | ⟨ θeqs , ⟨ θxM , θσ ⟩ ⟩ =
    ⟨ ⟨ sym θxM , subst-reflect θeqs θxM ⟩ , subst-reflect θσ θxM ⟩
unify-rec-sound {⟨ op ⦅ Ms ⦆ , op' ⦅ Ls ⦆ ⟩ ∷ eqs} {σ} {θ}{acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡θ
    with op-eq? op op'
... | yes refl
    with unify-rec-sound {append-eqs Ms Ls eqs}{σ}{θ}{rs _ (measure4{eqs}{θ})} Sσ
             (MsLseqs∩domσ⊆∅ {Ms = Ms}{Ls = Ls}{σ = σ} eqs∩domσ⊆∅) unify[eqs,σ]≡θ
... | ⟨ θMs,Ls,eqs , θσ ⟩
    with subst-vec-reflect {Ms = Ms}{Ls} θMs,Ls,eqs
... | ⟨ θMs=θLs , θeqs ⟩ =
    ⟨ ⟨ cong (λ □ → op ⦅ □ ⦆) θMs=θLs  , θeqs ⟩ , θσ ⟩
unify-rec-sound {⟨ op ⦅ Ms ⦆ , op' ⦅ Ls ⦆ ⟩ ∷ eqs} {σ} {θ}{acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡θ
    | no neq
    with unify[eqs,σ]≡θ
... | ()    

unify-sound : ∀{eqs}{θ}
   → unify eqs ≡ finished θ
   → θ unifies eqs
unify-sound {eqs}{θ} unify-eqs-θ =
    let m = (<₃-wellFounded (measure eqs [])) in
    proj₁ (unify-rec-sound {eqs}{[]}{θ}{m} empty G unify-eqs-θ)
    where
    G : vars-eqs eqs ∩ ∅ ⊆ ∅
    G rewrite p∩∅≡∅ (vars-eqs eqs) = λ z → z
```


```
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
        ⟨ subst-vec-pres {Ms = Ms}{Ls = Ls} θeqs (Ms≡-inversion θML) , θσ ⟩
unify-rec-complete {⟨ op ⦅ Ms ⦆ , op' ⦅ Ls ⦆ ⟩ ∷ eqs} {σ} {acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡no θ ⟨ ⟨ θML , θeqs ⟩ , θσ ⟩
    | no neq = neq (op≡-inversion θML)

unify-complete :  ∀{eqs}
   → unify eqs ≡ no-solution
   → ∀ θ → ¬ θ unifies eqs
unify-complete {eqs} unify[eqs]=no θ θeqs =
    let m = (<₃-wellFounded (measure eqs [])) in
    unify-rec-complete {eqs}{[]}{m} empty G unify[eqs]=no θ ⟨ θeqs , tt ⟩
    where
    G : vars-eqs eqs ∩ ∅ ⊆ ∅
    G rewrite p∩∅≡∅ (vars-eqs eqs) = λ z → z
```
