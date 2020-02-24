```
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.Vec using (Vec)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Unification
    (Op : Set)
    (op-eq : (x : Op) → (y : Op) → Dec (x ≡ y))
    (arity : Op → ℕ) where
```

{-

  Union-find interface

-}

```
record UnionFindRec (A : Set) (UF : Set) : Set₁ where
  field
    union : A → A → UF → UF
    find : A → UF → A
    make-set : A → UF → UF
    init : UF
```

A very simple Union-Find data structure.

```
UnionFind : Set
UnionFind = ℕ → ℕ

uf : UnionFindRec ℕ (ℕ → ℕ)
uf = record
    { union = union ;
      find = find ;
      make-set = make-set ;
      init = λ x → x }
    where
    union : ℕ → ℕ → (ℕ → ℕ) → (ℕ → ℕ)
    union x y uf z
        with x ≟ z
    ... | yes xz = uf y
    ... | no xz = uf z

    find : ℕ → (ℕ → ℕ) → ℕ
    find x uf = uf x
    
    make-set : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
    make-set x uf = uf

open UnionFindRec uf
```

```
Var = ℕ

data AST : Set where
  `_ : Var → AST
  _⦅_⦆ : (op : Op) → Vec AST (arity op) → AST
```

```
Solution : Set
Solution = Var → AST

init-soln : Solution
init-soln = λ x → ` x
```

Huet's algorithm.

```
unify : ℕ → AST → AST → UnionFind → Solution → Maybe (UnionFind × Solution)
unify 0 M L uf σ = nothing
unify (suc n) (` x) (` y) uf σ
    with find x uf | find y uf
... | xr | yr
    with xr ≟ yr
... | yes xy = just (uf , σ)
... | no xy
    with union xr yr uf
... | uf'    
    with σ xr | σ yr
... | ` _ | ` _ = just (uf' , σ)
... | M | L = unify n M L uf' σ
unify (suc n) (` x) (op ⦅ Ls ⦆) uf σ
    with find x uf
... | xr
    with σ xr
... | ` _ = {!!}
... | M = 
    unify n M (op ⦅ Ls ⦆) uf σ
unify (suc n) (op ⦅ Ms ⦆) (` y) uf σ =
    unify n (op ⦅ Ms ⦆) (σ (find y uf)) uf σ
unify (suc n) (op ⦅ Ms ⦆) (op' ⦅ Ls ⦆) uf σ = {!!}
```
