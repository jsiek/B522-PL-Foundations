```
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.Vec using (Vec; []; _∷_)
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
    union x y uf z  {- choose y's to be the representative -}
        with x ≟ uf z
    ... | yes xzᵣ = uf y
    ... | no xzᵣ = uf z
    
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

[_:=_]_ : Var → AST → Solution → Solution
([ x := M ] σ) y 
    with x ≟ y
... | yes xy = M
... | no xy = σ y
```

Huet's algorithm.

```
unify-vec : ℕ → ∀{a} → Vec AST a → Vec AST a → UnionFind → Solution
          → Maybe (UnionFind × Solution)

unify : ℕ → AST → AST → UnionFind → Solution → Maybe (UnionFind × Solution)
unify 0 M L uf σ = nothing
unify (suc n) (` x) (` y) uf σ
    with find x uf | find y uf
... | xᵣ | yᵣ
    with xᵣ ≟ yᵣ
... | yes xy = just (uf , σ)
... | no xy
    with union xᵣ yᵣ uf
... | uf'    
    with σ xᵣ | σ yᵣ
... | ` _ | ` _ = just (uf' , σ)
... | M | L = unify n M L uf' σ
unify (suc n) (` x) (op ⦅ Ls ⦆) uf σ
    with find x uf
... | xᵣ
    with σ xᵣ
... | ` _ = just (uf , ([ xᵣ := op ⦅ Ls ⦆ ] σ))
... | M = 
    unify n M (op ⦅ Ls ⦆) uf σ
unify (suc n) (op ⦅ Ms ⦆) (` y) uf σ 
    with find y uf
... | yᵣ
    with σ yᵣ
... | ` _ = just (uf , ([ yᵣ := op ⦅ Ms ⦆ ] σ))
... | L =
    unify n (op ⦅ Ms ⦆) L uf σ
unify (suc n) (op ⦅ Ms ⦆) (op' ⦅ Ls ⦆) uf σ
    with op-eq op op'
... | no neq = nothing
... | yes refl = unify-vec n Ms Ls uf σ

unify-vec zero {a} Ms Ls uf σ = nothing
unify-vec (suc n) {zero} [] [] uf σ = just (uf , σ)
unify-vec (suc n) {suc a} (M ∷ Ms) (L ∷ Ls) uf σ
    with unify n M L uf σ
... | nothing = nothing    
... | just (uf' , σ') =
    unify-vec n Ms Ls uf' σ'
```
