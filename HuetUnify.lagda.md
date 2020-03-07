
This is unfinished work... I decided to first do Martelli and
Montanari's algorithm, which is in the `Unification.lagda.md` file.

```
open import Data.Maybe
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
   renaming (_,_ to ⟨_,_⟩)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import UnionFind

module HuetUnify
    (Op : Set)
    (op-eq : (x : Op) → (y : Op) → Dec (x ≡ y))
    (arity : Op → ℕ) where
```

```
Var = ℕ

data AST : Set where
  `_ : Var → AST
  _⦅_⦆ : (op : Op) → Vec AST (arity op) → AST
```

```
Subst : Set
Subst = Var → AST

init-subst : Subst
init-subst = λ x → ` x

[_:=_]_ : Var → AST → Subst → Subst
([ x := M ] σ) y 
    with x ≟ y
... | yes xy = M
... | no xy = σ y
```

Huet's algorithm.

```
unify-vec : ℕ → ∀{a} → Vec AST a → Vec AST a → UnionFind → Subst
          → Maybe (UnionFind × Subst)

unify : ℕ → AST → AST → UnionFind → Subst → Maybe (UnionFind × Subst)
unify 0 M L uf σ = nothing
unify (suc n) (` x) (` y) uf σ
    with (find uf x) ≟ (find uf y)
... | yes xy = just ⟨ uf , σ ⟩
... | no xy
    with σ (find uf x) | σ (find uf y)
... | ` _ | ` _ = just ⟨ (union (find uf x) (find uf y) uf) , σ ⟩
... | M | L = unify n M L (union (find uf x) (find uf y) uf) σ
unify (suc n) (` x) (op ⦅ Ls ⦆) uf σ
    with σ (find uf x)
... | ` _ = just ⟨ uf , ([ (find uf x) := op ⦅ Ls ⦆ ] σ) ⟩
... | M = 
    unify n M (op ⦅ Ls ⦆) uf σ
unify (suc n) (op ⦅ Ms ⦆) (` y) uf σ 
    with σ (find uf y)
... | ` _ = just ⟨ uf , ([ (find uf y) := op ⦅ Ms ⦆ ] σ) ⟩
... | L =
    unify n (op ⦅ Ms ⦆) L uf σ
unify (suc n) (op ⦅ Ms ⦆) (op' ⦅ Ls ⦆) uf σ
    with op-eq op op'
... | no neq = nothing
... | yes refl = unify-vec n Ms Ls uf σ

unify-vec zero {a} Ms Ls uf σ = nothing
unify-vec (suc n) {zero} [] [] uf σ = just ⟨ uf , σ ⟩ 
unify-vec (suc n) {suc a} (M ∷ Ms) (L ∷ Ls) uf σ
    with unify n M L uf σ
... | nothing = nothing    
... | just ⟨ uf' , σ' ⟩ =
    unify-vec n Ms Ls uf' σ'
```

```
subst-vec : Subst → ∀{n} → Vec AST n → Vec AST n

subst : Subst → AST → AST
subst σ (` x) =  σ x
subst σ (op ⦅ As ⦆) = op ⦅ subst-vec σ As ⦆

subst-vec σ {zero} [] = []
subst-vec σ {suc n} (A ∷ As) = subst σ A ∷ subst-vec σ As
```

```
resolve : UnionFind → Subst → Subst
resolve uf σ x = subst (λ y → ` (find uf y)) (σ (find uf x))
```




```
{-
union-resolve-eq : ∀{x y}{uf uf'}{σ σ'}
   → (∀{x} → uf (uf x) ≡ uf x)
   → uf' ≡ union (uf x) (uf y) uf
   → σ' ≡ (resolve (union (uf x) (uf y) uf) σ)
   → σ' (uf' x) ≡ σ' (uf' y)
union-resolve-eq {x}{y}{uf}{uf'}{σ}{σ'} uf-idem uf'-def σ'-def = {!!}
    with (uf x) ≟ (uf (uf' x))
... | yes xx
    rewrite uf-idem {y} = {!!}
... | no xx = {!!}
-}

```

```
unify-eq-aux : ∀{n M L uf σ uf' σ'}
         → unify n M L uf σ ≡ just ⟨ uf' , σ' ⟩
         → subst (resolve uf' σ') M ≡ subst (resolve uf' σ') L 
unify-eq-aux {suc n} {` x} {` y} {uf} {σ} unif
    with find uf x ≟ find uf y
... | no xy
    with σ (find uf x) | σ (find uf y)
... | ` _ | ` _ = {!!}
... | M | L = {!!}
unify-eq-aux {suc n} {` x} {` y} {uf} {σ} unif | yes xy
    with unif
... | refl
    rewrite xy = refl
unify-eq-aux {suc n} {` x} {op ⦅ Ls ⦆} {uf} {σ} unif = {!!}
unify-eq-aux {suc n} {op ⦅ Ms ⦆} {` y} {uf} {σ} unif = {!!}
unify-eq-aux {suc n} {op ⦅ Ms ⦆} {op' ⦅ Ls ⦆} {uf} {σ} unif = {!!}



unify-eq : ∀{n M L uf σ}
         → unify n M L init init-subst ≡ just ⟨ uf , σ ⟩
         → subst (resolve uf σ) M ≡ subst (resolve uf σ) L 
unify-eq unif = {!!}
```
