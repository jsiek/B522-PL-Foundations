```
module TypeInference where
```

# Type Inference for STLC


## Imports

```
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.Maybe
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
   renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; inspect)
  renaming ([_] to ⟅_⟆)
```

The module `STLCWithRecursion` defines the STLC with primtive natural
numbers and general recursion. The variable representation is de
Bruijn indices and the type system is extrinsic.

```
open import STLCWithRecursion
```

The `Unification` modules defines the `unify` function for solving
equations over first-order terms, which we will use here to
solve equations over types.

```
open import Unification TyOp tyop-eq arity
   using (Equations; unify; finished; no-solution; unify-sound)
```

## Type Substitution

```
subst-env : Equations → Context → Context
subst-env σ ∅ = ∅
subst-env σ (Γ , A) = subst-env σ Γ , subst-ty σ A

subst-env-empty : ∀ Γ → subst-env [] Γ ≡ Γ
subst-env-empty ∅ = refl
subst-env-empty (Γ , A)
    rewrite subst-env-empty Γ
    | subst-empty A = refl

len : Context → ℕ
len ∅ = 0
len (Γ , x) = suc (len Γ)

<-∋ : ∀{Γ : Context}{x}
   → x < (len Γ)
   → Σ[ A ∈ Type ] Γ ∋ x ⦂ A
<-∋ {Γ , A} {zero} x<Γ = ⟨ A , Z ⟩
<-∋ {Γ , A} {suc x} (s≤s x<Γ) 
    with <-∋ {Γ} {x} x<Γ
... | ⟨ B , x:B ⟩ =
    ⟨ B , S x:B ⟩
```

```
subst-env-compose : ∀ σ σ' Γ
   → subst-env (σ' ∘ σ) Γ ≡ subst-env σ' (subst-env σ Γ)
subst-env-compose σ σ' ∅ = refl
subst-env-compose σ σ' (Γ , A)
    rewrite subst-ty-compose σ σ' A
    | subst-env-compose σ σ' Γ = refl
```

```
subst-pres-∋ : ∀{x Γ A σ}
   → Γ ∋ x ⦂ A
   → subst-env σ Γ ∋ x ⦂ subst-ty σ A
subst-pres-∋ {.0} {.(_ , A)} {A} Z = Z
subst-pres-∋ {.(suc _)} {.(_ , _)} {A} (S Γ∋x) = S (subst-pres-∋ Γ∋x)   
```

```
subst-id-prim : ∀{σ p}
   → subst-ty σ (typeof p) ≡ typeof p
subst-id-prim {σ} {base B-Nat} = refl
subst-id-prim {σ} {base B-Bool} = refl
subst-id-prim {σ} {pfun B-Nat p}
    rewrite subst-id-prim {σ} {p} = refl
subst-id-prim {σ} {pfun B-Bool p}
    rewrite subst-id-prim {σ} {p} = refl
```

```
subst-pres-types : ∀ {σ Γ A N}
   → Γ ⊢ N ⦂ A
   → subst-env σ Γ ⊢ N ⦂ subst-ty σ A
subst-pres-types {σ} {Γ} {A} {` x} (⊢` Γ∋x) = ⊢` (subst-pres-∋ Γ∋x)
subst-pres-types {σ} {Γ} {A ⇒ B} {ƛ N} (⊢ƛ Γ⊢N:B) = ⊢ƛ (subst-pres-types Γ⊢N:B)
subst-pres-types {σ} {Γ} {B} {.(_ · _)} (⊢· Γ⊢L:A→B Γ⊢M:A) =
    let ⊢L = subst-pres-types {σ} Γ⊢L:A→B in
    let ⊢M = subst-pres-types {σ} Γ⊢M:A in
    ⊢· ⊢L ⊢M
subst-pres-types {σ} {Γ} {A} {.(μ _)} (⊢μ Γ⊢N:A) = ⊢μ (subst-pres-types Γ⊢N:A)
subst-pres-types {σ} {Γ} {A} {$ p k} (⊢$ eq)
    rewrite eq = ⊢$ (subst-id-prim{σ}{p})
```

```
len-subst-env : ∀ Γ σ → len (subst-env σ Γ) ≡ len Γ
len-subst-env ∅ σ = refl
len-subst-env (Γ , A) σ = cong suc (len-subst-env Γ σ)
```

## Type Inference

Milner's Algorithm 𝒲 adapted to the STLC.

```
𝒲 : (Γ : Context) → (M : Term) → WF (len Γ) M → ℕ 
   → Maybe (Σ[ σ ∈ Equations ] Σ[ A ∈ Type ] subst-env σ Γ ⊢ M ⦂ A × ℕ)
𝒲 Γ (` x) (WF-var .x x<Γ) α
    with <-∋ x<Γ
... | ⟨ A , Γ∋x ⟩ =
    just ⟨ [] , ⟨ A , ⟨ (⊢` G) , α ⟩ ⟩ ⟩
    where G : subst-env [] Γ ∋ x ⦂ A
          G rewrite subst-env-empty Γ = Γ∋x
𝒲 Γ ($ p k) wfm α = just ⟨ [] , ⟨ (typeof p) , ⟨ (⊢$ refl) , α ⟩ ⟩ ⟩
𝒲 Γ (ƛ N) (WF-op (WF-cons (WF-bind (WF-ast wfN)) WF-nil)) α
    with 𝒲 (Γ , (tyvar α)) N wfN (suc α)
... | nothing = nothing
... | just ⟨ σ , ⟨ B , ⟨ ⊢N:B , β ⟩ ⟩ ⟩ =
      just ⟨ σ , ⟨ (subst-ty σ (tyvar α) ⇒ B) , ⟨ ⊢ƛ ⊢N:B , β ⟩ ⟩ ⟩
𝒲 Γ (μ N) (WF-op (WF-cons (WF-bind (WF-ast wfN)) WF-nil)) α
    with 𝒲 (Γ , (tyvar α)) N wfN (suc α)
... | nothing = nothing
... | just ⟨ σ , ⟨ A , ⟨ ⊢N:A , β ⟩ ⟩ ⟩
    with unify (⟨ subst-ty σ (tyvar α) , A ⟩ ∷ []) | inspect unify (⟨ subst-ty σ (tyvar α) , A ⟩ ∷ [])
... | no-solution | ⟅ uni ⟆ = nothing
... | finished σ' | ⟅ uni ⟆ =
      let α' = subst-ty σ' (subst-ty σ (tyvar α)) in
      just ⟨ σ' ∘ σ , ⟨ α' , ⟨ ⊢μ G , β ⟩ ⟩ ⟩
    where
    G : subst-env (σ' ∘ σ) Γ , subst-ty σ' (subst-ty σ (tyvar α))
        ⊢ N ⦂ subst-ty σ' (subst-ty σ (tyvar α))
    G   with subst-pres-types {σ'} ⊢N:A
    ... | σ'σΓ⊢N:σA
        with unify-sound (⟨ subst-ty σ (tyvar α) , A ⟩ ∷ []) σ' uni
    ... | ⟨ σ'σα=σ'A , _ ⟩ 
        rewrite subst-env-compose σ σ' Γ
        | σ'σα=σ'A = σ'σΓ⊢N:σA
𝒲 Γ (L · M) (WF-op (WF-cons (WF-ast wfL) (WF-cons (WF-ast wfM) WF-nil))) α
    with 𝒲 Γ L wfL α
... | nothing = nothing
... | just ⟨ σ , ⟨ A , ⟨ σΓ⊢L:A , β ⟩ ⟩ ⟩
    rewrite cong (λ □ → WF □ M) (sym (len-subst-env Γ σ))
    with 𝒲 (subst-env σ Γ) M wfM β
... | nothing = nothing
... | just ⟨ σ' , ⟨ B , ⟨ σ'σΓ⊢M:B , γ ⟩ ⟩ ⟩ 
    with unify (⟨ subst-ty σ' A , B ⇒ tyvar γ ⟩ ∷ []) | inspect unify (⟨ subst-ty σ' A , B ⇒ tyvar γ ⟩ ∷ [])
... | no-solution | ⟅ uni ⟆ = nothing
... | finished θ | ⟅ uni ⟆
    with subst-pres-types {σ'} σΓ⊢L:A
... | σ'σΓ⊢L:σ'A
    with subst-pres-types {θ} σ'σΓ⊢L:σ'A | subst-pres-types {θ} σ'σΓ⊢M:B
... | θσ'σΓ⊢L:θσ'A | θσ'σΓ⊢M:θB
    with unify-sound (⟨ subst-ty σ' A , B ⇒ tyvar γ ⟩ ∷ []) _ uni
... | ⟨ θσ'A=θB⇒γ , _ ⟩
    rewrite sym (subst-env-compose σ σ' Γ)
    | sym (subst-env-compose (σ' ∘ σ) θ Γ)
    | θσ'A=θB⇒γ =
    just ⟨ θ ∘ (σ' ∘ σ) ,
         ⟨ (subst-ty θ (tyvar γ)) ,
         ⟨ ⊢·  θσ'σΓ⊢L:θσ'A  θσ'σΓ⊢M:θB ,
           (suc γ) ⟩ ⟩ ⟩
```


