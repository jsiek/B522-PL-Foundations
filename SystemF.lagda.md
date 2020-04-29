```
{-# OPTIONS --rewriting #-}

module SystemF where
```

# SystemF


## Imports

```
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.Bool using () renaming (Bool to 𝔹)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-step; ≤-refl; ≤-pred)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
   renaming (_,_ to ⟨_,_⟩)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

import Syntax
```

## Primitives

The idea here is to use Agda values as primitive constants. We include
natural numbers, Booleans, and Agda functions over naturals and
Booleans.

The `Base` and `Prim` data types describe the types of constants.

```
data Base : Set where
  B-Nat : Base
  B-Bool : Base

data Prim : Set where
  base : Base → Prim
  _⇛_ : Base → Prim → Prim
```

The `base-rep` and `rep` functions map from the type descriptors to
the Agda types that we will use to represent the constants.

```
base-rep : Base → Set 
base-rep B-Nat = ℕ
base-rep B-Bool = 𝔹

rep : Prim → Set
rep (base b) = base-rep b
rep (b ⇛ p) = base-rep b → rep p
```

## Terms

We use the
[abstract-binding-trees](https://github.com/jsiek/abstract-binding-trees)
library to represent terms.

```
data Op : Set where
  op-lam : Op
  op-app : Op
  op-const : (p : Prim) → rep p → Op
  op-abs : Op
  op-tyapp : Op

sig : Op → List ℕ
sig op-lam = 1 ∷ []
sig op-app = 0 ∷ 0 ∷ []
sig (op-const p k) = []
sig op-abs = 0 ∷ []
sig op-tyapp = 0 ∷ []

open Syntax using (Rename; _•_; ↑; id; ext; ⦉_⦊; _⨟ᵣ_)

open Syntax.OpSig Op sig
  using (`_; _⦅_⦆; cons; nil; bind; ast; _[_]; Subst; ⟪_⟫; ⟦_⟧; exts; rename)
  renaming (ABT to Term)

infixl 7  _·_

pattern $ p k      = (op-const p k) ⦅ nil ⦆
pattern ƛ N        = op-lam         ⦅ cons (bind (ast N)) nil ⦆
pattern _·_ L M    = op-app         ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern Λ  N       = op-abs         ⦅ cons (ast N) nil ⦆
pattern _[·] N     = op-tyapp       ⦅ cons (ast N) nil ⦆
```

## Types

```
data TyOp : Set where
  op-nat : TyOp
  op-bool : TyOp
  op-fun : TyOp
  op-all : TyOp
```

```
tysig : TyOp → List ℕ
tysig op-nat = []
tysig op-bool = []
tysig op-fun = 0 ∷ 0 ∷ []
tysig op-all = 1 ∷ []
```

```
open Syntax.OpSig TyOp tysig
  using (_⨟_;
         rename-subst-commute; ext-cons-shift; compose-rename;
         rename→subst; rename-subst; exts-cons-shift; commute-subst)
  renaming (ABT to Type; `_ to tyvar; _⦅_⦆ to _〘_〙;
            cons to tycons; nil to tynil; bind to tybind; ast to tyast;
            _[_] to _⦗_⦘; Subst to TySubst; ⟪_⟫ to ⸂_⸃; ⟦_⟧ to ⧼_⧽;
            exts to tyexts; rename to tyrename)

pattern Nat      = op-nat 〘 tynil 〙
pattern Bool     = op-bool 〘 tynil 〙
pattern _⇒_ A B  = op-fun 〘 tycons (tyast A) (tycons (tyast B) tynil) 〙
pattern all A    = op-all 〘 tycons (tybind (tyast A)) tynil 〙
```

## Type of a primitive

```
typeof-base : Base → Type
typeof-base B-Nat = Nat
typeof-base B-Bool = Bool

typeof : Prim → Type
typeof (base b) = typeof-base b 
typeof (b ⇛ p) = typeof-base b ⇒ typeof p
```

## Contexts

```
data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context
```

```
infix  4  _∋_⦂_

data _∋_⦂_ : Context → ℕ → Type → Set where

  Z : ∀ {Γ A}
      ------------------
    → Γ , A ∋ 0 ⦂ A

  S : ∀ {Γ x A B}
    → Γ ∋ x ⦂ A
      ------------------
    → Γ , B ∋ (suc x) ⦂ A
```

```
ctx-rename : Rename → Context → Context
ctx-rename ρ ∅ = ∅
ctx-rename ρ (Γ , A) = ctx-rename ρ Γ , tyrename ρ A
```

```
ctx-subst : TySubst → Context → Context
ctx-subst σ ∅ = ∅
ctx-subst σ (Γ , A) = ctx-subst σ Γ , ⸂ σ ⸃ A
```

## Well-formed Types

```
infix  4  _⊢_

data _⊢_ : ℕ → Type → Set where
  ⊢var : ∀{Δ α}
     → α < Δ
       -----------
     → Δ ⊢ tyvar α

  ⊢nat : ∀{Δ}
       -------
     → Δ ⊢ Nat
     
  ⊢bool : ∀{Δ}
       --------
     → Δ ⊢ Bool

  ⊢fun : ∀{Δ A B}
     → Δ ⊢ A  →  Δ ⊢ B
       ---------------
     → Δ ⊢ A ⇒ B

  ⊢all : ∀{Δ A}
     → suc Δ ⊢ A
       ---------
     → Δ ⊢ all A
```


## Typing judgement

```
infix  4  _⨟_⊢_⦂_

data _⨟_⊢_⦂_ : ℕ → Context → Term → Type → Set where

  -- Constants
  ⊢$ : ∀{Γ Δ p k A}
     → A ≡ typeof p
       -------------
     → Δ ⨟ Γ ⊢ $ p k ⦂ A

  -- Axiom 
  ⊢` : ∀ {Γ Δ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Δ ⨟ Γ ⊢ ` x ⦂ A

  -- ⇒-I 
  ⊢ƛ : ∀ {Γ Δ N A B}
    → Δ ⊢ A
    → Δ ⨟ Γ , A ⊢ N ⦂ B
      -------------------
    → Δ ⨟ Γ ⊢ ƛ N ⦂ A ⇒ B

  -- ⇒-E
  ⊢· : ∀ {Γ Δ L M A B}
    → Δ ⨟ Γ ⊢ L ⦂ A ⇒ B
    → Δ ⨟ Γ ⊢ M ⦂ A
      -------------
    → Δ ⨟ Γ ⊢ L · M ⦂ B

  -- all-I
  ⊢Λ : ∀ {Γ Δ A N}
    → suc Δ ⨟ ctx-rename (↑ 1) Γ ⊢ N ⦂ A
      ---------------------------------
    → Δ ⨟ Γ ⊢ Λ N ⦂ all A

  -- all-E
  ⊢[·] : ∀{Γ Δ A B N}
    → Δ ⊢ B
    → Δ ⨟ Γ ⊢ N ⦂ all A
      ----------------------
    → Δ ⨟ Γ ⊢ N [·] ⦂ A ⦗ B ⦘
```

## Values

```
data Value : Term → Set where

  V-ƛ : ∀ {N : Term}
      ---------------------------
    → Value (ƛ N)

  V-const : ∀ {p k}
      -----------------
    → Value ($ p k)

  V-Λ : ∀ {N : Term}
      -----------------
    → Value (Λ N)
```

## Frames and plug

```
data Frame : Set where
  □·_ : Term → Frame
  _·□ : (M : Term) → (v : Value M) → Frame
  □[·] : Frame
```

The `plug` function fills a frame's hole with a term.

```
plug : Term → Frame → Term
plug L (□· M)        = L · M
plug M ((L ·□) v)    = L · M
plug M (□[·])        = M [·]
```

## Reduction

```
infix 4 _—→_

data _—→_ : Term → Term → Set where

  ξ : ∀ {M M′}
    → (F : Frame)
    → M —→ M′
      ---------------------
    → plug M F —→ plug M′ F

  β-ƛ : ∀ {N V}
    → Value V
      --------------------
    → (ƛ N) · V —→ N [ V ]

  δ : ∀ {b p f k}
      ---------------------------------------------
    → ($ (b ⇛ p) f) · ($ (base b) k) —→ ($ p (f k))

  β-Λ : ∀{N}
      --------------
    → (Λ N) [·] —→ N
```

## Multi-step reduction

```
infix  2 _—↠_
infixr 2 _—→⟨_⟩_
infix  3 _■

data _—↠_ : Term → Term → Set where
  _■ : ∀ M
      ---------
    → M —↠ M

  _—→⟨_⟩_ : ∀ L {M N}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N
```

## Canonical Forms

```
data Function : Term → Set where
  Fun-ƛ : ∀ {N} → Function (ƛ N)
  Fun-prim : ∀{b p k} → Function ($ (b ⇛ p) k)

canonical-fun : ∀{V A B}
  → 0 ⨟ ∅ ⊢ V ⦂ A ⇒ B
  → Value V
    ----------
  → Function V
canonical-fun ⊢V V-ƛ = Fun-ƛ
canonical-fun (⊢$ {p = base B-Nat} ()) (V-const {_} {k})
canonical-fun (⊢$ {p = base B-Bool} ()) (V-const {_} {k})
canonical-fun (⊢$ {p = b ⇛ p} eq) (V-const {_} {k}) = Fun-prim

data Constant : Base → Term → Set where
  base-const : ∀{b k} → Constant b ($ (base b) k)

canonical-base : ∀{b V A}
  → A ≡ typeof-base b
  → 0 ⨟ ∅ ⊢ V ⦂ A
  → Value V
    ------------
  → Constant b V
canonical-base {B-Nat} () (⊢ƛ wft ⊢V) V-ƛ
canonical-base {B-Bool} () (⊢ƛ wft ⊢V) V-ƛ
canonical-base {B-Nat} eq (⊢$ {p = base B-Nat} refl) V-const = base-const
canonical-base {B-Bool} eq (⊢$ {p = base B-Bool} refl) V-const = base-const
canonical-base {B-Nat} refl (⊢$ {p = b' ⇛ p} ()) V-const
canonical-base {B-Bool} refl (⊢$ {p = b' ⇛ p} ()) V-const

data Forall : Term → Set where
  Forall-Λ : ∀ {N} → Forall (Λ N)

canonical-all : ∀{V A}
  → 0 ⨟ ∅ ⊢ V ⦂ all A
  → Value V
    --------
  → Forall V
canonical-all {_} (⊢$ {p = base B-Nat} ()) V-const
canonical-all {_} (⊢$ {p = base B-Bool} ()) V-const
canonical-all {V} ⊢V V-Λ = Forall-Λ
```

## Progress

```
data Progress (M : Term) : Set where

  step : ∀ {N}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M
```

```
progress : ∀ {M A}
  → 0 ⨟ ∅ ⊢ M ⦂ A
    ------------
  → Progress M
progress (⊢` ())
progress (⊢$ _)                             = done V-const
progress (⊢ƛ wft ⊢N)                        = done V-ƛ
progress (⊢· {L = L}{M}{A}{B} ⊢L ⊢M)
    with progress ⊢L
... | step L—→L′                            = step (ξ (□· M) L—→L′)
... | done VL
        with progress ⊢M
...     | step M—→M′                        = step (ξ ((L ·□) VL) M—→M′)
...     | done VM
            with canonical-fun ⊢L VL
...         | Fun-ƛ                         = step (β-ƛ VM)
...         | Fun-prim {b}{p}{k}
                with ⊢L
...             | ⊢$ refl
                with canonical-base refl ⊢M VM
...             | base-const                = step δ
progress (⊢Λ ⊢N) = done V-Λ
progress (⊢[·] wfB ⊢N)
    with progress ⊢N
... | step N—→N′                            = step (ξ □[·] N—→N′)
... | done VN
    with canonical-all ⊢N VN
... | Forall-Λ {M}                          = step β-Λ
```

## Properties of Renaming and Substitution on Contexts

```
ctx-rename-pres : ∀{Γ x A ρ}
  → Γ ∋ x ⦂ A
  → ctx-rename ρ Γ ∋ x ⦂ tyrename ρ A
ctx-rename-pres Z = Z
ctx-rename-pres (S ∋x) = S (ctx-rename-pres ∋x)
```

```
ctx-rename-reflect : ∀{ρ}{Γ}{x}{A}
  → ctx-rename ρ Γ ∋ x ⦂ A
  → Σ[ B ∈ Type ] A ≡ tyrename ρ B × Γ ∋ x ⦂ B
ctx-rename-reflect {ρ} {Γ , C} {zero} Z = ⟨ C , ⟨ refl , Z ⟩ ⟩
ctx-rename-reflect {ρ} {Γ , C} {suc x} (S ∋x)
    with ctx-rename-reflect {ρ} {Γ} {x} ∋x
... | ⟨ B , ⟨ refl , ∋x' ⟩ ⟩ =    
      ⟨ B , ⟨ refl , (S ∋x') ⟩ ⟩
```

```
compose-ctx-rename : ∀{Γ}{ρ₁}{ρ₂}
  → ctx-rename ρ₂ (ctx-rename ρ₁ Γ) ≡ ctx-rename (ρ₁ ⨟ᵣ ρ₂) Γ
compose-ctx-rename {∅} {ρ₁} {ρ₂} = refl
compose-ctx-rename {Γ , A} {ρ₁} {ρ₂}
    rewrite compose-rename {A} {ρ₁} {ρ₂}
    | compose-ctx-rename {Γ} {ρ₁} {ρ₂} = refl
```

```
ctx-subst-pres : ∀{Γ x A σ}
  → Γ ∋ x ⦂ A
  → ctx-subst σ Γ ∋ x ⦂ ⸂ σ ⸃ A
ctx-subst-pres Z = Z
ctx-subst-pres (S ∋x) = S (ctx-subst-pres ∋x)
```

```
ctx-rename-subst : ∀ ρ Γ → ctx-rename ρ Γ ≡ ctx-subst (rename→subst ρ) Γ
ctx-rename-subst ρ ∅ = refl
ctx-rename-subst ρ (Γ , A)
    rewrite rename-subst ρ A
    | ctx-rename-subst ρ Γ = refl
```

```
compose-ctx-subst : ∀{Γ}{σ₁}{σ₂}
  → ctx-subst σ₂ (ctx-subst σ₁ Γ) ≡ ctx-subst (σ₁ ⨟ σ₂) Γ
compose-ctx-subst {∅} {σ₁} {σ₂} = refl
compose-ctx-subst {Γ , A} {σ₁} {σ₂}
  rewrite compose-ctx-subst {Γ} {σ₁} {σ₂} = refl
```

## Renaming Preserves Well-Formed Types

```
WFRename : ℕ → Rename → ℕ → Set
WFRename Δ ρ Δ′ = ∀{α} → α < Δ → Δ′ ⊢ tyvar (⦉ ρ ⦊ α)
```

```
ext-pres-wf : ∀{ρ Δ Δ′}
  → WFRename Δ ρ Δ′
  → WFRename (suc Δ) (ext ρ) (suc Δ′)
ext-pres-wf {ρ} ⊢ρ {zero} α<Δ = ⊢var (s≤s z≤n)
ext-pres-wf {ρ} ⊢ρ {suc α} α<Δ
    with ⊢ρ {α} (≤-pred α<Δ)
... | ⊢var lt = ⊢var (s≤s lt)
```

```
rename-pres-wf : ∀{ρ}{Δ Δ′}{A}
  → WFRename Δ ρ Δ′
  → Δ ⊢ A
  → Δ′ ⊢ tyrename ρ A
rename-pres-wf ΔσΔ′ (⊢var α) = ΔσΔ′ α
rename-pres-wf ΔσΔ′ ⊢nat = ⊢nat
rename-pres-wf ΔσΔ′ ⊢bool = ⊢bool
rename-pres-wf {σ} ΔσΔ′ (⊢fun ⊢A ⊢B) =
    ⊢fun (rename-pres-wf {σ} ΔσΔ′ ⊢A) (rename-pres-wf {σ} ΔσΔ′ ⊢B)
rename-pres-wf {ρ} ΔσΔ′ (⊢all ⊢A) =
  let IH = rename-pres-wf {ρ = ext ρ} (ext-pres-wf ΔσΔ′) ⊢A in
   ⊢all IH
```

## Term Renaming Preserves Well-Typed Terms

```
WTRename : Context → Rename → Context → Set
WTRename Γ ρ Γ′ = ∀ {x A} → Γ ∋ x ⦂ A → Γ′ ∋ ⦉ ρ ⦊ x ⦂ A
```

```
ctx-ren-ren : ∀{ρ}{γ}{Γ}{Γ′}
  → WTRename Γ ρ Γ′
  → WTRename (ctx-rename γ Γ) ρ (ctx-rename γ Γ′)
ctx-ren-ren {ρ}{γ}{Γ}{Γ′} ΓρΓ′ {x}{A} ∋x
    with ctx-rename-reflect ∋x
... | ⟨ B , ⟨ refl , ∋x' ⟩ ⟩ =
    let ∋x'' = ΓρΓ′ {x}{B} ∋x' in
    ctx-rename-pres ∋x''
```

```
ext-pres : ∀ {Γ Γ′ ρ B}
  → WTRename Γ ρ Γ′
    --------------------------------
  → WTRename (Γ , B) (ext ρ) (Γ′ , B)
ext-pres {ρ = ρ } ⊢ρ Z =  Z
ext-pres {ρ = ρ } ⊢ρ (S {x = x} ∋x) =  S (⊢ρ ∋x)
```

```
rename-pres : ∀ {Γ Γ′ Δ ρ M A}
  → WTRename Γ ρ Γ′
  → Δ ⨟ Γ ⊢ M ⦂ A
    ------------------
  → Δ ⨟ Γ′ ⊢ rename ρ M ⦂ A
rename-pres ⊢ρ (⊢$ eq)              = ⊢$ eq
rename-pres ⊢ρ (⊢` ∋w)              =  ⊢` (⊢ρ ∋w)
rename-pres {ρ = ρ} ⊢ρ (⊢ƛ wf ⊢N)   =
    ⊢ƛ wf (rename-pres {ρ = ext ρ} (ext-pres {ρ = ρ} ⊢ρ) ⊢N)
rename-pres {ρ = ρ} ⊢ρ (⊢· ⊢L ⊢M)   =
    ⊢· (rename-pres {ρ = ρ} ⊢ρ ⊢L) (rename-pres {ρ = ρ} ⊢ρ ⊢M)
rename-pres {ρ = ρ} ⊢ρ (⊢Λ ⊢N)      =
    ⊢Λ (rename-pres {ρ = ρ} (ctx-ren-ren {ρ} ⊢ρ) ⊢N)
rename-pres {ρ = ρ} ⊢ρ (⊢[·] wf ⊢N) = ⊢[·] wf (rename-pres {ρ = ρ} ⊢ρ ⊢N)
```

## Type Renaming Preserves Well-Typed Terms

```
rename-base : ∀ ρ b
   → tyrename ρ (typeof-base b) ≡ typeof-base b
rename-base σ B-Nat = refl
rename-base σ B-Bool = refl
```

```
rename-prim : ∀ ρ p
   → tyrename ρ (typeof p) ≡ typeof p
rename-prim σ (base B-Nat) = refl
rename-prim σ (base B-Bool) = refl
rename-prim σ (b ⇛ p)
    with rename-base σ b | rename-prim σ p
... | eq1 | eq2 rewrite eq1 | eq2 = refl 
```

```
ty-rename : ∀{ρ : Rename}{Δ Δ′}{Γ}{N}{A}
  → WFRename Δ ρ Δ′
  → Δ ⨟ Γ ⊢ N ⦂ A
    -------------------------------------
  → Δ′ ⨟ ctx-rename ρ Γ ⊢ N ⦂ tyrename ρ A
ty-rename {ρ} {Δ} {Δ'} {Γ} {_} {A} ΔρΔ′ (⊢$ {p = p} refl) = ⊢$ (rename-prim ρ p)
ty-rename {ρ} {Δ} {Δ'} {Γ} {_} {A} ΔρΔ′ (⊢` ∋x) = ⊢` (ctx-rename-pres ∋x)
ty-rename {ρ} {Δ} {Δ'} {Γ} {_} {.(_ ⇒ _)} ΔρΔ′ (⊢ƛ wf ⊢N) =
    ⊢ƛ (rename-pres-wf {ρ} ΔρΔ′ wf) (ty-rename ΔρΔ′ ⊢N)
ty-rename {ρ} {Δ} {Δ'} {Γ} {_} {A} ΔρΔ′ (⊢· ⊢L ⊢M) =
    ⊢· (ty-rename ΔρΔ′ ⊢L ) (ty-rename ΔρΔ′ ⊢M)
ty-rename {ρ} {Δ} {Δ'} {Γ} {Λ N} {.(all _)} ΔρΔ′ (⊢Λ {A = A} ⊢N)
    with ty-rename {ext ρ} (ext-pres-wf ΔρΔ′) ⊢N
... | IH =
    ⊢Λ (subst (λ □ → suc Δ' ⨟ □ ⊢ N ⦂ tyrename (ext ρ) A) EQ IH) 
    where
    EQ = begin
            ctx-rename (ext ρ) (ctx-rename (↑ 1) Γ)
         ≡⟨ compose-ctx-rename ⟩
            ctx-rename (↑ 1 ⨟ᵣ ext ρ) Γ
         ≡⟨ cong (λ □ → ctx-rename (↑ 1 ⨟ᵣ □) Γ) (ext-cons-shift ρ) ⟩
            ctx-rename (↑ 1 ⨟ᵣ 0 • (ρ ⨟ᵣ ↑ 1)) Γ
         ≡⟨⟩
            ctx-rename (ρ ⨟ᵣ ↑ 1) Γ
         ≡⟨ sym compose-ctx-rename ⟩
            ctx-rename (↑ 1) (ctx-rename ρ Γ)
         ∎
ty-rename {ρ} {Δ} {Δ'} {Γ} {N [·]} {_} ΔρΔ′ (⊢[·] {A = A}{B = B} wf ⊢N) =
    let IH = ty-rename {ρ} ΔρΔ′ ⊢N in
    let ⊢N[·] = ⊢[·] (rename-pres-wf {ρ} ΔρΔ′ wf) IH in
    subst (λ □ → Δ' ⨟ ctx-rename ρ Γ ⊢ N [·] ⦂ □) EQ ⊢N[·]
    where
    EQ : tyrename (ext ρ) A ⦗ tyrename ρ B ⦘ ≡ tyrename ρ (A ⦗ B ⦘)
    EQ = rename-subst-commute {A}{B}{ρ}
```

## Term Substitution Preserves Well-Typed Terms

```
WTSubst : Context → ℕ → Subst → Context → Set
WTSubst Γ Δ σ Γ′ = ∀ {A x} → Γ ∋ x ⦂ A → Δ ⨟ Γ′ ⊢ ⟪ σ ⟫ (` x) ⦂ A
```

```
exts-pres : ∀ {Γ Δ Γ′ σ B}
  → WTSubst Γ Δ σ Γ′
    --------------------------------
  → WTSubst (Γ , B) Δ (exts σ) (Γ′ , B)
exts-pres {σ = σ} Γ⊢σ Z = ⊢` Z
exts-pres {σ = σ} Γ⊢σ (S {x = x} ∋x) = rename-pres {ρ = ↑ 1} S (Γ⊢σ ∋x)
```

```
WF↑1 : ∀{Δ} → WFRename Δ (↑ 1) (suc Δ)
WF↑1 {Δ}{α} α<Δ = ⊢var (s≤s α<Δ)
```

```
subst-pres : ∀ {Γ Γ′ σ N A Δ}
  → WTSubst Γ Δ σ Γ′
  → Δ ⨟ Γ ⊢ N ⦂ A
    ---------------
  → Δ ⨟ Γ′ ⊢ ⟪ σ ⟫ N ⦂ A
subst-pres Γ⊢σ (⊢$ e) = ⊢$ e 
subst-pres Γ⊢σ (⊢` eq)           = Γ⊢σ eq
subst-pres {σ = σ} Γ⊢σ (⊢ƛ wf ⊢N) =
    ⊢ƛ wf (subst-pres {σ = exts σ} (exts-pres {σ = σ} Γ⊢σ) ⊢N) 
subst-pres {σ = σ} Γ⊢σ (⊢· ⊢L ⊢M) =
    ⊢· (subst-pres {σ = σ} Γ⊢σ ⊢L) (subst-pres {σ = σ} Γ⊢σ ⊢M) 
subst-pres {Γ}{Γ′}{σ}{Δ = Δ} Γ⊢σ (⊢Λ ⊢N)   = ⊢Λ (subst-pres {σ = σ} G ⊢N)
  where
  G : WTSubst (ctx-rename (↑ 1) Γ) (suc Δ) σ (ctx-rename (↑ 1) Γ′)
  G {A}{x} ∋x
      with ctx-rename-reflect {↑ 1}{Γ}{x}{A} ∋x
  ... | ⟨ B , ⟨ refl , ∋x' ⟩ ⟩ =
         let ⊢⟦σ⟧x = Γ⊢σ {B}{x} ∋x' in
         ty-rename{↑ 1}{Δ}{suc Δ} WF↑1 ⊢⟦σ⟧x
subst-pres {σ = σ} Γ⊢σ (⊢[·] wf ⊢N) = ⊢[·] wf (subst-pres {σ = σ} Γ⊢σ ⊢N)
```

```
substitution : ∀{Γ Δ A B M N}
   → Δ ⨟ Γ ⊢ M ⦂ A
   → Δ ⨟ (Γ , A) ⊢ N ⦂ B
     ---------------
   → Δ ⨟ Γ ⊢ N [ M ] ⦂ B
substitution {Γ}{Δ}{A}{B}{M}{N} ⊢M ⊢N = subst-pres {σ = M • ↑ 0 } G ⊢N
    where
    G : WTSubst (Γ , A) Δ (M • ↑ 0) Γ
    G {A₁} {zero} Z = ⊢M
    G {A₁} {suc x} (S ∋x) = ⊢` ∋x
```

## Type Substitution Preserves Well-Formed Types

```
WFSubst : ℕ → TySubst → ℕ → Set
WFSubst Δ σ Δ′ = ∀{α} → α < Δ → Δ′ ⊢ ⧼ σ ⧽ α
```

```
exts-pres-wf : ∀ {Δ Δ′ σ}
  → WFSubst Δ σ Δ′
    -----------------------------------
  → WFSubst (suc Δ) (tyexts σ) (suc Δ′)
exts-pres-wf ΔσΔ′ {zero} α<Δ = ⊢var (s≤s z≤n)
exts-pres-wf ΔσΔ′ {suc α} α<Δ =
    rename-pres-wf {ρ = ↑ 1} WF↑1 (ΔσΔ′ {α} (≤-pred α<Δ))
```

```
subst-pres-wf : ∀{σ}{Δ Δ′}{A}
  → WFSubst Δ σ Δ′
  → Δ ⊢ A
  → Δ′ ⊢ ⸂ σ ⸃ A
subst-pres-wf ΔσΔ′ (⊢var α) = ΔσΔ′ α
subst-pres-wf ΔσΔ′ ⊢nat = ⊢nat
subst-pres-wf ΔσΔ′ ⊢bool = ⊢bool
subst-pres-wf {σ} ΔσΔ′ (⊢fun ⊢A ⊢B) =
    ⊢fun (subst-pres-wf {σ} ΔσΔ′ ⊢A) (subst-pres-wf {σ} ΔσΔ′ ⊢B)
subst-pres-wf {σ} ΔσΔ′ (⊢all ⊢A) =
  let IH = subst-pres-wf {σ = tyexts σ} (exts-pres-wf ΔσΔ′) ⊢A in
  ⊢all IH
```

## Type Substitution Preserves Well-Typed Terms

```
subst-base : ∀ σ b
   → ⸂ σ ⸃ (typeof-base b) ≡ typeof-base b
subst-base σ B-Nat = refl
subst-base σ B-Bool = refl
```

```
subst-prim : ∀ σ p
   → ⸂ σ ⸃ (typeof p) ≡ typeof p
subst-prim σ (base B-Nat) = refl
subst-prim σ (base B-Bool) = refl
subst-prim σ (b ⇛ p)
    with subst-base σ b | subst-prim σ p
... | eq1 | eq2 rewrite eq1 | eq2 = refl 
```

```
ty-subst : ∀{σ : TySubst}{Δ Δ′}{Γ}{N}{A}
  → WFSubst Δ σ Δ′
  → Δ ⨟ Γ ⊢ N ⦂ A
    -------------------------------
  → Δ′ ⨟ ctx-subst σ Γ ⊢ N ⦂ ⸂ σ ⸃ A
ty-subst {σ} ΔσΔ′ (⊢$ {p = p} refl) = ⊢$ (subst-prim σ p)
ty-subst {σ} ΔσΔ′ (⊢` ∋x) = ⊢` (ctx-subst-pres ∋x)
ty-subst {σ} ΔσΔ′ (⊢ƛ wf ⊢N) =
  ⊢ƛ (subst-pres-wf {σ} ΔσΔ′ wf) (ty-subst {σ} ΔσΔ′ ⊢N)
ty-subst {σ} ΔσΔ′ (⊢· ⊢L ⊢M) = ⊢· (ty-subst {σ} ΔσΔ′ ⊢L) (ty-subst {σ} ΔσΔ′ ⊢M)
ty-subst {σ}{Δ}{Δ′}{Γ}{Λ N}{all A} ΔσΔ′ (⊢Λ ⊢N) =
    let IH = ty-subst {σ = tyexts σ} (exts-pres-wf ΔσΔ′) ⊢N in
    let ⊢N = subst (λ □ → suc Δ′ ⨟ □ ⊢ N ⦂ ⸂ tyexts σ ⸃ A) GEQ IH in 
    ⊢Λ ⊢N
    where
    GEQ = begin
            ctx-subst (tyexts σ) (ctx-rename (↑ 1) Γ)
         ≡⟨ cong (λ □ → ctx-subst (tyexts σ) □) (ctx-rename-subst (↑ 1) Γ) ⟩
            ctx-subst (tyexts σ) (ctx-subst (↑ 1) Γ)
         ≡⟨ compose-ctx-subst ⟩
            ctx-subst (↑ 1 ⨟ tyexts σ) Γ
         ≡⟨ cong (λ □ → ctx-subst (↑ 1 ⨟ □) Γ) (exts-cons-shift σ)  ⟩
            ctx-subst (↑ 1 ⨟ ((tyvar 0) • (σ ⨟ ↑ 1))) Γ
         ≡⟨⟩
            ctx-subst (σ ⨟ ↑ 1) Γ
         ≡⟨ sym compose-ctx-subst ⟩
            ctx-subst (↑ 1) (ctx-subst σ Γ)
         ≡⟨ sym (ctx-rename-subst (↑ 1) (ctx-subst σ Γ)) ⟩
            ctx-rename (↑ 1) (ctx-subst σ Γ)
         ∎
ty-subst {σ}{Δ}{Δ′}{Γ}{N [·]} ΔσΔ′ (⊢[·] {A = A}{B} wf ⊢N) =
    let IH = ty-subst {σ} ΔσΔ′ ⊢N in
    let ⊢N[·] = ⊢[·] (subst-pres-wf {σ} ΔσΔ′ wf) IH in
    subst (λ □ → Δ′ ⨟ ctx-subst σ Γ ⊢ N [·] ⦂ □) EQ ⊢N[·]
    where
    EQ : ⸂ tyexts σ ⸃ A  ⦗ ⸂ σ ⸃ B ⦘ ≡ ⸂ σ ⸃ (A ⦗ B ⦘)
    EQ = sym (commute-subst {A}{B}{σ})
```

```
type-substitution : ∀{B}{Δ}{Γ}{N}{A}
  → Δ ⊢ B
  → suc Δ ⨟ Γ ⊢ N ⦂ A
    -----------------------------------------
  → Δ ⨟ ctx-subst (B • id) Γ ⊢ N ⦂ A ⦗ B ⦘
type-substitution {B}{Δ} wfB ⊢N = ty-subst {σ = B • id} G ⊢N
    where
    G : WFSubst (suc Δ) (B • id) Δ
    G {zero} α<Δ = wfB
    G {suc α} α<Δ = ⊢var (≤-pred α<Δ)
```

## Plug Inversion

```
plug-inversion : ∀{M F A}
   → 0 ⨟ ∅ ⊢ plug M F ⦂ A
     --------------------------------------------------
   → Σ[ B ∈ Type ]
       0 ⨟ ∅ ⊢ M ⦂ B
     × (∀ M' → 0 ⨟ ∅ ⊢ M' ⦂ B  →  0 ⨟ ∅ ⊢ plug M' F ⦂ A)
plug-inversion {M} {□· N} {A} (⊢· {A = A'} ⊢M ⊢N) =
    ⟨ A' ⇒ A , ⟨ ⊢M , (λ M' z → ⊢· z ⊢N) ⟩ ⟩
plug-inversion {M} {(L ·□) v} {A} (⊢· {A = A'} ⊢L ⊢M) =
    ⟨ A' , ⟨ ⊢M , (λ M' → ⊢· ⊢L) ⟩ ⟩
plug-inversion {M} {□[·]} {A} (⊢[·] {A = A'} wf ⊢N) =
    ⟨ all A' , ⟨ ⊢N , (λ N' ⊢N' → ⊢[·] wf ⊢N') ⟩ ⟩
```

## Preservation

```
preserve : ∀ {M N A}
  → 0 ⨟ ∅ ⊢ M ⦂ A
  → M —→ N
    ----------
  → 0 ⨟ ∅ ⊢ N ⦂ A
preserve ⊢M (ξ {M}{M′} F M—→M′)
    with plug-inversion ⊢M
... | ⟨ B , ⟨ ⊢M' , plug-wt ⟩ ⟩ = plug-wt M′ (preserve ⊢M' M—→M′)
preserve (⊢· (⊢ƛ wf ⊢N) ⊢M) (β-ƛ vV) = substitution ⊢M ⊢N
preserve (⊢· (⊢$ refl) (⊢$ refl)) δ = ⊢$ refl
preserve (⊢[·] {B = B} wf (⊢Λ ⊢N)) β-Λ = type-substitution wf ⊢N
```
