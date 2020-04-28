```
{-# OPTIONS --rewriting #-}

module SystemF where
```

# SystemF


## Imports

```
import Syntax
open import Data.Bool using () renaming (Bool to 𝔹)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-step; ≤-refl)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
   renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)

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

open Syntax using (Rename; _•_; ↑; id; ext; ⦉_⦊)

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
  using ()
  renaming (ABT to Type; `_ to tyvar; _⦅_⦆ to _〘_〙;
            cons to tycons; nil to tynil; bind to tybind; ast to tyast;
            _[_] to _⦗_⦘; Subst to TySubst; ⟪_⟫ to ⸂_⸃; ⟦_⟧ to ⧼_⧽)

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

data _⨟_⊢_⦂_ : Context → ℕ → Term → Type → Set where

  -- Constants
  ⊢$ : ∀{Γ Δ p k A}
     → A ≡ typeof p
       -------------
     → Γ ⨟ Δ ⊢ $ p k ⦂ A

  -- Axiom 
  ⊢` : ∀ {Γ Δ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⨟ Δ ⊢ ` x ⦂ A

  -- ⇒-I 
  ⊢ƛ : ∀ {Γ Δ N A B}
    → Δ ⊢ A
    → Γ , A ⨟ Δ ⊢ N ⦂ B
      -------------------
    → Γ ⨟ Δ ⊢ ƛ N ⦂ A ⇒ B

  -- ⇒-E
  ⊢· : ∀ {Γ Δ L M A B}
    → Γ ⨟ Δ ⊢ L ⦂ A ⇒ B
    → Γ ⨟ Δ ⊢ M ⦂ A
      -------------
    → Γ ⨟ Δ ⊢ L · M ⦂ B

  -- all-I
  ⊢Λ : ∀ {Γ Δ A N}
    → Γ ⨟ suc Δ ⊢ N ⦂ A
      ----------------------
    → Γ ⨟ Δ ⊢ Λ N ⦂ all A

  -- all-E
  ⊢[·] : ∀{Γ Δ A B N}
    → Δ ⊢ B
    → Γ ⨟ Δ ⊢ N ⦂ all A
      ----------------------
    → Γ ⨟ Δ ⊢ N [·] ⦂ A ⦗ B ⦘
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
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : Term → Term → Set where
  _∎ : ∀ M
      ---------
    → M —↠ M

  _—→⟨_⟩_ : ∀ L {M N}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

begin_ : ∀ {M N}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N
```

## Canonical Forms

```
data Function : Term → Set where
  Fun-ƛ : ∀ {N} → Function (ƛ N)
  Fun-prim : ∀{b p k} → Function ($ (b ⇛ p) k)

canonical-fun : ∀{V A B}
  → ∅ ⨟ 0 ⊢ V ⦂ A ⇒ B
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
  → ∅ ⨟ 0 ⊢ V ⦂ A
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
  → ∅ ⨟ 0 ⊢ V ⦂ all A
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
  → ∅ ⨟ 0 ⊢ M ⦂ A
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

## Renaming and substitution

```
WTRename : Context → Rename → Context → Set
WTRename Γ ρ Γ′ = ∀ {x A} → Γ ∋ x ⦂ A → Γ′ ∋ ⦉ ρ ⦊ x ⦂ A
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
  → Γ ⨟ Δ ⊢ M ⦂ A
    ------------------
  → Γ′ ⨟ Δ ⊢ rename ρ M ⦂ A
rename-pres ⊢ρ (⊢$ eq)              = ⊢$ eq
rename-pres ⊢ρ (⊢` ∋w)              =  ⊢` (⊢ρ ∋w)
rename-pres {ρ = ρ} ⊢ρ (⊢ƛ wf ⊢N)   =
    ⊢ƛ wf (rename-pres {ρ = ext ρ} (ext-pres {ρ = ρ} ⊢ρ) ⊢N)
rename-pres {ρ = ρ} ⊢ρ (⊢· ⊢L ⊢M)   =
    ⊢· (rename-pres {ρ = ρ} ⊢ρ ⊢L) (rename-pres {ρ = ρ} ⊢ρ ⊢M)
rename-pres {ρ = ρ} ⊢ρ (⊢Λ ⊢N)      = ⊢Λ (rename-pres {ρ = ρ} ⊢ρ ⊢N)
rename-pres {ρ = ρ} ⊢ρ (⊢[·] wf ⊢N) = ⊢[·] wf (rename-pres {ρ = ρ} ⊢ρ ⊢N)
```

```
WTSubst : Context → ℕ → Subst → Context → Set
WTSubst Γ Δ σ Γ′ = ∀ {A x} → Γ ∋ x ⦂ A → Γ′ ⨟ Δ ⊢ ⟪ σ ⟫ (` x) ⦂ A
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
weaken-ty : ∀{Δ Δ′ A}
   → Δ ≤ Δ′
   → Δ ⊢ A
   → Δ′ ⊢ A
weaken-ty Δ≤Δ′ (⊢var α<Δ) = ⊢var (≤-trans α<Δ Δ≤Δ′)
weaken-ty Δ≤Δ′ ⊢nat = ⊢nat
weaken-ty Δ≤Δ′ ⊢bool = ⊢bool
weaken-ty Δ≤Δ′ (⊢fun ⊢A ⊢B) = ⊢fun (weaken-ty Δ≤Δ′ ⊢A) (weaken-ty Δ≤Δ′ ⊢B)
weaken-ty Δ≤Δ′ (⊢all ⊢A) = ⊢all (weaken-ty (s≤s Δ≤Δ′) ⊢A)
```

```
weaken-tyenv : ∀{Γ Δ Δ′ M A}
   → Δ ≤ Δ′
   → Γ ⨟ Δ ⊢ M ⦂ A
   → Γ ⨟ Δ′ ⊢ M ⦂ A
weaken-tyenv Δ≤Δ′ (⊢$ x) = ⊢$ x
weaken-tyenv Δ≤Δ′ (⊢` x) = ⊢` x
weaken-tyenv Δ≤Δ′ (⊢ƛ wf ⊢N) = ⊢ƛ (weaken-ty Δ≤Δ′ wf) (weaken-tyenv Δ≤Δ′ ⊢N)
weaken-tyenv Δ≤Δ′ (⊢· ⊢L ⊢M) = ⊢· (weaken-tyenv Δ≤Δ′ ⊢L) (weaken-tyenv Δ≤Δ′ ⊢M)
weaken-tyenv Δ≤Δ′ (⊢Λ ⊢M) = ⊢Λ (weaken-tyenv (s≤s Δ≤Δ′) ⊢M)
weaken-tyenv Δ≤Δ′ (⊢[·] wf ⊢M) = ⊢[·] (weaken-ty Δ≤Δ′ wf) (weaken-tyenv Δ≤Δ′ ⊢M)
```


```
subst : ∀ {Γ Γ′ σ N A Δ}
  → WTSubst Γ Δ σ Γ′
  → Γ ⨟ Δ ⊢ N ⦂ A
    ---------------
  → Γ′ ⨟ Δ ⊢ ⟪ σ ⟫ N ⦂ A
subst Γ⊢σ (⊢$ e) = ⊢$ e 
subst Γ⊢σ (⊢` eq)           = Γ⊢σ eq
subst {σ = σ} Γ⊢σ (⊢ƛ wf ⊢N) = ⊢ƛ wf (subst {σ = exts σ} (exts-pres {σ = σ} Γ⊢σ) ⊢N) 
subst {σ = σ} Γ⊢σ (⊢· ⊢L ⊢M) = ⊢· (subst {σ = σ} Γ⊢σ ⊢L) (subst {σ = σ} Γ⊢σ ⊢M) 
subst {Γ}{Γ′}{σ}{Δ = Δ} Γ⊢σ (⊢Λ ⊢N)   = ⊢Λ (subst {σ = σ} G ⊢N)
  where
  G : WTSubst Γ (suc Δ) σ Γ′
  G {A}{x} ∋x =
    let yy = Γ⊢σ {A}{x} ∋x in
    weaken-tyenv (≤-step ≤-refl) yy
subst {σ = σ} Γ⊢σ (⊢[·] wf ⊢N) = ⊢[·] wf (subst {σ = σ} Γ⊢σ ⊢N)
```

```
substitution : ∀{Γ Δ A B M N}
   → Γ ⨟ Δ ⊢ M ⦂ A
   → (Γ , A) ⨟ Δ ⊢ N ⦂ B
     ---------------
   → Γ ⨟ Δ ⊢ N [ M ] ⦂ B
substitution {Γ}{Δ}{A}{B}{M}{N} ⊢M ⊢N = subst {σ = M • ↑ 0 } G ⊢N
    where
    G : WTSubst (Γ , A) Δ (M • ↑ 0) Γ
    G {A₁} {zero} Z = ⊢M
    G {A₁} {suc x} (S ∋x) = ⊢` ∋x
```

## Type Substitution

```
subst-base : ∀ σ b
   → ⸂ σ ⸃ (typeof-base b) ≡ typeof-base b
subst-base σ B-Nat = refl
subst-base σ B-Bool = refl

subst-prim : ∀ σ p
   → ⸂ σ ⸃ (typeof p) ≡ typeof p
subst-prim σ (base B-Nat) = refl
subst-prim σ (base B-Bool) = refl
subst-prim σ (b ⇛ p)
    with subst-base σ b | subst-prim σ p
... | eq1 | eq2 rewrite eq1 | eq2 = refl 
```

```
ctx-subst : TySubst → Context → Context
ctx-subst σ ∅ = ∅
ctx-subst σ (Γ , A) = ctx-subst σ Γ , ⸂ σ ⸃ A
```

```
ctx-subst-pres : ∀{Γ x A σ}
  → Γ ∋ x ⦂ A
  → ctx-subst σ Γ ∋ x ⦂ ⸂ σ ⸃ A
ctx-subst-pres Z = Z
ctx-subst-pres (S ∋x) = S (ctx-subst-pres ∋x)
```

```
WFSubst : ℕ → TySubst → ℕ → Set
WFSubst Δ σ Δ′ = ∀{α} → α < Δ → Δ′ ⊢ ⧼ σ ⧽ α
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
subst-pres-wf ΔσΔ′ (⊢all ⊢A) = ⊢all {!!}
```

```
ty-subst : ∀{σ : TySubst}{Δ Δ′}{Γ}{N}{A}
  → WFSubst Δ σ Δ′
  → Γ ⨟ Δ ⊢ N ⦂ A
    -------------------------------
  → ctx-subst σ Γ ⨟ Δ′ ⊢ N ⦂ ⸂ σ ⸃ A
ty-subst {σ} ΔσΔ′ (⊢$ {p = p} refl) = ⊢$ (subst-prim σ p)
ty-subst {σ} ΔσΔ′ (⊢` ∋x) = ⊢` (ctx-subst-pres ∋x)
ty-subst {σ} ΔσΔ′ (⊢ƛ wf ⊢N) =
  ⊢ƛ (subst-pres-wf {σ} ΔσΔ′ wf) (ty-subst {σ} ΔσΔ′ ⊢N)
ty-subst {σ} ΔσΔ′ (⊢· ⊢L ⊢M) = ⊢· (ty-subst {σ} ΔσΔ′ ⊢L) (ty-subst {σ} ΔσΔ′ ⊢M)
ty-subst {σ} ΔσΔ′ (⊢Λ ⊢N) = ⊢Λ {!!}
ty-subst {σ} ΔσΔ′ (⊢[·] wf ⊢N) = {!!}
```

## Plug Inversion

```
plug-inversion : ∀{M F A}
   → ∅ ⨟ 0 ⊢ plug M F ⦂ A
     --------------------------------------------------------------------------
   → Σ[ B ∈ Type ]
       ∅ ⨟ 0 ⊢ M ⦂ B
     × (∀ M' → ∅ ⨟ 0 ⊢ M' ⦂ B → ∅ ⨟ 0 ⊢ plug M' F ⦂ A)
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
  → ∅ ⨟ 0 ⊢ M ⦂ A
  → M —→ N
    ----------
  → ∅ ⨟ 0 ⊢ N ⦂ A
preserve ⊢M (ξ {M}{M′} F M—→M′)
    with plug-inversion ⊢M
... | ⟨ B , ⟨ ⊢M' , plug-wt ⟩ ⟩ = plug-wt M′ (preserve ⊢M' M—→M′)
preserve (⊢· (⊢ƛ wf ⊢N) ⊢M) (β-ƛ vV) = substitution ⊢M ⊢N
preserve (⊢· (⊢$ refl) (⊢$ refl)) δ = ⊢$ refl
preserve (⊢[·] wf (⊢Λ ⊢N)) β-Λ = {!!}
```
