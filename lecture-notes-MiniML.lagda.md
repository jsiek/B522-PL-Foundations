```
module lecture-notes-MiniML where
```

# MiniML


## Imports

```
import Syntax
open import Data.Bool using () renaming (Bool to 𝔹)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe
open import Data.Vec using (Vec; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
   renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Relation.Nullary using (Dec; yes; no)

import UnifyMM
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
  pfun : Base → Prim → Prim
```

The `base-rep` and `rep` functions map from the type descriptors to
the Agda types that we will use to represent the constants.

```
base-rep : Base → Set 
base-rep B-Nat = ℕ
base-rep B-Bool = 𝔹

rep : Prim → Set
rep (base b) = base-rep b
rep (pfun b p) = base-rep b → rep p
```

## Terms

We use the
[abstract-binding-trees](https://github.com/jsiek/abstract-binding-trees)
library to represent terms.

```
data Op : Set where
  op-lam : Op
  op-app : Op
  op-rec : Op
  op-const : (p : Prim) → rep p → Op
  op-let : Op

sig : Op → List ℕ
sig op-lam = 1 ∷ []
sig op-app = 0 ∷ 0 ∷ []
sig op-rec = 1 ∷ []
sig (op-const p k) = []
sig op-let = 0 ∷ 1 ∷ []

open Syntax Op sig
  using (`_; _⦅_⦆; cons; nil; bind; ast; _[_];
         Rename; Subst; ⟪_⟫; ⟦_⟧; exts; _•_; 
         ↑; _⨟_; exts-0; exts-suc-rename; rename; ext; ⦉_⦊;
         ext-0; ext-suc; WF; WF-var)
  renaming (ABT to Term)

pattern $ p k = (op-const p k) ⦅ nil ⦆

pattern ƛ N  = op-lam ⦅ cons (bind (ast N)) nil ⦆

pattern μ N  = op-rec ⦅ cons (bind (ast N)) nil ⦆

infixl 7  _·_
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆

pattern `let L M = op-let ⦅ cons (ast L) (cons (bind (ast M)) nil) ⦆
```

```
sub-lam : ∀ (N : Term) (σ : Subst) → ⟪ σ ⟫ (ƛ N) ≡ ƛ (⟪ exts σ ⟫ N)
sub-lam N σ = refl 

sub-app : ∀ (L M : Term) (σ : Subst) → ⟪ σ ⟫ (L · M) ≡ (⟪ σ ⟫ L) · (⟪ σ ⟫ M)
sub-app L M σ = refl
```

## Types

```
data TyOp : Set where
  op-nat : TyOp
  op-bool : TyOp
  op-fun : TyOp
  
arity : TyOp → ℕ
arity op-nat = 0
arity op-bool = 0
arity op-fun = 2

tyop-eq : (a : TyOp) → (b : TyOp) → Dec (a ≡ b)
tyop-eq op-nat op-nat = yes refl
tyop-eq op-nat op-bool = no (λ ())
tyop-eq op-nat op-fun = no (λ ())
tyop-eq op-bool op-nat = no (λ ())
tyop-eq op-bool op-bool = yes refl
tyop-eq op-bool op-fun = no (λ ())
tyop-eq op-fun op-nat = no (λ ())
tyop-eq op-fun op-bool = no (λ ())
tyop-eq op-fun op-fun = yes refl

open UnifyMM TyOp tyop-eq arity
  renaming (AST to Type; _⦅_⦆ to _❨_❩; subst to subst-ty)

Nat = op-nat ❨ [] ❩
Bool = op-bool ❨ [] ❩

_⇒_ : Type → Type → Type
A ⇒ B = op-fun ❨ A ∷ B ∷ [] ❩
```

## Type of a primitive

```
typeof-base : Base → Type
typeof-base B-Nat = Nat
typeof-base B-Bool = Bool

typeof : Prim → Type
typeof (base b) = typeof-base b 
typeof (pfun b p) = typeof-base b ⇒ typeof p
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

## Typing judgement


```
infix  4  _⊢_⦂_

data _⊢_⦂_ : Context → Term → Type → Set where

  -- Axiom 
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ⦂ A

  -- ⇒-I 
  ⊢ƛ : ∀ {Γ N A B}
    → Γ , A ⊢ N ⦂ B
      -------------------
    → Γ ⊢ ƛ N ⦂ A ⇒ B

  -- ⇒-E
  ⊢· : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B

  ⊢μ : ∀ {Γ M A}
    → Γ , A ⊢ M ⦂ A
      -----------------
    → Γ ⊢ μ M ⦂ A

  ⊢$ : ∀{Γ p k A}
     → A ≡ typeof p
       -------------
     → Γ ⊢ $ p k ⦂ A

  ⊢let : ∀{Γ A B M N}
    → Γ ⊢ M ⦂ A
    → Γ , A ⊢ N ⦂ B
      -----------------
    → Γ ⊢ `let M N ⦂ B
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
```

## Frames and plug

With the addition of errors, one would need to add many more rules for
propagating an error to the top of the program. We instead collapse
these rules, and the ξ rules, into just two rules by abstracting over
the notion of a _frame_, which controls how reduction can occur inside
of each term constructor. Think of the `□` symbol is a hole in the term.

```
data Frame : Set where
  □·_ : Term → Frame
  _·□ : (M : Term) → (v : Value M) → Frame
  let□ : Term → Frame
```

The `plug` function fills a frame's hole with a term.

```
plug : Term → Frame → Term
plug L (□· M)        = L · M
plug M ((L ·□) v)    = L · M
plug M (let□ N)      = `let M N
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

  β-μ : ∀ {M}
      ----------------
    → μ M —→ M [ μ M ]

  δ : ∀ {b p f k}
      ---------------------------------------------
    → ($ (pfun b p) f) · ($ (base b) k) —→ ($ p (f k))

  β-let : ∀{V N}
    → Value V
      -------------------
    → `let V N —→ N [ V ]
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
  Fun-prim : ∀{b p k} → Function ($ (pfun b p) k)

canonical-fun : ∀{V A B}
  → ∅ ⊢ V ⦂ A ⇒ B
  → Value V
    ----------
  → Function V
canonical-fun ⊢V V-ƛ = Fun-ƛ
canonical-fun (⊢$ {p = base B-Nat} ()) (V-const {_} {k})
canonical-fun (⊢$ {p = base B-Bool} ()) (V-const {_} {k})
canonical-fun (⊢$ {p = pfun b p} eq) (V-const {_} {k}) = Fun-prim

data Constant : Base → Term → Set where
  base-const : ∀{b k} → Constant b ($ (base b) k)

canonical-base : ∀{b V A}
  → A ≡ typeof-base b
  → ∅ ⊢ V ⦂ A
  → Value V
    ------------
  → Constant b V
canonical-base {B-Nat} () (⊢ƛ ⊢V) V-ƛ
canonical-base {B-Bool} () (⊢ƛ ⊢V) V-ƛ
canonical-base {B-Nat} eq (⊢$ {p = base B-Nat} refl) V-const = base-const
canonical-base {B-Bool} eq (⊢$ {p = base B-Bool} refl) V-const = base-const
canonical-base {B-Nat} refl (⊢$ {p = pfun b' p} ()) V-const
canonical-base {B-Bool} refl (⊢$ {p = pfun b' p} ()) V-const
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
  → ∅ ⊢ M ⦂ A
    ----------
  → Progress M
progress (⊢` ())
progress (⊢$ _)                             = done V-const
progress (⊢ƛ ⊢N)                            = done V-ƛ
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
progress (⊢μ ⊢M)                            = step β-μ
progress (⊢let {N = N} ⊢L ⊢N)
    with progress ⊢L
... | step L—→L′                            = step (ξ (let□ N) L—→L′)
... | done VL                               = step (β-let VL)
```

## Renaming and substitution

```
WTRename : Context → Rename → Context → Set
WTRename Γ ρ Δ = ∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ ⦉ ρ ⦊ x ⦂ A
```

```
ext-pres : ∀ {Γ Δ ρ B}
  → WTRename Γ ρ Δ
    --------------------------------
  → WTRename (Γ , B) (ext ρ) (Δ , B)
ext-pres {ρ = ρ } ⊢ρ Z
    rewrite ext-0 ρ =  Z
ext-pres {ρ = ρ } ⊢ρ (S {x = x} ∋x)
    rewrite ext-suc ρ x =  S (⊢ρ ∋x)
```

```
rename-pres : ∀ {Γ Δ ρ M A}
  → WTRename Γ ρ Δ
  → Γ ⊢ M ⦂ A
    ------------------
  → Δ ⊢ rename ρ M ⦂ A
rename-pres ⊢ρ (⊢` ∋w)           =  ⊢` (⊢ρ ∋w)
rename-pres {ρ = ρ} ⊢ρ (⊢ƛ ⊢N)   =  ⊢ƛ (rename-pres (ext-pres {ρ = ρ} ⊢ρ) ⊢N)
rename-pres ⊢ρ (⊢· ⊢L ⊢M)        =  ⊢· (rename-pres ⊢ρ ⊢L) (rename-pres ⊢ρ ⊢M)
rename-pres {ρ = ρ} ⊢ρ (⊢μ ⊢M)   =  ⊢μ (rename-pres (ext-pres {ρ = ρ} ⊢ρ) ⊢M)
rename-pres ⊢ρ (⊢$ eq)           = ⊢$ eq
rename-pres {ρ = ρ} ⊢ρ (⊢let ⊢M ⊢N) =
    ⊢let (rename-pres ⊢ρ ⊢M) (rename-pres (ext-pres {ρ = ρ} ⊢ρ) ⊢N)
```

```
WTSubst : Context → Subst → Context → Set
WTSubst Γ σ Δ = ∀ {A x} → Γ ∋ x ⦂ A → Δ ⊢ ⟪ σ ⟫ (` x) ⦂ A
```

```
exts-pres : ∀ {Γ Δ σ B}
  → WTSubst Γ σ Δ
    --------------------------------
  → WTSubst (Γ , B) (exts σ) (Δ , B)
exts-pres {σ = σ} Γ⊢σ Z
    rewrite exts-0 σ = ⊢` Z
exts-pres {σ = σ} Γ⊢σ (S {x = x} ∋x)
    rewrite exts-suc-rename σ x = rename-pres S (Γ⊢σ ∋x)
```

```
subst : ∀ {Γ Δ σ N A}
  → WTSubst Γ σ Δ
  → Γ ⊢ N ⦂ A
    ---------------
  → Δ ⊢ ⟪ σ ⟫ N ⦂ A
subst Γ⊢σ (⊢` eq)              = Γ⊢σ eq
subst {σ = σ} Γ⊢σ (⊢ƛ ⊢N)      = ⊢ƛ (subst (exts-pres {σ = σ} Γ⊢σ) ⊢N) 
subst Γ⊢σ (⊢· ⊢L ⊢M)           = ⊢· (subst Γ⊢σ ⊢L) (subst Γ⊢σ ⊢M) 
subst {σ = σ} Γ⊢σ (⊢μ ⊢M)      = ⊢μ (subst (exts-pres {σ = σ} Γ⊢σ) ⊢M) 
subst Γ⊢σ (⊢$ e) = ⊢$ e 
subst {σ = σ} Γ⊢σ (⊢let ⊢M ⊢N) =
    ⊢let (subst Γ⊢σ ⊢M) (subst (exts-pres {σ = σ} Γ⊢σ) ⊢N) 
```

```
substitution : ∀{Γ A B M N}
   → Γ ⊢ M ⦂ A
   → (Γ , A) ⊢ N ⦂ B
     ---------------
   → Γ ⊢ N [ M ] ⦂ B
substitution {Γ}{A}{B}{M}{N} ⊢M ⊢N = subst G ⊢N
    where
    G : ∀ {A₁ : Type} {x : ℕ}
      → (Γ , A) ∋ x ⦂ A₁ → Γ ⊢ ⟪ M • ↑ 0 ⟫ (` x) ⦂ A₁
    G {A₁} {zero} Z = ⊢M
    G {A₁} {suc x} (S ∋x) = ⊢` ∋x
```

## Plug Inversion

```
plug-inversion : ∀{M F A}
   → ∅ ⊢ plug M F ⦂ A
     ----------------------------------------------------------------
   → Σ[ B ∈ Type ] ∅ ⊢ M ⦂ B × (∀ M' → ∅ ⊢ M' ⦂ B → ∅ ⊢ plug M' F ⦂ A)
plug-inversion {M} {□· N} {A} (⊢· {A = A'} ⊢M ⊢N) =
    ⟨ A' ⇒ A , ⟨ ⊢M , (λ M' z → ⊢· z ⊢N) ⟩ ⟩
plug-inversion {M} {(L ·□) v} {A} (⊢· {A = A'} ⊢L ⊢M) =
    ⟨ A' , ⟨ ⊢M , (λ M' → ⊢· ⊢L) ⟩ ⟩
plug-inversion {M} {let□ N} {A} (⊢let {A = A'} ⊢M ⊢N) =
    ⟨ A' , ⟨ ⊢M , (λ M' z → ⊢let z ⊢N) ⟩ ⟩
```

## Preservation

```
preserve : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —→ N
    ----------
  → ∅ ⊢ N ⦂ A
preserve ⊢M (ξ {M}{M′} F M—→M′)
    with plug-inversion ⊢M
... | ⟨ B , ⟨ ⊢M' , plug-wt ⟩ ⟩ = plug-wt M′ (preserve ⊢M' M—→M′)
preserve (⊢· (⊢ƛ ⊢N) ⊢M) (β-ƛ vV) = substitution ⊢M ⊢N
preserve (⊢μ ⊢M) β-μ = substitution (⊢μ ⊢M) ⊢M
preserve (⊢· (⊢$ refl) (⊢$ refl)) δ = ⊢$ refl
preserve (⊢let ⊢M ⊢N) (β-let vV) = substitution ⊢M ⊢N
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

## Type Inferece

```
𝒲 : (Γ : Context) → (M : Term) → WF (len Γ) M → ℕ 
   → Maybe (Σ[ σ ∈ Equations ] Σ[ A ∈ Type ] subst-env σ Γ ⊢ M ⦂ A × ℕ)
𝒲 Γ (` x) (WF-var .x x<Γ) n
    with <-∋ x<Γ
... | ⟨ A , Γ∋x ⟩ =
    just ⟨ [] , ⟨ A , ⟨ (⊢` G) , n ⟩ ⟩ ⟩
    where G : subst-env [] Γ ∋ x ⦂ A
          G rewrite subst-env-empty Γ = Γ∋x
𝒲 Γ (op Syntax.⦅ x ⦆) wfm n = {!!}
```
