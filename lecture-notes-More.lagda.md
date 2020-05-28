```
{-# OPTIONS --rewriting #-}

module lecture-notes-More where
```

# STLC + Primitives, Let, Arrays, and Errors


## Imports

```
import Syntax
open import Data.Bool renaming (Bool to 𝔹)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
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
  _⇒_ : Base → Prim → Prim
```

The `base-rep` and `rep` functions map from the type descriptors to
the Agda types that we will use to represent the constants.

```
base-rep : Base → Set 
base-rep B-Nat = ℕ
base-rep B-Bool = 𝔹

rep : Prim → Set
rep (base b) = base-rep b
rep (b ⇒ p) = base-rep b → rep p
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
  op-insert : Op
  op-empty  : Op
  op-index : Op
  op-error : Op

sig : Op → List ℕ
sig op-lam = 1 ∷ []
sig op-app = 0 ∷ 0 ∷ []
sig op-rec = 1 ∷ []
sig (op-const p k) = []
sig op-let = 0 ∷ 1 ∷ []
sig op-insert = 0 ∷ 0 ∷ []
sig op-empty = []
sig op-index = 0 ∷ 0 ∷ []
sig op-error = []

open Syntax using (Rename; _•_; ↑; id; ext; ⦉_⦊)

open Syntax.OpSig Op sig
  using (`_; _⦅_⦆; cons; nil; bind; ast; _[_]; Subst; ⟪_⟫; ⟦_⟧; exts; rename)
  renaming (ABT to Term)

infixl 7  _·_

pattern $ p k      = (op-const p k) ⦅ nil ⦆
pattern ƛ N        = op-lam         ⦅ cons (bind (ast N)) nil ⦆
pattern μ N        = op-rec         ⦅ cons (bind (ast N)) nil ⦆
pattern _·_ L M    = op-app         ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern `let L M   = op-let         ⦅ cons (ast L) (cons (bind (ast M)) nil) ⦆
pattern _⦂⦂_ L M    = op-insert      ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern 〈〉        = op-empty       ⦅ nil ⦆
pattern _!_ L M    = op-index       ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern error      = op-error       ⦅ nil ⦆
```

```
sub-lam : ∀ (N : Term) (σ : Subst) → ⟪ σ ⟫ (ƛ N) ≡ ƛ (⟪ exts σ ⟫ N)
sub-lam N σ = refl 

sub-app : ∀ (L M : Term) (σ : Subst) → ⟪ σ ⟫ (L · M) ≡ (⟪ σ ⟫ L) · (⟪ σ ⟫ M)
sub-app L M σ = refl
```

## Types

```
data Type : Set where
  Nat   : Type
  Bool   : Type
  _⇒_   : Type → Type → Type
  Array _  : Type → Type
```

## Type of a primitive

```
typeof-base : Base → Type
typeof-base B-Nat = Nat
typeof-base B-Bool = Bool

typeof : Prim → Type
typeof (base b) = typeof-base b 
typeof (b ⇒ p) = typeof-base b ⇒ typeof p
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

  ⊢empty : ∀{Γ A}
      ------------------
    → Γ ⊢ 〈〉 ⦂ Array A

  ⊢insert : ∀{Γ A M Ms}
    → Γ ⊢ M ⦂ A
    → Γ ⊢ Ms ⦂ Array A
      ----------------------
    → Γ ⊢ (M ⦂⦂ Ms) ⦂ Array A

  ⊢! : ∀{Γ A Ms N}
    → Γ ⊢ Ms ⦂ Array A
    → Γ ⊢ N ⦂ Nat
      ----------------
    → Γ ⊢ Ms ! N ⦂ A

  ⊢error : ∀ {Γ A}
      -------------
    → Γ ⊢ error ⦂ A
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

  V-〈〉 : Value 〈〉

  V-⦂⦂ : ∀ {V Vs : Term}
    → Value V
    → Value Vs
      -----------------
    → Value (V ⦂⦂ Vs)
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
  □⦂⦂_ : Term → Frame
  _⦂⦂□ : (M : Term) → (v : Value M) → Frame
  □!_ : Term → Frame
  _!□ : Term → Frame
  let□ : Term → Frame
```

The `plug` function fills a frame's hole with a term.

```
plug : Term → Frame → Term
plug L (□· M)        = L · M
plug M ((L ·□) v)    = L · M
plug M (□⦂⦂ N)       = M ⦂⦂ N
plug N ((M ⦂⦂□) v)   = M ⦂⦂ N
plug M (□! N)        = M ! N
plug N (M !□)        = M ! N
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

  lift-error :
      (F : Frame)
    → plug error F —→ error

  β-ƛ : ∀ {N V}
    → Value V
      --------------------
    → (ƛ N) · V —→ N [ V ]

  β-μ : ∀ {M}
      ----------------
    → μ M —→ M [ μ M ]

  δ : ∀ {b p f k}
      ---------------------------------------------
    → ($ (b ⇒ p) f) · ($ (base b) k) —→ ($ p (f k))

  β-index-0 : ∀ {V Vs}
    → Value (V ⦂⦂ Vs)
      -------------------------
    → (V ⦂⦂ Vs) ! ($ _ 0) —→  V

  β-index-suc : ∀ {V Vs i}
    → Value (V ⦂⦂ Vs)
      ------------------------------------------
    → (V ⦂⦂ Vs) ! ($ _ (suc i)) —→  Vs ! ($ _ i)

  β-index-error : ∀ {N}
      -----------------
    → 〈〉 ! N —→ error

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
  Fun-prim : ∀{b p k} → Function ($ (b ⇒ p) k)
  Fun-error : Function error

canonical-fun : ∀{V A B}
  → ∅ ⊢ V ⦂ A ⇒ B
  → Value V
    ----------
  → Function V
canonical-fun ⊢V V-ƛ = Fun-ƛ
canonical-fun (⊢$ {p = base B-Nat} ()) (V-const {_} {k})
canonical-fun (⊢$ {p = base B-Bool} ()) (V-const {_} {k})
canonical-fun (⊢$ {p = b ⇒ p} eq) (V-const {_} {k}) = Fun-prim

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
canonical-base {B-Nat} refl (⊢$ {p = b' ⇒ p} ()) V-const
canonical-base {B-Bool} refl (⊢$ {p = b' ⇒ p} ()) V-const
canonical-base {B-Nat} () (⊢insert ⊢V ⊢V₁) (V-⦂⦂ vV vV₁)
canonical-base {B-Bool} () (⊢insert ⊢V ⊢V₁) (V-⦂⦂ vV vV₁)

data IsArray : Term → Set where
  array-empty : IsArray 〈〉
  array-insert : ∀{V Vs} → IsArray Vs → IsArray (V ⦂⦂ Vs)
 
canonical-array : ∀ {Ms A}
  → ∅ ⊢ Ms ⦂ Array A
  → Value Ms
  → IsArray Ms
canonical-array (⊢$ {p = base B-Nat} ()) V-const
canonical-array (⊢$ {p = base B-Bool} ()) V-const
canonical-array ⊢empty V-〈〉 = array-empty
canonical-array (⊢insert ⊢M ⊢Ms) (V-⦂⦂ VM VMs) =
    array-insert (canonical-array ⊢Ms VMs)
```


## Progress

```
data Error : Term → Set where
  is-error : Error error
```

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

  trapped-error :
      Error M
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
... | trapped-error is-error                = step (lift-error (□· M))
... | done VL
        with progress ⊢M
...     | step M—→M′                        = step (ξ ((L ·□) VL) M—→M′)
...     | trapped-error is-error            = step (lift-error ((L ·□) VL))
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
... | trapped-error is-error                = step (lift-error (let□ N))
... | done VL                               = step (β-let VL)
progress ⊢empty                             = done V-〈〉
progress (⊢insert {M = M}{Ms} ⊢M ⊢Ms)
    with progress ⊢M
... | step M—→M′                            = step (ξ (□⦂⦂ Ms) M—→M′)
... | trapped-error is-error                = step (lift-error (□⦂⦂ Ms))
... | done VM
        with progress ⊢Ms
...     | step Ms—→Ms′                      = step (ξ ((M ⦂⦂□) VM) Ms—→Ms′)
...     | trapped-error is-error            = step (lift-error ((M ⦂⦂□) VM))
...     | done VMs                          = done (V-⦂⦂ VM VMs)
progress (⊢! {Ms = M}{N} ⊢M ⊢N)
    with progress ⊢M
... | step M—→M′                            = step (ξ (□! N) M—→M′)
... | trapped-error is-error                = step (lift-error (□! N))
... | done VMs
        with progress ⊢N
...     | step N—→N′                        = step (ξ (M !□) N—→N′)
...     | trapped-error is-error            = step (lift-error (M !□))
...     | done VN
            with canonical-array ⊢M VMs
...         | array-empty                   = step β-index-error
...         | array-insert aVs
            with canonical-base refl ⊢N VN
...         | base-const {b}{0}             = step (β-index-0 VMs)
...         | base-const {b}{suc i}         = step (β-index-suc VMs)
progress ⊢error                             = trapped-error is-error
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
ext-pres {ρ = ρ } ⊢ρ Z =  Z
ext-pres {ρ = ρ } ⊢ρ (S {x = x} ∋x) =  S (⊢ρ ∋x)
```

```
rename-pres : ∀ {Γ Δ ρ M A}
  → WTRename Γ ρ Δ
  → Γ ⊢ M ⦂ A
    ------------------
  → Δ ⊢ rename ρ M ⦂ A
rename-pres ⊢ρ (⊢` ∋w)            =  ⊢` (⊢ρ ∋w)
rename-pres {ρ = ρ} ⊢ρ (⊢ƛ ⊢N)    =  ⊢ƛ (rename-pres {ρ = ext ρ} (ext-pres {ρ = ρ} ⊢ρ) ⊢N)
rename-pres {ρ = ρ} ⊢ρ (⊢· ⊢L ⊢M) =  ⊢· (rename-pres {ρ = ρ} ⊢ρ ⊢L) (rename-pres {ρ = ρ} ⊢ρ ⊢M)
rename-pres {ρ = ρ} ⊢ρ (⊢μ ⊢M)    =  ⊢μ (rename-pres {ρ = ext ρ} (ext-pres {ρ = ρ} ⊢ρ) ⊢M)
rename-pres ⊢ρ (⊢$ eq)            = ⊢$ eq
rename-pres {ρ = ρ} ⊢ρ (⊢let ⊢M ⊢N) =
    ⊢let (rename-pres {ρ = ρ} ⊢ρ ⊢M) (rename-pres {ρ = ext ρ} (ext-pres {ρ = ρ} ⊢ρ) ⊢N)
rename-pres ⊢ρ ⊢empty = ⊢empty
rename-pres {ρ = ρ} ⊢ρ (⊢insert ⊢M ⊢Ms) =
    ⊢insert (rename-pres {ρ = ρ} ⊢ρ ⊢M) (rename-pres {ρ = ρ} ⊢ρ ⊢Ms)
rename-pres {ρ = ρ} ⊢ρ (⊢! ⊢Ms ⊢N)       = ⊢! (rename-pres {ρ = ρ} ⊢ρ ⊢Ms) (rename-pres {ρ = ρ} ⊢ρ ⊢N)
rename-pres ⊢ρ ⊢error            = ⊢error
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
exts-pres {σ = σ} Γ⊢σ Z = ⊢` Z
exts-pres {σ = σ} Γ⊢σ (S {x = x} ∋x) = rename-pres {ρ = ↑ 1} S (Γ⊢σ ∋x)
```

```
subst : ∀ {Γ Δ σ N A}
  → WTSubst Γ σ Δ
  → Γ ⊢ N ⦂ A
    ---------------
  → Δ ⊢ ⟪ σ ⟫ N ⦂ A
subst Γ⊢σ (⊢` eq)              = Γ⊢σ eq
subst {σ = σ} Γ⊢σ (⊢ƛ ⊢N)      = ⊢ƛ (subst {σ = exts σ} (exts-pres {σ = σ} Γ⊢σ) ⊢N) 
subst {σ = σ} Γ⊢σ (⊢· ⊢L ⊢M)           = ⊢· (subst {σ = σ} Γ⊢σ ⊢L) (subst {σ = σ} Γ⊢σ ⊢M) 
subst {σ = σ} Γ⊢σ (⊢μ ⊢M)      = ⊢μ (subst {σ = exts σ} (exts-pres {σ = σ} Γ⊢σ) ⊢M) 
subst Γ⊢σ (⊢$ e) = ⊢$ e 
subst {σ = σ} Γ⊢σ (⊢let ⊢M ⊢N) =
    ⊢let (subst {σ = σ} Γ⊢σ ⊢M) (subst {σ = exts σ} (exts-pres {σ = σ} Γ⊢σ) ⊢N) 
subst Γ⊢σ ⊢empty               = ⊢empty
subst {σ = σ} Γ⊢σ (⊢insert ⊢M ⊢Ms)= ⊢insert (subst {σ = σ} Γ⊢σ ⊢M) (subst {σ = σ} Γ⊢σ ⊢Ms) 
subst {σ = σ} Γ⊢σ (⊢! ⊢M ⊢N)   = ⊢! (subst {σ = σ} Γ⊢σ ⊢M) (subst {σ = σ} Γ⊢σ ⊢N) 
subst Γ⊢σ ⊢error               = ⊢error
```

```
substitution : ∀{Γ A B M N}
   → Γ ⊢ M ⦂ A
   → (Γ , A) ⊢ N ⦂ B
     ---------------
   → Γ ⊢ N [ M ] ⦂ B
substitution {Γ}{A}{B}{M}{N} ⊢M ⊢N = subst {σ = M • ↑ 0 } G ⊢N
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
plug-inversion {M} {□⦂⦂ Ms} {.(Array _)} (⊢insert {A = A} ⊢M ⊢Ms) =
    ⟨ A , ⟨ ⊢M , (λ M' z → ⊢insert z ⊢Ms) ⟩ ⟩
plug-inversion {M} {(N ⦂⦂□) v} {.(Array _)} (⊢insert {A = A} ⊢N ⊢M) =
    ⟨ Array A , ⟨ ⊢M , (λ M' → ⊢insert ⊢N) ⟩ ⟩
plug-inversion {M} {□! i} {A} (⊢! ⊢M ⊢N) =
    ⟨ (Array A) , ⟨ ⊢M , (λ M' z → ⊢! z ⊢N) ⟩ ⟩
plug-inversion {M} {Ms !□} {A} (⊢! ⊢M ⊢N) =
    ⟨ Nat , ⟨ ⊢N , (λ M' → ⊢! ⊢M) ⟩ ⟩
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
preserve ⊢M (lift-error F) = ⊢error
preserve (⊢· (⊢ƛ ⊢N) ⊢M) (β-ƛ vV) = substitution ⊢M ⊢N
preserve (⊢μ ⊢M) β-μ = substitution (⊢μ ⊢M) ⊢M
preserve (⊢· (⊢$ refl) (⊢$ refl)) δ = ⊢$ refl
preserve (⊢! (⊢insert ⊢M ⊢Ms) ⊢N) (β-index-0 vMMs) = ⊢M
preserve (⊢! (⊢insert ⊢M ⊢Ms) ⊢N) (β-index-suc vVVs) = ⊢! ⊢Ms (⊢$ refl)
preserve ⊢M β-index-error = ⊢error
preserve (⊢let ⊢M ⊢N) (β-let vV) = substitution ⊢M ⊢N
```
