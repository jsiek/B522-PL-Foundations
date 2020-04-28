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
open import Data.Nat using (ℕ; zero; suc; _<_)
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
  renaming (ABT to Type; `_ to tyvar; _⦅_⦆ to _〘_〙;
            cons to tycons; nil to tynil; bind to tybind; ast to tyast;
            _[_] to _⦗_⦘; Subst to TySubst)


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

  ⊢$ : ∀{Γ Δ p k A}
     → A ≡ typeof p
       -------------
     → Γ ⨟ Δ ⊢ $ p k ⦂ A

  ⊢Λ : ∀ {Γ Δ A N}
    → Γ ⨟ suc Δ ⊢ N ⦂ A
      ----------------------
    → Γ ⨟ Δ ⊢ Λ N ⦂ all A

  ⊢[·] : ∀{Γ Δ A B N}
    → Δ ⊢ B
    → Γ ⨟ Δ ⊢ N ⦂ all A
      ----------------------
    → Γ ⨟ Δ ⊢ N [·] ⦂ A ⦗ B ⦘
```
