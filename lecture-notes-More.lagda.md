```
module lecture-notes-More where
```

# Primitives, Let, Arrays, and Errors


## Imports

```
import Syntax
open import Data.Bool renaming (Bool to 𝔹)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)

```

## Primitives

```
data Base : Set where
  B-Nat : Base
  B-Bool : Base

data Prim : Set where
  base : Base → Prim
  _⇒_ : Base → Prim → Prim

base-rep : Base → Set 
base-rep B-Nat = ℕ
base-rep B-Bool = 𝔹

rep : Prim → Set
rep (base b) = base-rep b
rep (b ⇒ p) = base-rep b → rep p
```

## Syntax

```
```


## Types

```
data Type : Set where
  Nat   : Type
  Bool   : Type
  _⇒_   : Type → Type → Type
  Array _  : Type → Type
```

### Contexts

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

## Terms

```
data Op : Set where
  op-lam : Op
  op-app : Op
  op-rec : Op
  op-const : (p : Prim) → rep p → Op
  op-let : Op
  op-insert : Op
  op-empty  : Op
  op-index : ℕ → Op
  op-error : Op

sig : Op → List ℕ
sig op-lam = 1 ∷ []
sig op-app = 0 ∷ 0 ∷ []
sig op-rec = 1 ∷ []
sig (op-const p k) = []
sig op-let = 0 ∷ 1 ∷ []
sig op-insert = 0 ∷ 0 ∷ []
sig op-empty = []
sig (op-index i) = 0 ∷ []
sig op-error = []

open Syntax Op sig
  using (`_; _⦅_⦆; cons; nil; bind; ast; _[_]; Subst; ⟪_⟫; exts; _•_; id)
  renaming (ABT to Term)

pattern $ p k = (op-const p k) ⦅ nil ⦆

pattern ƛ N  = op-lam ⦅ cons (bind (ast N)) nil ⦆

pattern μ N  = op-rec ⦅ cons (bind (ast N)) nil ⦆

infixl 7  _·_
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆

pattern `let L M = op-let ⦅ cons (ast L) (cons (bind (ast M)) nil) ⦆

pattern _⦂⦂_ L M = op-insert ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern 〈〉 = op-empty ⦅ nil ⦆
pattern _!_ M k = (op-index k) ⦅ cons (ast M) nil ⦆

pattern error = op-error ⦅ nil ⦆
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

  ⊢insert : ∀{Γ A M Ms}
    → Γ ⊢ M ⦂ A
    → Γ ⊢ Ms ⦂ Array A
      ----------------------
   → Γ ⊢ (M ⦂⦂ Ms) ⦂ Array A

  ⊢! : ∀{Γ A Ms k}
    → Γ ⊢ Ms ⦂ Array A
      ----------------
    → Γ ⊢ Ms ! k ⦂ A
```


## Values

```
data Value : Term → Set where

  -- functions

  V-ƛ : ∀ {N : Term}
      ---------------------------
    → Value (ƛ N)

  -- primitives

  V-const : ∀ {p k}
      -----------------
    → Value ($ p k)

  -- arrays

  V-〈〉 : Value 〈〉

  V-⦂⦂ : ∀ {V W : Term}
    → Value V
    → Value W
      -----------------
    → Value (V ⦂⦂ W)
```

## Frames and plug

```
data Frame : Set where
  □·_ : Term → Frame
  _·□ : (M : Term) → (v : Value M) → Frame
  □⦂⦂_ : Term → Frame
  _⦂⦂□ : (M : Term) → (v : Value M) → Frame
  □! : ℕ → Frame
  let□ : Term → Frame
```

```
plug : Term → Frame → Term
plug L (□· M)        = L · M
plug M ((L ·□) v)    = L · M
plug M (□⦂⦂ N)       = M ⦂⦂ N
plug N ((M ⦂⦂□) v)   = M ⦂⦂ N
plug M (□! k)        = M ! k
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
      -------------------
    → (V ⦂⦂ Vs) ! 0 —→  V

  β-index-suc : ∀ {V Vs i}
    → Value (V ⦂⦂ Vs)
      ----------------------------
    → (V ⦂⦂ Vs) ! (suc i) —→  Vs ! i

  β-index-error : ∀ {i}
      -----------------
    → 〈〉 ! i —→ error

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
progress (⊢$ _)                               = done V-const
progress (⊢ƛ ⊢N)                            =  done V-ƛ
progress (⊢· {L = L}{M}{A}{B} ⊢L ⊢M)
    with progress ⊢L
... | step L—→L′                            =  step (ξ (□· M) L—→L′)
... | trapped-error is-error                = step (lift-error (□· M))
... | done VL
        with progress ⊢M
...     | step M—→M′                        =  step (ξ ((L ·□) VL) M—→M′)
...     | trapped-error is-error            = step (lift-error ((L ·□) VL))
...     | done VM
            with canonical-fun ⊢L VL
...         | Fun-ƛ                         =  step (β-ƛ VM)
...         | Fun-prim {b}{p}{k}
                with ⊢L
...             | ⊢$ refl
                with canonical-base refl ⊢M VM
...             | base-const                = step δ
progress (⊢μ ⊢M)                            =  step β-μ
progress (⊢let {N = N} ⊢L ⊢N)
    with progress ⊢L
... | step L—→L′                            = step (ξ (let□ N) L—→L′)
... | trapped-error is-error                = step (lift-error (let□ N))
... | done VL                               = step (β-let VL)
progress (⊢insert {M = M}{Ms} ⊢M ⊢Ms)
    with progress ⊢M
... | step M—→M′                            = step (ξ (□⦂⦂ Ms) M—→M′)
... | trapped-error is-error                = step (lift-error (□⦂⦂ Ms))
... | done VM
        with progress ⊢Ms
...     | step Ms—→Ms′                      = step (ξ ((M ⦂⦂□) VM) Ms—→Ms′)
...     | trapped-error is-error            = step (lift-error ((M ⦂⦂□) VM))
...     | done VMs                          = done (V-⦂⦂ VM VMs)
progress (⊢! {k = k} ⊢M)
    with progress ⊢M
... | step M—→M′                            = step (ξ (□! k) M—→M′)
... | trapped-error is-error                = step (lift-error (□! k))
... | done VMs
        with canonical-array ⊢M VMs
...     | array-empty                       = step β-index-error
...     | array-insert aVs
        with k
...     | 0                                 = step (β-index-0 VMs)
...     | suc k'                            = step (β-index-suc VMs)
```
