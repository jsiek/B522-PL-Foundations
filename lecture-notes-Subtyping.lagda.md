```
module lecture-notes-Subtyping where
```

## Imports

```
open import Data.List using (List; []; _∷_)
open import Data.List.Any using (Any; here; there)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Bool using () renaming (Bool to 𝔹)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
   renaming (_,_ to ⟨_,_⟩)
open import Data.String using (String; _≟_)
open import Data.Empty using (⊥; ⊥-elim)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)
open import Relation.Nullary using (Dec; yes; no)
import Syntax
```

### Syntax

```
infix  4 _⊢_⦂_
infix  4 _∈_
infixl 5 _,_

infixr 7 _⇒_
infix 6 _<:_

infix  5 λ:_⇒_
infixl 7 _·_
infix  9 _:=_,_
infixr 9 _#_

infix 4 _—→_
```

### Types

```
Id : Set
Id = String

data Type : Set where
  `𝔹    : Type
  `ℕ    : Type
  _⇒_   : Type → Type → Type
  Record : List (Id × Type) → Type 
```

```
data WFRow : List (Id × Type) → Set

data WF : Type → Set where
   WF-Bool : WF (`𝔹)
   WF-Nat : WF (`ℕ)
   WF-Fun : ∀{A B} → WF A → WF B → WF (A ⇒ B)
   WF-Record : ∀{ρ} → WFRow ρ → WF (Record ρ)

data WFRow where
  WFR-nil : WFRow []
  WFR-cons : → WFRow (⟨ x , A ⟩ ∷ ρ)
  
```

### Subtyping

```
data _<:_ : Type → Type → Set
data _∈_ : (Id × Type) → List (Id × Type) → Set
data _<::_ : List (Id × Type) → List (Id × Type) → Set

data _<:_ where
  <:bool : `𝔹 <: `𝔹
  
  <:nat : `ℕ <: `ℕ
  
  <:fun : ∀ {A B C D}
        → C <: A  →  B <: D
          ------------------
        → (A ⇒ B) <: (C ⇒ D)
        
  <:rec : ∀{ρ₁ ρ₂}
        → ρ₁ <:: ρ₂
          ----------------------
        → Record ρ₁ <: Record ρ₂ 

data _<::_ where
  <::nil : ∀{ρ} → ρ <:: []
  
  <::cons-R : ∀{ρ₁ ρ₂ y B}
          → ⟨ y , B ⟩ ∈ ρ₁
          → ρ₁ <:: ρ₂
            -----------------------
          → ρ₁ <:: (⟨ y , B ⟩ ∷ ρ₂)

data _∈_ where
  ∈-eq : ∀ {ρ x A B}
       → A <: B
         ---------------------------
       → ⟨ x , B ⟩ ∈ (⟨ x , A ⟩ ∷ ρ)

  ∈-neq : ∀ {ρ x y A B}
       → ⟨ x , B ⟩ ∈ ρ   → x ≢ y
         ---------------------------
       → ⟨ x , B ⟩ ∈ (⟨ y , A ⟩ ∷ ρ)
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

## Type of a primitive

```
typeof-base : Base → Type
typeof-base B-Nat = `ℕ
typeof-base B-Bool = `𝔹

typeof : Prim → Type
typeof (base b) = typeof-base b 
typeof (b ⇒ p) = typeof-base b ⇒ typeof p
```

## Properties of Subtyping


```
sub-inv-fun : ∀{A B C : Type}
  → A <: B ⇒ C
  → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ ⇒ A₂
sub-inv-fun (<:fun {A = A}{B = B} A<:BC A<:BC₁) = ⟨ A , ⟨ B , refl ⟩ ⟩
```

```
sub-inv-base : ∀ {b A}
  → A <: typeof-base b
  → A ≡ typeof-base b
sub-inv-base {B-Nat} <:nat = refl
sub-inv-base {B-Bool} <:bool = refl
```


```
{-
<:-∈ : ∀{A B y ρ}
     → A <: B
     → ⟨ y , A ⟩ ∈ ρ
     → ⟨ y , B ⟩ ∈ ρ
<:-∈ A<:B (∈-eq x) = {!!}
<:-∈ A<:B (∈-neq y∈ρ x) = {!!}


∈-<:: : ∀{y B ρ₁ ρ₂}
      → ⟨ y , B ⟩ ∈ ρ₁
      → ρ₂ <:: ρ₁
      → ⟨ y , B ⟩ ∈ ρ₂
∈-<:: (∈-eq A<:B) (<::cons-R x ρ₂<:ρ₁) =
  {!!}
∈-<:: (∈-neq y∈ρ₁ x) ρ₂<:ρ₁ = {!!}
-}

<::cons-L : ∀{ρ₁ ρ₂ x A}
          → ρ₁ <:: ρ₂
            -----------------------
          → (⟨ x , A ⟩ ∷ ρ₁) <:: ρ₂
<::cons-L {ρ₁} {[]} ρ₁<:ρ₂ = <::nil
<::cons-L {ρ₁} {(⟨ y , B ⟩) ∷ ρ₂} {x}{A} (<::cons-R y∈ρ₁ ρ₁<:ρ₂)
    with x ≟ y
... | yes refl = {!!}
... | no x≢y = {!!}

{-
    with x ≟ y
... | yes xy = ?
... | no x≢y = 
   let IH = <::cons-L {x = x}{A} ρ₁<:ρ₂ in
   {!!}
-}

```

```
<::-refl : ∀ ρ → ρ <:: ρ

<:-refl : ∀ A → A <: A
<:-refl `𝔹 = <:bool
<:-refl `ℕ = <:nat
<:-refl (A ⇒ B) = <:fun (<:-refl A) (<:-refl B)
<:-refl (Record ρ) = <:rec (<::-refl ρ)

<::-refl [] = <::nil
<::-refl (⟨ f , A ⟩ ∷ ρ) = <::cons-R (∈-eq (<:-refl A)) (<::cons-L (<::-refl ρ))
```

```
<::-trans : ∀{A B C} → A <:: B → B <:: C → A <:: C

<:-trans : ∀{A B C} → A <: B → B <: C → A <: C
<:-trans <:bool <:bool = <:bool
<:-trans <:nat <:nat = <:nat
<:-trans (<:fun C1A BD1) (<:fun CC1 D1D) =
    <:fun (<:-trans CC1 C1A) (<:-trans BD1 D1D)
<:-trans (<:rec R1R2) (<:rec R2R3) = <:rec (<::-trans R1R2 R2R3)

<::-trans AB <::nil = <::nil
<::-trans A<:B₁ (<::cons-R y∈B₁ B₁ρ₂) =
  let IH = <::-trans A<:B₁ B₁ρ₂ in
  <::cons-R {!!} IH
{-
<::-trans AB (<::cons-L BC) = {!!}
-}
```


## Terms

We use the
[abstract-binding-trees](https://github.com/jsiek/abstract-binding-trees)
library to represent terms.

```
data Op : Set where
  op-lam : Type → Op
  op-app : Op
  op-rec : Op
  op-const : (p : Prim) → rep p → Op
  op-let : Op
  op-insert : Id → Op
  op-empty  : Op
  op-member : Id → Op

sig : Op → List ℕ
sig (op-lam A) = 1 ∷ []
sig op-app = 0 ∷ 0 ∷ []
sig op-rec = 1 ∷ []
sig (op-const p k) = []
sig op-let = 0 ∷ 1 ∷ []
sig (op-insert f) = 0 ∷ 0 ∷ []
sig op-empty = []
sig (op-member f) = 0 ∷ []

open Syntax Op sig
  using (`_; _⦅_⦆; cons; nil; bind; ast; _[_];
         Rename; Subst; ⟪_⟫; ⟦_⟧; exts; _•_; 
         ↑; _⨟_; exts-0; exts-suc-rename; rename; ext; ⦉_⦊;
         ext-0; ext-suc)
  renaming (ABT to Term)

pattern $ p k = (op-const p k) ⦅ nil ⦆

pattern λ:_⇒_ A N  = (op-lam A) ⦅ cons (bind (ast N)) nil ⦆

pattern μ N  = op-rec ⦅ cons (bind (ast N)) nil ⦆

pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆

pattern `let L M = op-let ⦅ cons (ast L) (cons (bind (ast M)) nil) ⦆

pattern _:=_,_ f L M = (op-insert f) ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern 〈〉 = op-empty ⦅ nil ⦆
pattern _#_ M f = (op-member f) ⦅ cons (ast M) nil ⦆
```

```
sub-lam : ∀{A} (N : Term) (σ : Subst) → ⟪ σ ⟫ (λ: A ⇒ N) ≡ λ: A ⇒ (⟪ exts σ ⟫ N)
sub-lam N σ = refl 

sub-app : ∀ (L M : Term) (σ : Subst) → ⟪ σ ⟫ (L · M) ≡ (⟪ σ ⟫ L) · (⟪ σ ⟫ M)
sub-app L M σ = refl
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
data _⊢_⦂_ : Context → Term → Type → Set where

  -- Axiom 
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ⦂ A

  -- ⇒-I 
  ⊢λ : ∀ {Γ N A B}
    → Γ , A ⊢ N ⦂ B
      -------------------
    → Γ ⊢ λ: A ⇒ N ⦂ A ⇒ B

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

  ⊢empty : ∀{Γ}
      -------------------
    → Γ ⊢ 〈〉 ⦂ Record []

  ⊢insert : ∀{Γ A M R ρ f}
    → Γ ⊢ M ⦂ A
    → Γ ⊢ R ⦂ Record ρ
      -----------------------------------------
    → Γ ⊢ (f := M , R) ⦂ Record (⟨ f , A ⟩ ∷ ρ)

  ⊢# : ∀{Γ A R f ρ}
    → Γ ⊢ R ⦂ Record ρ
    → ⟨ f , A ⟩ ∈ ρ
      ----------------
    → Γ ⊢ R # f ⦂ A

  ⊢<: : ∀{Γ M A B}
    → Γ ⊢ M ⦂ A   → A <: B
      --------------------
    → Γ ⊢ M ⦂ B
```

## Values

```
data Value : Term → Set where

  V-λ : ∀ {A} {N : Term}
      ---------------------------
    → Value (λ: A ⇒ N)

  V-const : ∀ {p k}
      -----------------
    → Value ($ p k)

  V-〈〉 : Value 〈〉

  V-:= : ∀ {V RV : Term}{f}
    → Value V
    → Value RV
      -------------------
    → Value (f := V , RV)
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
  _:=□,_ : Id → Term → Frame
  _:=_,□ : Id → (M : Term) → (v : Value M) → Frame
  □#_ : Id → Frame
  let□ : Term → Frame
```

The `plug` function fills a frame's hole with a term.

```
plug : Term → Frame → Term
plug L (□· M)          = L · M
plug M ((L ·□) v)      = L · M
plug M (f :=□, R)      = f := M , R
plug R ((f := M ,□) v) = f := M , R
plug M (□# f)          = M # f
plug M (let□ N)        = `let M N
```

```
data _—→_ : Term → Term → Set where

  ξ : ∀ {M M′}
    → (F : Frame)
    → M —→ M′
      ---------------------
    → plug M F —→ plug M′ F

  β-λ : ∀ {A N V}
    → Value V
      -------------------------
    → (λ: A ⇒ N) · V —→ N [ V ]

  β-μ : ∀ {M}
      ----------------
    → μ M —→ M [ μ M ]

  δ : ∀ {b p f k}
      ---------------------------------------------
    → ($ (b ⇒ p) f) · ($ (base b) k) —→ ($ p (f k))

  β-let : ∀{V N}
    → Value V
      -------------------
    → `let V N —→ N [ V ]

  β-member-eq : ∀ {V RV f}
    → Value (f := V , RV)
      -----------------------
    → (f := V , RV) # f —→  V

  β-member-neq : ∀ {V RV f f'}
    → Value (f := V , RV)   → f ≢ f'
      ------------------------------
    → (f := V , RV) # f' —→  RV # f'
```



## Canonical Forms

```
data Function : Term → Set where
  Fun-λ : ∀ {A}{N} → Function (λ: A ⇒ N)
  Fun-prim : ∀{b p k} → Function ($ (b ⇒ p) k)

canonical-fun : ∀{V A B C}
  → ∅ ⊢ V ⦂ A
  → Value V
  → A <: (B ⇒ C)
    ----------
  → Function V
canonical-fun (⊢λ ⊢V) V-λ A<:⇒ = Fun-λ
canonical-fun (⊢$ {p = base B-Nat} refl) (V-const {_} {k}) A<:⇒
    with sub-inv-fun A<:⇒
... | ⟨ A₁ , ⟨ A₂ , () ⟩ ⟩
canonical-fun (⊢$ {p = base B-Bool} refl) (V-const {_} {k}) A<:⇒
    with sub-inv-fun A<:⇒
... | ⟨ A₁ , ⟨ A₂ , () ⟩ ⟩
canonical-fun (⊢$ {p = b ⇒ p} eq) (V-const {_} {k}) A<:⇒ = Fun-prim
canonical-fun (⊢<: ⊢M A<:) V A<:⇒
    with sub-inv-fun A<:⇒
... | ⟨ A₁ , ⟨ A₂ , refl ⟩ ⟩ =
    canonical-fun ⊢M V A<: 

data Constant : Base → Term → Set where
  base-const : ∀{b k} → Constant b ($ (base b) k)

canonical-base : ∀{b V A}
  → ∅ ⊢ V ⦂ A
  → Value V
  → A <: typeof-base b
    ------------
  → Constant b V
canonical-base {B-Nat} (⊢λ ⊢V) vV ()
canonical-base {B-Bool} (⊢λ ⊢V) vV ()
canonical-base {B-Nat} (⊢$ {p = base B-Nat} refl) V-const <:nat = base-const
canonical-base {B-Bool} (⊢$ {p = base B-Bool} refl) V-const <:bool = base-const
canonical-base {B-Nat} ⊢empty V-〈〉 ()
canonical-base {B-Bool} ⊢empty V-〈〉 ()
canonical-base {B-Nat} (⊢insert ⊢V ⊢V₁) (V-:= vV vV₁) ()
canonical-base {B-Bool} (⊢insert ⊢V ⊢V₁) (V-:= vV vV₁) ()
canonical-base {b} (⊢<: ⊢V x) vV A<: = canonical-base ⊢V vV {!!}
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
progress (⊢λ ⊢N)                            = done V-λ
progress (⊢· {L = L}{M}{A}{B} ⊢L ⊢M)
    with progress ⊢L
... | step L—→L′                            = step (ξ (□· M) L—→L′)
... | done VL
        with progress ⊢M
...     | step M—→M′                        = step (ξ ((L ·□) VL) M—→M′)
...     | done VM = {!!}

{-
            with canonical-fun ⊢L VL {!!}
...         | Fun-λ                         = step (β-λ VM)
...         | Fun-prim {b}{p}{k}
                with ⊢L
...             | ⊢$ refl
                with canonical-base refl ⊢M VM
...             | base-const                = step δ
-}
progress (⊢μ ⊢M)                            = step β-μ
progress (⊢let {N = N} ⊢L ⊢N)
    with progress ⊢L
... | step L—→L′                            = step (ξ (let□ N) L—→L′)
... | done VL                               = step (β-let VL)
progress ⊢empty                             = done V-〈〉
progress (⊢insert {M = M}{R}{f = f} ⊢M ⊢R)
    with progress ⊢M
... | step M—→M′                            = step (ξ (f :=□, R) M—→M′)
... | done VM
        with progress ⊢R
...     | step R—→R′                        = step (ξ ((f := M ,□) VM) R—→R′)
...     | done VR                           = done (V-:= VM VR)
progress (⊢# {R = R} {f} ⊢R f∈ρ)
    with progress ⊢R
... | step R—→R′                            = step (ξ (□# f) R—→R′)
... | done VR
    with f∈ρ
... | ∈-eq {A = A}{B} A<:B = {!!}
... | ∈-neq f∈ρ' x = {!!}
progress (⊢<: {A = A}{B} ⊢M A<:B) = progress ⊢M
```
