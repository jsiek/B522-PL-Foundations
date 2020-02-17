```
module lecture-notes-Subtyping where
```

## Imports

```
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (ℕ; zero; suc; _<_; _+_; _≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Bool using () renaming (Bool to 𝔹)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
   renaming (_,_ to ⟨_,_⟩)
open import Data.String using (String; _≟_)
open import Data.Empty using (⊥; ⊥-elim)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)
open import Relation.Nullary using (Dec; yes; no; ¬_)
import Syntax
```

### Syntax

```
infix  4 _⊢_⦂_
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
```

The field names in records must be distinct.

```
distinct : ∀{A : Set} → List A → Set
distinct [] = ⊤
distinct (x ∷ xs) = ¬ (x ∈ xs) × distinct xs

wf-rcd : ∀{A : Set} → List (Id × A) → Set
wf-rcd ρ = distinct (map proj₁ ρ)
```

```
data Type : Set where
  `𝔹    : Type
  `ℕ    : Type
  _⇒_   : Type → Type → Type
  Record : (ρ : List (Id × Type)) → .{ w : wf-rcd ρ } → Type 
```


### Subtyping

```
data _<:_ : Type → Type → Set where
  <:-refl : ∀{A} → A <: A

  <:-trans : ∀{A B C}
    → A <: B   →   B <: C
      -------------------
    → A <: C

  <:-fun : ∀{A B C D}
    → C <: A  → B <: D
      ----------------
    → A ⇒ B <: C ⇒ D

  <:-rcd-width : ∀{ρ₁ ρ₂ wf1 wf2}
    → (∀ {x A} → ⟨ x , A ⟩ ∈ ρ₂ → ⟨ x , A ⟩ ∈ ρ₁)
      -------------------------------------------
    → Record ρ₁ {wf1} <: Record ρ₂ {wf2}

  <:-rcd-nil : ∀{wf1 wf2} → Record [] {wf1} <: Record [] {wf2}

  <:-rcd-depth : ∀{ρ₁ ρ₂}{ x : Id}{A B : Type}{wf1 wf2 wf1' wf2'}
    → A <: B    →   Record ρ₁ {wf1} <: Record ρ₂ {wf2}
      ----------------------------------------------------------------
    → Record (⟨ x , A ⟩ ∷ ρ₁) {wf1'} <: Record (⟨ x , B ⟩ ∷ ρ₂) {wf2'}
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

## Inversion of Subtyping

```
inversion-<:-fun : ∀{A B C : Type}
  → A <: B ⇒ C
  → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] A ≡ A₁ ⇒ A₂
inversion-<:-fun {.(B ⇒ C)}{B}{C} <:-refl = ⟨ B , ⟨ C , refl ⟩ ⟩
inversion-<:-fun (<:-trans AB BB₁C)
    with inversion-<:-fun BB₁C
... | ⟨ D , ⟨ E , refl ⟩ ⟩ = inversion-<:-fun AB
inversion-<:-fun (<:-fun {A}{B} ABC ABC₁) = ⟨ A , ⟨ B , refl ⟩ ⟩
```

```
inversion-<:-fun2 : ∀{A B C : Type}
  → A <: B ⇒ C
  → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] (A ≡ A₁ ⇒ A₂ × B <: A₁ × A₂ <: C)
inversion-<:-fun2 {A}{B}{C} <:-refl =
    ⟨ B , ⟨ C , ⟨ refl , ⟨ <:-refl , <:-refl ⟩ ⟩ ⟩ ⟩
inversion-<:-fun2 (<:-trans a<:bc a<:bc₁)
    with inversion-<:-fun2 a<:bc₁
... | ⟨ D , ⟨ E , ⟨ refl , ⟨ s1 , s2 ⟩ ⟩ ⟩ ⟩ 
    with inversion-<:-fun2 a<:bc
... | ⟨ D' , ⟨ E' , ⟨ refl , ⟨ s3 , s4 ⟩ ⟩ ⟩ ⟩ =
    ⟨ D' , ⟨ E' , ⟨ refl , ⟨ (<:-trans s1 s3) , (<:-trans s4 s2) ⟩ ⟩ ⟩ ⟩
inversion-<:-fun2 (<:-fun {A}{B} a<:bc a<:bc₁) =
    ⟨ A , ⟨ B , ⟨ refl , ⟨ a<:bc , a<:bc₁ ⟩ ⟩ ⟩ ⟩
```


```
inversion-<:-base : ∀ {b A}
  → A <: typeof-base b
  → A ≡ typeof-base b
inversion-<:-base {B-Nat} <:-refl = refl
inversion-<:-base {B-Nat} (<:-trans A<: A<:₁) 
    rewrite inversion-<:-base A<:₁
    | inversion-<:-base A<: = refl
inversion-<:-base {B-Bool} <:-refl = refl
inversion-<:-base {B-Bool} (<:-trans A<: A<:₁)
    rewrite inversion-<:-base A<:₁
    | inversion-<:-base A<: = refl
```

```
inversion-<:-rcd : ∀{A ρ₂ wf}
  → A <: Record ρ₂ {wf}
  → Σ[ ρ₁ ∈ List (Id × Type) ] Σ[ wf1 ∈ wf-rcd ρ₁ ]
       A ≡ Record ρ₁ {wf1}
inversion-<:-rcd {A}{ρ₂}{wf} <:-refl = ⟨ ρ₂ , ⟨ wf , refl ⟩ ⟩
inversion-<:-rcd {wf = wf} (<:-trans A<: A<:₁)
    with inversion-<:-rcd {wf = wf} A<:₁
... | ⟨ ρ₁ , ⟨ wf1 , refl ⟩ ⟩ =
    inversion-<:-rcd {wf = wf1} A<:
inversion-<:-rcd (<:-rcd-width {ρ₁ = ρ₁}{wf1 = wf1} ρ₁⊆ρ₂) =
    ⟨ ρ₁ , ⟨ wf1 , refl ⟩ ⟩
inversion-<:-rcd <:-rcd-nil = ⟨ [] , ⟨ tt , refl ⟩ ⟩
inversion-<:-rcd (<:-rcd-depth {ρ₁}{x = x}{A = A}{wf1' = wf1'} A<: A<:₁) = ⟨ ⟨ x , A ⟩ ∷ ρ₁ , ⟨ wf1' , refl ⟩ ⟩
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
subst-lam : ∀{A} (N : Term) (σ : Subst) → ⟪ σ ⟫ (λ: A ⇒ N) ≡ λ: A ⇒ (⟪ exts σ ⟫ N)
subst-lam N σ = refl 

subst-app : ∀ (L M : Term) (σ : Subst) → ⟪ σ ⟫ (L · M) ≡ (⟪ σ ⟫ L) · (⟪ σ ⟫ M)
subst-app L M σ = refl
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

  ⊢insert : ∀{Γ A M R ρ f w}
    → Γ ⊢ M ⦂ A
    → Γ ⊢ R ⦂ Record ρ {w}
    → (d : ¬ f ∈ (map proj₁ ρ))
      ----------------------------------------------------
    → Γ ⊢ (f := M , R) ⦂ Record (⟨ f , A ⟩ ∷ ρ) {⟨ d , w ⟩}

  ⊢# : ∀{Γ A R f ρ w}
    → Γ ⊢ R ⦂ Record ρ {w}
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

## Reduction

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
data Function : Term → Type → Set where
  Fun-λ : ∀ {A B}{N} → Function (λ: A ⇒ N) B
  Fun-prim : ∀{b p k A}
    → typeof (b ⇒ p) <: A
    → Function ($ (b ⇒ p) k) A

Function-<: : ∀{V A B}
   → Function V A
   → A <: B
   → Function V B
Function-<: Fun-λ a<:b = Fun-λ
Function-<: (Fun-prim x) a<:b = Fun-prim (<:-trans x a<:b)

canonical-fun : ∀{V A B C}
  → ∅ ⊢ V ⦂ A
  → Value V
  → A <: (B ⇒ C)
    ------------
  → Function V A
canonical-fun (⊢λ ⊢V) V-λ A<:⇒ = Fun-λ
canonical-fun (⊢$ {p = base B-Nat} refl) (V-const {_} {k}) A<:⇒
    with inversion-<:-fun A<:⇒
... | ⟨ A₁ , ⟨ A₂ , () ⟩ ⟩
canonical-fun (⊢$ {p = base B-Bool} refl) (V-const {_} {k}) A<:⇒
    with inversion-<:-fun A<:⇒
... | ⟨ A₁ , ⟨ A₂ , () ⟩ ⟩
canonical-fun (⊢$ {p = b ⇒ p} refl) (V-const {_} {k}) A<:⇒ =
    Fun-prim <:-refl
canonical-fun {V}{A}{B}{C}(⊢<: {A = A'} ⊢M A<:) vV A<:⇒
    with inversion-<:-fun A<:⇒
... | ⟨ A₁ , ⟨ A₂ , refl ⟩ ⟩ =
    let IH = canonical-fun ⊢M vV A<: in
    Function-<: IH A<:
canonical-fun ⊢empty V-〈〉 <:⇒
    with inversion-<:-fun <:⇒
... | ⟨ A₁ , ⟨ A₂ , () ⟩ ⟩
canonical-fun (⊢insert x₁ x₂ d) (V-:= x₃ x₄) <:⇒
    with inversion-<:-fun <:⇒
... | ⟨ A₁ , ⟨ A₂ , () ⟩ ⟩
```

```
data Constant : Base → Term → Set where
  base-const : ∀{b k} → Constant b ($ (base b) k)

canonical-base : ∀{b V A}
  → ∅ ⊢ V ⦂ A
  → Value V
  → A <: typeof-base b
    ------------
  → Constant b V
canonical-base {B-Nat} (⊢λ ⊢V) vV A<:
    with inversion-<:-base A<:
... | ()
canonical-base {B-Bool} (⊢λ ⊢V) vV A<:
    with inversion-<:-base A<:
... | ()
canonical-base {B-Nat} (⊢$ {p = base B-Nat} refl) vV A<: =
    base-const
canonical-base {B-Nat} (⊢$ {p = base B-Bool} refl) vV A<:
    with inversion-<:-base A<:
... | ()
canonical-base {B-Nat} (⊢$ {p = x ⇒ p} refl) vV A<:
    with inversion-<:-base A<:
... | ()
canonical-base {B-Bool} (⊢$ {p = base B-Nat} refl) vV A<:
    with inversion-<:-base A<:
... | ()
canonical-base {B-Bool} (⊢$ {p = base B-Bool} refl) vV A<: =
    base-const
canonical-base {B-Bool} (⊢$ {p = x ⇒ p} refl) vV A<:
    with inversion-<:-base A<:
... | ()
canonical-base {B-Nat} ⊢empty vV A<:
    with inversion-<:-base A<:
... | ()
canonical-base {B-Bool} ⊢empty vV A<:
    with inversion-<:-base A<:
... | ()
canonical-base {B-Nat} (⊢insert ⊢V ⊢V₁ d) vV A<:
    with inversion-<:-base A<:
... | ()
canonical-base {B-Bool} (⊢insert ⊢V ⊢V₁ d) vV A<:
    with inversion-<:-base A<:
... | ()
canonical-base {b} (⊢<: ⊢V x) vV A<: =
  canonical-base ⊢V vV (<:-trans x A<:)
```

```
data Rcd : Term → Type → Set where
  Rcd-⟨⟩ : ∀{B} → Record [] <: B → Rcd 〈〉 B
  Rcd-:= : ∀ {f A B M R ρ w}
         → Rcd R (Record ρ {w})
         → (d : ¬ f ∈ map proj₁ ρ)
         → Record (⟨ f , A ⟩ ∷ ρ) {⟨ d , w ⟩} <: B
         → Rcd (f := M , R) B

Rcd-<: : ∀{R A B}
  → Rcd R A
  → A <: B
  → Rcd R B
Rcd-<: (Rcd-⟨⟩ s) A<:B = Rcd-⟨⟩ (<:-trans s A<:B)
Rcd-<: (Rcd-:= {w = w} RA d x) A<:B =
    Rcd-:= {w = w} RA d (<:-trans x A<:B)


rem : Id → List (Id × Type) → List (Id × Type)
rem f [] = []
rem f (⟨ x , A ⟩ ∷ ρ)
    with f ≟ x
... | yes refl = ρ
... | no f≢x = rem f ρ

distinct-rem : ∀{ρ f}
  → distinct (map proj₁ ρ)
  → distinct (map proj₁ (rem f ρ))
distinct-rem {[]} d = tt
distinct-rem {⟨ x , A ⟩ ∷ ρ}{f} ⟨ fst , snd ⟩ 
    with f ≟ x
... | yes refl = snd
... | no f≢x = distinct-rem snd

wf-rem : ∀{ρ f} → wf-rcd ρ
   → wf-rcd (rem f ρ)
wf-rem {[]} wf = tt
wf-rem {⟨ g , A ⟩ ∷ ρ} {f} ⟨ d , w ⟩
    with f ≟ g
... | yes refl = w
... | no f≢g = distinct-rem w

rem-mem : ∀{ρ ρ' f}
   → (∀ {x A} → ⟨ x , A ⟩ ∈ ρ' → ⟨ x , A ⟩ ∈ ρ)
   → ∀ {x A} → ⟨ x , A ⟩ ∈ rem f ρ' → ⟨ x , A ⟩ ∈ rem f ρ
rem-mem {ρ} {⟨ y , B ⟩ ∷ ρ'}{f} mem x∈rem
    with f ≟ y
... | yes refl
    with x∈rem
... | here refl = {!!}
... | there z = {!!}
rem-mem {ρ} {⟨ y , B ⟩ ∷ ρ'}{f} mem x∈rem | no f≢y = {!!}

rem-<: : ∀{f ρ w ρ' w'}
   → Record ρ {w} <: Record ρ' {w'}
   → Record (rem f ρ) {wf-rem w} <: Record (rem f ρ') {wf-rem w'}
rem-<: {f} {ρ} {w} {.ρ} {w'} <:-refl = <:-refl
rem-<: {f} {ρ} {w} {ρ'} {w'} (<:-trans ρ<:B B<:ρ')
    with inversion-<:-rcd {wf = w'} B<:ρ' 
... | ⟨ ρ₂ , ⟨ w₂ , refl ⟩ ⟩ =
  let IH1 = rem-<: {w = w} {w' = w₂} ρ<:B in
  let IH2 = rem-<: {w = w₂} {w' = w'} B<:ρ' in
  <:-trans IH1 IH2
rem-<: {f} {ρ} {w} {ρ'} {w'} (<:-rcd-width x) = <:-rcd-width {wf1 = {!!}}{wf2 = {!!}} (rem-mem x)
rem-<: {f} {.[]} {w} {.[]} {w'} <:-rcd-nil = <:-refl
rem-<: {f} {.(⟨ _ , _ ⟩ ∷ _)} {w} {.(⟨ _ , _ ⟩ ∷ _)} {w'} (<:-rcd-depth R<: R<:₁) = {!!}

rcd-insert<: : ∀{f A ρ ρ' w d' w'}
   → Record (⟨ f , A ⟩ ∷ ρ') {⟨ d' , w' ⟩} <: Record ρ {w}
   → Record ρ' {w'} <: Record (rem f ρ) {wf-rem w}
rcd-insert<: {f} <:-refl
    with f ≟ f
... | yes refl = <:-refl
... | no x = ⊥-elim (x refl)
rcd-insert<: {w = w}{d'}{w'} (<:-trans ρ'<:B B<:ρ)
    with inversion-<:-rcd {wf = w} B<:ρ
... | ⟨ ρ₂ , ⟨ w'' , refl ⟩ ⟩ =
    let IH = rcd-insert<: {w = w''}{d'}{w'} ρ'<:B in
    <:-trans IH {!!}
rcd-insert<: (<:-rcd-width x) = {!!}
rcd-insert<: (<:-rcd-depth R<: R<:₁) = {!!}


canonical-rcd : ∀{R A ρ w}
  → ∅ ⊢ R ⦂ A
  → Value R
  → A <: Record ρ {w}
  → Rcd R A
canonical-rcd {w = w} (⊢λ ⊢R) vR A<:
    with inversion-<:-rcd {wf = w} A<:
... | ⟨ ρ , ⟨ wf , () ⟩ ⟩
canonical-rcd {w = w} (⊢$ {p = base B-Nat} refl) vR A<:
    with inversion-<:-rcd {wf = w} A<:
... | ⟨ ρ , ⟨ wf , () ⟩ ⟩
canonical-rcd {w = w} (⊢$ {p = base B-Bool} refl) vR A<:
    with inversion-<:-rcd {wf = w} A<:
... | ⟨ ρ , ⟨ wf , () ⟩ ⟩
canonical-rcd {w = w} (⊢$ {p = b ⇒ p} refl) vR A<:
    with inversion-<:-rcd {wf = w} A<:
... | ⟨ ρ , ⟨ wf , () ⟩ ⟩
canonical-rcd ⊢empty vR A<: = Rcd-⟨⟩ <:-refl
canonical-rcd {A = A}{ρ}{w}(⊢insert {A = A'} {ρ = ρ'} {f} {w'} ⊢M ⊢R d) (V-:= vM vR) A<: =
    let IH = canonical-rcd {ρ = ρ}{w} ⊢R vR {!!} in
    Rcd-:= {w = w'} IH d <:-refl
canonical-rcd {ρ = ρ}{w} (⊢<: {A = B} ⊢R B<:A) vR A<: = {!!}
{-
    with inversion-<:-rcd {wf = w} A<:
... | ⟨ ρ' , ⟨ wf , refl ⟩ ⟩
    with canonical-rcd {ρ = ρ}{w} ⊢R vR (<:-trans B<:A A<:)
... | ⟨ ρ'' , ⟨ wf' , refl ⟩ ⟩ = ⟨ ρ' , ⟨ wf , refl ⟩ ⟩
-}
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
progress (⊢$ _)                           = done V-const
progress (⊢λ ⊢N)                          = done V-λ
progress (⊢· {L = L}{M}{A}{B} ⊢L ⊢M)
    with progress ⊢L
... | step L—→L′                          = step (ξ (□· M) L—→L′)
... | done VL
        with progress ⊢M
...     | step M—→M′                      = step (ξ ((L ·□) VL) M—→M′)
...     | done VM 
        with canonical-fun ⊢L VL <:-refl
...     | Fun-λ                           = step (β-λ VM)
...     | Fun-prim {b}{p}{k} p⇒b<:A⇒B
        with inversion-<:-fun2 p⇒b<:A⇒B
...     | ⟨ A₁ , ⟨ A₂ , ⟨ refl , ⟨ A<:p , b<:B ⟩ ⟩ ⟩ ⟩
        with inversion-<:-base A<:p
...     | refl
        with canonical-base ⊢M VM A<:p
...     | base-const                      = step δ
progress (⊢μ ⊢M)                          = step β-μ
progress (⊢let {N = N} ⊢L ⊢N)
    with progress ⊢L
... | step L—→L′                          = step (ξ (let□ N) L—→L′)
... | done VL                             = step (β-let VL)
progress ⊢empty                           = done V-〈〉
progress (⊢insert {M = M}{R}{f = f} ⊢M ⊢R ¬∈)
    with progress ⊢M
... | step M—→M′                          = step (ξ (f :=□, R) M—→M′)
... | done VM
        with progress ⊢R
...     | step R—→R′                      = step (ξ ((f := M ,□) VM) R—→R′)
...     | done VR                         = done (V-:= VM VR)
progress (⊢# {R = R} {f} ⊢R f∈ρ)
    with progress ⊢R
... | step R—→R′                          = step (ξ (□# f) R—→R′)
... | done VR
    with f∈ρ
... | here refl = {!!}
... | there x = {!!}
{-
    with f∈ρ
... | ∈-eq {A = A}{B} A<:B = {!!}
... | ∈-neq f∈ρ' x = {!!}
-}
progress (⊢<: {A = A}{B} ⊢M A<:B) = progress ⊢M
```
