```
module lecture-notes-Subtyping where
```

## Imports

```
open import Data.Unit using (⊤; tt)
{-
open import Data.List using (List; []; _∷_; map; length)
open import Data.Maybe using (Maybe; just; nothing)
-}
open import Data.Vec
  using (Vec; toList; []; _∷_; lookup)
open import Data.Fin using (Fin)
open import Data.Vec.Membership.Propositional using (_∈_)
open import Data.Vec.Any using (Any; here; there)
{-
open import Data.List.Membership.Propositional using (_∈_)
-}
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
distinct : ∀{A : Set}{n} → Vec A n → Set
distinct [] = ⊤
distinct (x ∷ xs) = ¬ (x ∈ xs) × distinct xs
```

```
data Type : Set where
  `𝔹    : Type
  `ℕ    : Type
  _⇒_   : Type → Type → Type
  Record : (n : ℕ) (fs : Vec Id n) (As : Vec Type n) → .{d : distinct fs} → Type 
```

```
data _⦂_∈_⦂_ : Id → Type → {n : ℕ} → Vec Id n → Vec Type n → Set where
  member : ∀{n}{i : Fin n}{j : Fin n}{fs : Vec Id n}{As : Vec Type n}{x : Id}{A : Type}
         → lookup fs i ≡ x
         → lookup As i ≡ A
         → x ⦂ A ∈ fs ⦂ As
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

  <:-rcd-width : ∀{n fs₁ As₁ d₁ fs₂ As₂ d₂}
    → (∀ {x}{A} → x ⦂ A ∈ fs₂ ⦂ As₂ → x ⦂ A ∈ fs₁ ⦂ As₁)
      --------------------------------------------------
    → Record n fs₁ As₁ {d₁} <: Record n fs₂ As₂ {d₂}

  <:-rcd-nil : ∀{d1 d2} → Record 0 [] [] {d1} <: Record 0 [] [] {d2}

  <:-rcd-depth : ∀{n}{fs : Vec Id n}{As₁ As₂ : Vec Type n}{d1 d2}
    → (∀ {i : Fin n} → lookup As₁ i <: lookup As₂ i)
      ----------------------------------------------
    → Record n fs As₁ {d1} <: Record n fs As₂ {d2}
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
