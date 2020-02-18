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
open import Data.Fin using (Fin; reduce≥)
open import Data.Vec.Membership.Propositional using (_∈_)
open import Data.Vec.Any using (Any; here; there)
{-
open import Data.List.Membership.Propositional using (_∈_)
-}
open import Data.Nat using (ℕ; zero; suc; _<_; _+_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-pred; m+n≤o⇒m≤o; m+n≤o⇒n≤o; n≤0⇒n≡0; ≤-step)
open import Data.Bool using () renaming (Bool to 𝔹)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
   renaming (_,_ to ⟨_,_⟩)
open import Data.String using (String; _≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
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

_∈?_ : ∀{n} (x : Id) → (xs : Vec Id n) → Dec (x ∈ xs)
x ∈? [] = no λ ()
x ∈? (y ∷ xs)
    with x ≟ y
... | yes xy = yes (here xy)
... | no xy
    with x ∈? xs
... | yes x∈xs = yes (there x∈xs)
... | no x∉xs = no λ { (here a) → xy a ; (there a) → x∉xs a } 

distinct? : ∀{n} → (xs : Vec Id n) → Dec (distinct xs)
distinct? [] = yes tt
distinct? (x ∷ xs)
    with x ∈? xs
... | yes x∈xs = no λ z → proj₁ z x∈xs
... | no x∉xs
    with distinct? xs
... | yes dxs = yes ⟨ x∉xs , dxs ⟩
... | no ¬dxs = no λ x₁ → ¬dxs (proj₂ x₁)

distinct-rel : ∀ {n}{fs : Vec Id n} .(d : distinct fs) → distinct fs
distinct-rel {n}{fs} d
    with distinct? fs
... | yes dfs = dfs
... | no ¬dfs = ⊥-elimi (¬dfs d)
```

```
lookup-mem : ∀{n}{fs : Vec Id n}{j : Fin n} 
           → lookup fs j ∈ fs
lookup-mem {.(suc _)} {x ∷ fs} {Data.Fin.0F} = here refl
lookup-mem {.(suc _)} {x ∷ fs} {Fin.suc j} = there lookup-mem
```

```
distinct-lookup-eq : ∀ {n}{fs : Vec Id n}{i j : Fin n}
   → distinct fs
   → lookup fs j ≡ lookup fs i
   → i ≡ j
distinct-lookup-eq {.(suc _)} {x ∷ fs} {Data.Fin.0F} {Data.Fin.0F} ⟨ x∉fs , dfs ⟩ lij = refl
distinct-lookup-eq {suc n} {x ∷ fs} {Data.Fin.0F} {Fin.suc j} ⟨ x∉fs , dfs ⟩ refl =
    ⊥-elim (x∉fs lookup-mem)
distinct-lookup-eq {.(suc _)} {x ∷ fs} {Fin.suc i} {Data.Fin.0F} ⟨ x∉fs , dfs ⟩ refl =
    ⊥-elim (x∉fs lookup-mem)
distinct-lookup-eq {suc n} {x ∷ fs} {Fin.suc i} {Fin.suc j} ⟨ x∉fs , dfs ⟩ lij =
  let IH = distinct-lookup-eq {n} {fs}{i}{j} dfs lij in
  cong Fin.suc IH
```


```
data Type : Set where
  `𝔹    : Type
  `ℕ    : Type
  _⇒_   : Type → Type → Type
  Record : (n : ℕ) (fs : Vec Id n) (As : Vec Type n) → .{d : distinct fs} → Type 
```

### Subtyping

```
data _⦂_∈_⦂_ : Id → Type → {n : ℕ} → Vec Id n → Vec Type n → Set where
  member : ∀{n}{i : Fin n}{j : Fin n}{fs : Vec Id n}{As : Vec Type n}{x : Id}{A : Type}
         → lookup fs i ≡ x
         → lookup As i ≡ A
         → x ⦂ A ∈ fs ⦂ As
```

```
data _⊆_ : ∀{n m} → Vec Id n → Vec Id m → Set where
  subseteq : ∀ {n m} {xs : Vec Id n} {ys : Vec Id m}
           → ((i : Fin n) → Σ[ j ∈ Fin m ] lookup xs i ≡ lookup ys j)
           → xs ⊆ ys 
```


```
data _<:_ : Type → Type → Set where
  <:-bool : `𝔹 <: `𝔹

  <:-nat : `ℕ <: `ℕ

  <:-fun : ∀{A B C D}
    → C <: A  → B <: D
      ----------------
    → A ⇒ B <: C ⇒ D

  <:-rcd :  ∀{m}{ks : Vec Id m}{Ss : Vec Type m}.{d1}
             {n}{ls : Vec Id n}{Ts : Vec Type n}.{d2}
    → ls ⊆ ks
    → (∀{i : Fin n}{j : Fin m} → lookup ks j ≡ lookup ls i
                               → lookup Ss j <: lookup Ts i)
      ------------------------------------------------------
    → Record m ks Ss {d1} <: Record n ls Ts {d2}
```

```
t-size : (A : Type) → ℕ
ts-size : ∀ {n : ℕ} → (As : Vec Type n) → ℕ

t-size `𝔹 = 1
t-size `ℕ = 1
t-size (A ⇒ B) = suc (t-size A + t-size B)
t-size (Record n fs As) = suc (ts-size As)

ts-size {n} [] = 0
ts-size {n} (x ∷ xs) = suc (t-size x + ts-size xs)

⊆-refl : ∀{n}{fs : Vec Id n} → fs ⊆ fs
⊆-refl {n}{fs} = subseteq (λ i → ⟨ i , refl ⟩)

t-size-pos : ∀ {A} → 0 < t-size A
t-size-pos {`𝔹} = s≤s z≤n
t-size-pos {`ℕ} = s≤s z≤n
t-size-pos {A ⇒ B} = s≤s z≤n
t-size-pos {Record n fs As} = s≤s z≤n

lookup-ts-size : ∀{n} {As : Vec Type n} {j}
   → ts-size As ≤ n
   → t-size (lookup As j) ≤ n
lookup-ts-size {suc n} {A ∷ As} {Data.Fin.0F} As≤n = ≤-step (m+n≤o⇒m≤o (t-size A) (≤-pred As≤n))
lookup-ts-size {suc n} {A ∷ As} {Fin.suc j} As≤n =
  let IH = lookup-ts-size {n} {As} {j} (m+n≤o⇒n≤o (t-size A) (≤-pred As≤n)) in
  ≤-step IH



<:-refl : ∀{n}{A}{m : t-size A ≤ n} → A <: A
<:-refl {0}{A}{m}
    with t-size-pos {A}
... | pos rewrite n≤0⇒n≡0 m
    with pos
... | ()    
<:-refl {suc n}{`𝔹}{m} = <:-bool
<:-refl {suc n}{`ℕ}{m} = <:-nat
<:-refl {suc n}{A ⇒ B}{m} =
  let a = ≤-pred m in
  <:-fun (<:-refl{n}{A}{m+n≤o⇒m≤o (t-size A) a }) (<:-refl{n}{B}{m+n≤o⇒n≤o (t-size A) a})
<:-refl {suc n}{Record k fs As {d}}{m} = <:-rcd {d1 = d}{d2 = d} ⊆-refl G
    where
    G : ∀ {i j : Fin k} →
          lookup fs j ≡ lookup fs i → lookup As j <: lookup As i
    G {i}{j} lij rewrite distinct-lookup-eq (distinct-rel d) lij = <:-refl {n}{lookup As j}{{!!}}

<:-trans : ∀{A B C}
    → A <: B   →   B <: C
      -------------------
    → A <: C
<:-trans = {!!}
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
{-
inversion-<:-fun : ∀{A B C : Type}
  → A <: B ⇒ C
  → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] (A ≡ A₁ ⇒ A₂ × B <: A₁ × A₂ <: C)
inversion-<:-fun {A}{B}{C} <:-refl =
    ⟨ B , ⟨ C , ⟨ refl , ⟨ <:-refl , <:-refl ⟩ ⟩ ⟩ ⟩
inversion-<:-fun (<:-trans a<:bc a<:bc₁)
    with inversion-<:-fun a<:bc₁
... | ⟨ D , ⟨ E , ⟨ refl , ⟨ s1 , s2 ⟩ ⟩ ⟩ ⟩ 
    with inversion-<:-fun a<:bc
... | ⟨ D' , ⟨ E' , ⟨ refl , ⟨ s3 , s4 ⟩ ⟩ ⟩ ⟩ =
    ⟨ D' , ⟨ E' , ⟨ refl , ⟨ (<:-trans s1 s3) , (<:-trans s4 s2) ⟩ ⟩ ⟩ ⟩
inversion-<:-fun (<:-fun {A}{B} a<:bc a<:bc₁) =
    ⟨ A , ⟨ B , ⟨ refl , ⟨ a<:bc , a<:bc₁ ⟩ ⟩ ⟩ ⟩
-}
```

```
{-
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
-}
```
