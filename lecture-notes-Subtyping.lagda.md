```
module lecture-notes-Subtyping where
```

## Imports

```
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_)
open import Data.Vec
  using (Vec; toList; []; _∷_; lookup)
open import Data.Fin using (Fin; 0F; suc; reduce≥)
open import Data.Vec.Membership.Propositional using (_∈_)
open import Data.Vec.Any using (Any; here; there)
open import Data.Nat using (ℕ; zero; suc; _<_; _+_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-pred; m+n≤o⇒m≤o; m+n≤o⇒n≤o; n≤0⇒n≡0; ≤-step)
open import Data.Bool using () renaming (Bool to 𝔹)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
   renaming (_,_ to ⟨_,_⟩)
open import Data.String using (String; _≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym; trans)
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
_⦂_<:_⦂_ : ∀ {m n} → Vec Id m → Vec Type m → Vec Id n → Vec Type n → Set
_⦂_<:_⦂_ {m}{n} ks Ss ls Ts = (∀{i : Fin n}{j : Fin m} → lookup ks j ≡ lookup ls i
                               → lookup Ss j <: lookup Ts i)
```

```
t-size : (A : Type) → ℕ
ts-size : ∀ {n : ℕ} → (As : Vec Type n) → ℕ

t-size `𝔹 = 1
t-size `ℕ = 1
t-size (A ⇒ B) = suc (t-size A + t-size B)
t-size (Record n fs As) = suc (ts-size As)

ts-size {n} [] = 0
ts-size {n} (x ∷ xs) = t-size x + ts-size xs

⊆-refl : ∀{n}{fs : Vec Id n} → fs ⊆ fs
⊆-refl {n}{fs} = subseteq (λ i → ⟨ i , refl ⟩)


⊆-trans : ∀{l n m}{ns  : Vec Id n}{ms  : Vec Id m}{ls  : Vec Id l}
        → ns ⊆ ms   →    ms ⊆ ls
        → ns ⊆ ls
⊆-trans {l}{n}{m}{ns}{ms}{ls} (subseteq a) (subseteq b) = subseteq G
    where
    G : (i : Fin n) →  Σ[ j ∈ Fin l ] lookup ns i ≡ lookup ls j
    G i
        with a i
    ... | ⟨ j , lk1 ⟩
        with b j
    ... | ⟨ k , lk2 ⟩
        rewrite lk1 | lk2 = ⟨ k , refl ⟩

t-size-pos : ∀ {A} → 0 < t-size A
t-size-pos {`𝔹} = s≤s z≤n
t-size-pos {`ℕ} = s≤s z≤n
t-size-pos {A ⇒ B} = s≤s z≤n
t-size-pos {Record n fs As} = s≤s z≤n

lookup-ts-size : ∀{n}{k} {As : Vec Type k} {j}
   → ts-size As ≤ n
   → t-size (lookup As j) ≤ n
lookup-ts-size {n} {suc k} {A ∷ As} {Data.Fin.0F} As≤n = m+n≤o⇒m≤o (t-size A) As≤n
lookup-ts-size {n} {suc k}{A ∷ As} {Fin.suc j} As≤n =
    lookup-ts-size {n} {k} {As} {j} (m+n≤o⇒n≤o (t-size A) As≤n)

<:-refl-aux : ∀{n}{A}{m : t-size A ≤ n} → A <: A
<:-refl-aux {0}{A}{m}
    with t-size-pos {A}
... | pos rewrite n≤0⇒n≡0 m
    with pos
... | ()    
<:-refl-aux {suc n}{`𝔹}{m} = <:-bool
<:-refl-aux {suc n}{`ℕ}{m} = <:-nat
<:-refl-aux {suc n}{A ⇒ B}{m} =
  let a = ≤-pred m in
  <:-fun (<:-refl-aux{n}{A}{m+n≤o⇒m≤o (t-size A) a }) (<:-refl-aux{n}{B}{m+n≤o⇒n≤o (t-size A) a})
<:-refl-aux {suc n}{Record k fs As {d}}{m} = <:-rcd {d1 = d}{d2 = d} ⊆-refl G
    where
    G : ∀ {i j : Fin k} →
          lookup fs j ≡ lookup fs i → lookup As j <: lookup As i
    G {i}{j} lij rewrite distinct-lookup-eq (distinct-rel d) lij =
        let Asⱼ≤n = lookup-ts-size {n}{k}{As}{j} (≤-pred m) in 
        <:-refl-aux {n}{lookup As j}{Asⱼ≤n}

<:-refl : ∀{A} → A <: A
<:-refl {A} = <:-refl-aux {t-size A}{A}{≤-refl}

lookup-⊆ : ∀{n m : ℕ}{ns : Vec Id n}{ms : Vec Id m}{i : Fin n}
   → ns ⊆ ms
   → Σ[ k ∈ Fin m ] lookup ns i ≡ lookup ms k
lookup-⊆ {suc n} {m} {x ∷ ns} {ms} {i} (subseteq x₁) = x₁ i


<:-trans : ∀{A B C}
    → A <: B   →   B <: C
      -------------------
    → A <: C
<:-trans {.`𝔹} {`𝔹} {.`𝔹} <:-bool <:-bool = <:-bool
<:-trans {.`ℕ} {`ℕ} {.`ℕ} <:-nat <:-nat = <:-nat
<:-trans {A₁ ⇒ A₂} {B₁ ⇒ B₂} {C₁ ⇒ C₂} (<:-fun A<:B A<:B₁) (<:-fun B<:C B<:C₁) =
    <:-fun (<:-trans B<:C A<:B) (<:-trans A<:B₁ B<:C₁)
<:-trans {Record l ls As {d1} } {Record m ms Bs {d2} } {Record n ns Cs {d3} } (<:-rcd ms⊆ls As<:Bs) (<:-rcd ns⊆ms Bs<:Cs) =
    <:-rcd (⊆-trans ns⊆ms ms⊆ls) G
    where
    G : {i : Fin n} {j : Fin l} →
      lookup ls j ≡ lookup ns i → lookup As j <: lookup Cs i
    G {i}{j} lij
        with lookup-⊆ {i = i} ns⊆ms 
    ... | ⟨ k , lik ⟩
        with lookup-⊆ {i = k} ms⊆ls
    ... | ⟨ j' , lkj' ⟩ rewrite sym lkj' | lij | sym lik  =
        let ab = As<:Bs {k}{j} (trans lij lik) in
        let bc = Bs<:Cs {i}{k} (sym lik) in
        <:-trans ab bc
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
  → Σ[ A₁ ∈ Type ] Σ[ A₂ ∈ Type ] (A ≡ A₁ ⇒ A₂ × B <: A₁ × A₂ <: C)
inversion-<:-fun {A₁ ⇒ A₂} {B} {C} (<:-fun B<:A₁ A₂<:C) = ⟨ A₁ , ⟨ A₂ , ⟨ refl , ⟨ B<:A₁ , A₂<:C ⟩ ⟩ ⟩ ⟩
```

```
inversion-<:-base : ∀ {b A}
  → A <: typeof-base b
  → A ≡ typeof-base b
inversion-<:-base {B-Nat} <:-nat = refl
inversion-<:-base {B-Bool} <:-bool = refl
```

```
inversion-<:-rcd : ∀{A k}{ks : Vec Id k}{Bs : Vec Type k}{dks : distinct ks}
  → A <: Record k ks Bs {dks}
  → Σ[ n ∈ ℕ ] Σ[ ns ∈ Vec Id n ] Σ[ As ∈ Vec Type n ] Σ[ dns ∈ distinct ns ]
       A ≡ Record n ns As {dns} × ks ⊆ ns × (ns ⦂ As <: ks ⦂ Bs)
inversion-<:-rcd {Record n ns As {dns}} (<:-rcd ks⊆ns As<:Bs) =
    ⟨ n , ⟨ ns , ⟨ As , ⟨ (distinct-rel dns) , ⟨ refl , ⟨ ks⊆ns , As<:Bs ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
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
  op-rcd : (n : ℕ) → Vec Id n → Op
  op-member : Id → Op

replicate : ℕ → ℕ → List ℕ
replicate x 0 = []
replicate x (suc n) = x ∷ replicate x n

sig : Op → List ℕ
sig (op-lam A) = 1 ∷ []
sig op-app = 0 ∷ 0 ∷ []
sig op-rec = 1 ∷ []
sig (op-const p k) = []
sig op-let = 0 ∷ 1 ∷ []
sig (op-rcd n fs) = replicate 0 n
sig (op-member f) = 0 ∷ []

open Syntax Op sig
  using (`_; _⦅_⦆; cons; nil; bind; ast; _[_];
         Rename; Subst; ⟪_⟫; ⟦_⟧; exts; _•_; 
         ↑; _⨟_; exts-0; exts-suc-rename; rename; ext; ⦉_⦊;
         ext-0; ext-suc; Args; Arg)
  renaming (ABT to Term)

pattern $ p k = (op-const p k) ⦅ nil ⦆

pattern λ:_⇒_ A N  = (op-lam A) ⦅ cons (bind (ast N)) nil ⦆

pattern μ N  = op-rec ⦅ cons (bind (ast N)) nil ⦆

pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆

pattern `let L M = op-let ⦅ cons (ast L) (cons (bind (ast M)) nil) ⦆

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
data _⊢*_⦂_ : Context → ∀ {n} → Args (replicate 0 n) → Vec Type n → Set 

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

  ⊢rcd : ∀{Γ n}{Ms : Args (replicate 0 n) }{As : Vec Type n}{fs : Vec Id n}
    → Γ ⊢* Ms ⦂ As
    → (d : distinct fs)
    →  Γ ⊢ (op-rcd n fs) ⦅ Ms ⦆ ⦂ Record n fs As {d}

  ⊢# : ∀{Γ A R n fs As d i f}
    → Γ ⊢ R ⦂ Record n fs As {d}
    → lookup fs i ≡ f
    → lookup As i ≡ A
      ----------------
    → Γ ⊢ R # f ⦂ A

  ⊢<: : ∀{Γ M A B}
    → Γ ⊢ M ⦂ A   → A <: B
      --------------------
    → Γ ⊢ M ⦂ B

data _⊢*_⦂_ where
  ⊢*nil : ∀{Γ} → Γ ⊢* nil ⦂ []

  ⊢*cons : ∀ {n}{Γ M}{Ms : Args (replicate 0 n)}{A}{As : Vec Type n}
         → Γ ⊢ M ⦂ A
         → Γ ⊢* Ms ⦂ As
         → Γ ⊢* (cons (ast M) Ms) ⦂ (A ∷ As)
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

  V-rcd : ∀{n}{fs}{Ms} → Value ((op-rcd n fs) ⦅ Ms  ⦆ )
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
  rcd□ : ∀ {n : ℕ} (i : Fin n) → Vec Id n → Args (replicate 0 n) → Frame
  □#_ : Id → Frame
  let□ : Term → Frame
```

The `plug` function fills a frame's hole with a term.

```
plug : Term → Frame → Term
plug L (□· M)             = L · M
plug M ((L ·□) v)         = L · M
plug M (rcd□ {n} i fs Ms) = (op-rcd n fs) ⦅ insert {n} M i Ms ⦆
    where
    insert : ∀{n} → Term → (i : Fin n) → Args (replicate 0 n) → Args (replicate 0 n)
    insert {suc n} M 0F (cons M' Ms) = cons (ast M) Ms
    insert {suc n} M (suc i) (cons M' Ms) = cons M' (insert {n} M i Ms)
plug M (□# f)          = M # f
plug M (let□ N)        = `let M N
```

## Reduction

```
getfield : {n : ℕ} → (i : Fin n) → Args (replicate 0 n) → Term
getfield {suc n} 0F (cons (ast M) Ms) = M
getfield {suc n} (suc i) (cons (ast M) Ms) = getfield {n} i Ms
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

  β-# : ∀ {n}{fs : Vec Id n}{Ms : Args (replicate 0 n)} {f}{i : Fin n}
    → lookup fs i ≡ f
      ---------------------------------------------
    → ((op-rcd n fs) ⦅ Ms ⦆ ) # f —→  getfield i Ms
```

## Canonical Forms

```
data Function : Term → Type → Set where
  Fun-λ : ∀ {A B}{N} → Function (λ: A ⇒ N) B
  Fun-prim : ∀{b p k A}
    → typeof (b ⇒ p) <: A
    → Function ($ (b ⇒ p) k) A

canonical-fun : ∀{V A B}
  → ∅ ⊢ V ⦂ A ⇒ B
  → Value V
    ------------------
  → Function V (A ⇒ B)
canonical-fun (⊢λ ⊢V) vV = Fun-λ
canonical-fun (⊢$ {p = base B-Nat} ()) vV
canonical-fun (⊢$ {p = base B-Bool} ()) vV
canonical-fun (⊢$ {p = b ⇒ p} refl) vV = Fun-prim <:-refl
canonical-fun (⊢<: ⊢V <:A→B) vV
    with inversion-<:-fun <:A→B
... | ⟨ C , ⟨ D , ⟨ refl , _ ⟩ ⟩ ⟩
    with canonical-fun ⊢V vV
... | Fun-λ = Fun-λ
... | Fun-prim lt = Fun-prim (<:-trans lt <:A→B)
```

```
data Constant : Base → Term → Set where
  base-const : ∀{b k} → Constant b ($ (base b) k)

canonical-base : ∀{b V}
  → ∅ ⊢ V ⦂ typeof-base b
  → Value V
    ------------
  → Constant b V
canonical-base {B-Nat} (⊢$ {.∅} {base B-Nat} x) vV = base-const
canonical-base {B-Nat} (⊢<: ⊢V A<:) vV
    rewrite inversion-<:-base A<: = canonical-base ⊢V vV
canonical-base {B-Bool} (⊢$ {.∅} {base B-Bool} x) vV = base-const
canonical-base {B-Bool} (⊢<: ⊢V A<:) vV
    rewrite inversion-<:-base A<: = canonical-base ⊢V vV
```

todo: add a Type parameter to Rcd

```
data Rcd : Term → Set where
  rcd : ∀{n : ℕ}{fs : Vec Id n}{Ms : Args (replicate 0 n)}
      → Rcd ((op-rcd n fs) ⦅ Ms ⦆)
```

```
canonical-rcd : ∀{V n fs As d}
   → ∅ ⊢ V ⦂ Record n fs As {d}
   → Value V
   → Rcd V
canonical-rcd (⊢$ {p = base B-Nat} ()) vV
canonical-rcd (⊢$ {p = base B-Bool} ()) vV
canonical-rcd (⊢rcd x d) vV = rcd
canonical-rcd {d = d} (⊢<: ⊢V A<:) vV
    with inversion-<:-rcd {dks = d} A<:
... | ⟨ n , ⟨ ns , ⟨ As , ⟨ dns , ⟨ refl , _ ⟩ ⟩ ⟩ ⟩ ⟩ =
    canonical-rcd {d = dns} ⊢V vV
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
        with canonical-fun ⊢L VL 
...     | Fun-λ                           = step (β-λ VM)
...     | Fun-prim {b}{p}{k} p⇒b<:A⇒B
        with inversion-<:-fun p⇒b<:A⇒B
...     | ⟨ A₁ , ⟨ A₂ , ⟨ refl , ⟨ A<:p , b<:B ⟩ ⟩ ⟩ ⟩
        with inversion-<:-base A<:p
...     | refl
        with canonical-base ⊢M VM 
...     | base-const                      = step δ
progress (⊢μ ⊢M)                          = step β-μ
progress (⊢let {N = N} ⊢L ⊢N)
    with progress ⊢L
... | step L—→L′                          = step (ξ (let□ N) L—→L′)
... | done VL                             = step (β-let VL)
progress (⊢# {n = n}{fs}{As}{d}{i}{f} ⊢R lif liA)
    with progress ⊢R
... | step R—→R′                          = step (ξ (□# f) R—→R′)
... | done VR
    with canonical-rcd {d = d} ⊢R VR
... | rcd {n'}{fs'}{Ms} = step (β-# {!!})
progress (⊢rcd x d)                       = done V-rcd
progress (⊢<: {A = A}{B} ⊢M A<:B)         = progress ⊢M
```
