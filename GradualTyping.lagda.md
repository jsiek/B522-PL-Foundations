```
module GradualTyping where
```

# Gradually Typed Lambda Calculus

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
open import Relation.Nullary using (¬_)
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

## Types

```
data BaseTy : Set where
  Nat : BaseTy
  Bool : BaseTy

data Type : Set where
  `_    : BaseTy → Type
  ⋆     : Type
  _⇒_   : Type → Type → Type
  _`×_  : Type → Type → Type
  _`⊎_  : Type → Type → Type
```

## Consistency and Join

```
infix  5  _~_
data _~_ : Type → Type → Set where
  unk~L : ∀ {A} → ⋆ ~ A
  unk~R : ∀ {A} → A ~ ⋆
  base~ : ∀{ι} → ` ι ~ ` ι
  fun~ : ∀{A B A' B'}
    → A' ~ A  →  B ~ B'
      -------------------
    → (A ⇒ B) ~ (A' ⇒ B')
  pair~ : ∀{A B A' B'}
    → A ~ A'  →  B ~ B'
      -------------------
    → (A `× B) ~ (A' `× B')
  sum~ : ∀{A B A' B'}
    → A ~ A'  →  B ~ B'
      -------------------
    → (A `⊎ B) ~ (A' `⊎ B')
```

```
⨆ : ∀{A B : Type} → (c : A ~ B) → Type
⨆ {.⋆} {B} unk~L = B
⨆ {A} {.⋆} unk~R = A
⨆ {(` ι)} {.(` _)} base~ = ` ι
⨆ {.(_ ⇒ _)} {.(_ ⇒ _)} (fun~ c d) = (⨆ c) ⇒ (⨆ d)
⨆ {.(_ `× _)} {.(_ `× _)} (pair~ c d) = (⨆ c) `× (⨆ d)
⨆ {.(_ `⊎ _)} {.(_ `⊎ _)} (sum~ c d) = (⨆ c) `⊎ (⨆ d)
```

## Terms

We use the
[abstract-binding-trees](https://github.com/jsiek/abstract-binding-trees)
library to represent terms.

```
data Op : Set where
  op-lam : Type → Op
  op-app : Op
  op-const : (p : Prim) → rep p → Op
  op-pair : Op
  op-fst  : Op
  op-snd : Op
  op-inl : Op
  op-inr : Op
  op-case : Op

sig : Op → List ℕ
sig (op-lam A) = 1 ∷ []
sig op-app = 0 ∷ 0 ∷ []
sig (op-const p k) = []
sig op-pair = 0 ∷ 0 ∷ []
sig op-fst = 0 ∷ []
sig op-snd = 0 ∷ []
sig op-inl = 0 ∷ []
sig op-inr = 0 ∷ []
sig op-case = 0 ∷ 1 ∷ 1 ∷ []

open Syntax using (Rename; _•_; ↑; id; ext; ⦉_⦊)

open Syntax.OpSig Op sig
  using (`_; _⦅_⦆; cons; nil; bind; ast)
  renaming (ABT to Term)

infixl 7  _·_

pattern $ p k      = (op-const p k) ⦅ nil ⦆
pattern ƛ_˙_ A N    = op-lam A       ⦅ cons (bind (ast N)) nil ⦆
pattern _·_ L M    = op-app         ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern pair L M   = op-pair        ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern fst M      = op-fst         ⦅ cons (ast M) nil ⦆
pattern snd M      = op-snd         ⦅ cons (ast M) nil ⦆
pattern inl M      = op-inl         ⦅ cons (ast M) nil ⦆
pattern inr M      = op-inr         ⦅ cons (ast M) nil ⦆
pattern case L M N = op-case        ⦅ cons (ast L) (cons (bind (ast M))
                                                   (cons (bind (ast N)) nil)) ⦆
```

## Type of a primitive

```
typeof-base : Base → Type
typeof-base B-Nat = ` Nat
typeof-base B-Bool = ` Bool

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

## Type Matching

```
data _▹_⇒_ : Type → Type → Type → Set where
  match⇒⇒ : ∀{A B} → (A ⇒ B) ▹ A ⇒ B
  match⇒⋆ : ⋆ ▹ ⋆ ⇒ ⋆

data _▹_×_ : Type → Type → Type → Set where
  match×× : ∀{A B} → (A `× B) ▹ A × B
  match×⋆ : ⋆ ▹ ⋆ × ⋆

data _▹_⊎_ : Type → Type → Type → Set where
  match⊎⊎ : ∀{A B} → (A `⊎ B) ▹ A ⊎ B
  match⊎⋆ : ⋆ ▹ ⋆ ⊎ ⋆
```

## Typing judgement

```
infix  4  _⊢G_⦂_

data _⊢G_⦂_ : Context → Term → Type → Set where

  -- Axiom 
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢G ` x ⦂ A

  -- ⇒-I 
  ⊢ƛ : ∀ {Γ N A B}
    → Γ , A ⊢G N ⦂ B
      -------------------
    → Γ ⊢G (ƛ A ˙ N) ⦂ A ⇒ B

  -- ⇒-E
  ⊢· : ∀ {Γ L M A A₁ A₂ B}
    → Γ ⊢G L ⦂ A
    → Γ ⊢G M ⦂ B
    → A ▹ A₁ ⇒ A₂
    → A₁ ~ B
      --------------
    → Γ ⊢G L · M ⦂ A₂

  ⊢$ : ∀{Γ p k A}
     → A ≡ typeof p
       -------------
     → Γ ⊢G $ p k ⦂ A

  ⊢pair : ∀ {Γ A B}{M N : Term}
    → Γ ⊢G M ⦂ A  →  Γ ⊢G N ⦂ B
      -----------------------
    → Γ ⊢G (pair M N) ⦂ A `× B
    
  ⊢fst : ∀ {Γ A A₁ A₂}{M : Term}
    → Γ ⊢G M ⦂ A
    → A ▹ A₁ × A₂
      -------------------------
    → Γ ⊢G fst M ⦂ A₁

  ⊢snd : ∀ {Γ A A₁ A₂}{M : Term}
    → Γ ⊢G M ⦂ A
    → A ▹ A₁ × A₂
      -------------------------
    → Γ ⊢G (snd M) ⦂ A₂

  ⊢inl : ∀ {Γ A}{M : Term}
    → (B : Type)
    → Γ ⊢G M ⦂ A
      -----------------------
    → Γ ⊢G (inl M) ⦂ A `⊎ B

  ⊢inr : ∀ {Γ B}{M : Term}
    → (A : Type)
    → Γ ⊢G M ⦂ B
      -----------------------
    → Γ ⊢G (inr M) ⦂ A `⊎ B

  ⊢case : ∀{Γ A A₁ A₂ B B₁ B₂ C C₁ C₂}{L M N : Term}
    → Γ ⊢G L ⦂ A
    → Γ ⊢G M ⦂ B
    → Γ ⊢G N ⦂ C
    → {ma : A ▹ A₁ ⊎ A₂ }
    → {mb : B ▹ B₁ ⇒ B₂ }
    → {mc : C ▹ C₁ ⇒ C₂ }
    → {ab : A₁ ~ B₁}
    → {ac : A₂ ~ C₁}
    → {bc : B₂ ~ C₂}
      ----------------------------------
    → Γ ⊢G (case L M N) ⦂ ⨆ bc
```

## Cast Calculus

```
data cc-Op : Set where
  op-cc-lam : cc-Op
  op-cc-app : cc-Op
  op-cc-const : (p : Prim) → rep p → cc-Op
  op-cc-pair : cc-Op
  op-cc-fst  : cc-Op
  op-cc-snd : cc-Op
  op-cc-inl : cc-Op
  op-cc-inr : cc-Op
  op-cc-case : cc-Op
  op-cc-cast : Type → Type → cc-Op
  op-cc-blame : cc-Op

cc-sig : cc-Op → List ℕ
cc-sig op-cc-lam = 1 ∷ []
cc-sig op-cc-app = 0 ∷ 0 ∷ []
cc-sig (op-cc-const p k) = []
cc-sig op-cc-pair = 0 ∷ 0 ∷ []
cc-sig op-cc-fst = 0 ∷ []
cc-sig op-cc-snd = 0 ∷ []
cc-sig op-cc-inl = 0 ∷ []
cc-sig op-cc-inr = 0 ∷ []
cc-sig op-cc-case = 0 ∷ 1 ∷ 1 ∷ []
cc-sig (op-cc-cast A B) = 0 ∷ []
cc-sig op-cc-blame = []

open Syntax using (Rename; _•_; ↑; id; ext; ⦉_⦊)

open Syntax.OpSig cc-Op cc-sig
  using (_[_]; Subst; ⟪_⟫; ⟦_⟧; exts; rename)
  renaming (`_ to ^_; _⦅_⦆ to _〖_〗; ABT to cc-Term;
  cons to cc-cons; nil to cc-nil; bind to cc-bind; ast to cc-ast)

pattern ! p k      = (op-cc-const p k)〖 cc-nil 〗
pattern ƛ N      = op-cc-lam        〖 cc-cons (cc-bind (cc-ast N)) cc-nil 〗
pattern app L M    = op-cc-app        〖 cc-cons (cc-ast L) (cc-cons (cc-ast M) cc-nil) 〗
pattern cc-pair L M   = op-cc-pair    〖 cc-cons (cc-ast L) (cc-cons (cc-ast M) cc-nil) 〗
pattern cc-fst M      = op-cc-fst     〖 cc-cons (cc-ast M) cc-nil 〗
pattern cc-snd M      = op-cc-snd     〖 cc-cons (cc-ast M) cc-nil 〗
pattern cc-inl M      = op-cc-inl     〖 cc-cons (cc-ast M) cc-nil 〗
pattern cc-inr M      = op-cc-inr     〖 cc-cons (cc-ast M) cc-nil 〗
pattern cc-case L M N = op-cc-case    〖 cc-cons (cc-ast L) (cc-cons (cc-bind (cc-ast M))
                                                   (cc-cons (cc-bind (cc-ast N)) cc-nil)) 〗
pattern _⟨_⇛_⟩ M A B = op-cc-cast A B 〖 cc-cons (cc-ast M) cc-nil 〗
pattern blame = op-cc-blame  〖 cc-nil 〗
```


```
infix  4  _⊢_⦂_

data _⊢_⦂_ : Context → cc-Term → Type → Set where

  -- Axiom 
  ⊢^ : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ^ x ⦂ A

  -- ⇒-I 
  ⊢ƛ : ∀ {Γ A B}{N : cc-Term}
    → Γ , A ⊢ N ⦂ B
      -------------------
    → Γ ⊢ ƛ N ⦂ A ⇒ B

  -- ⇒-E
  ⊢· : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      --------------
    → Γ ⊢ app L M ⦂ B

  ⊢! : ∀{Γ p k A}
     → A ≡ typeof p
       -------------
     → Γ ⊢ ! p k ⦂ A

  ⊢pair : ∀ {Γ A B}{M N : cc-Term}
    → Γ ⊢ M ⦂ A  →  Γ ⊢ N ⦂ B
      -----------------------
    → Γ ⊢ (cc-pair M N) ⦂ A `× B
    
  ⊢fst× : ∀ {Γ A B}{M : cc-Term}
    → Γ ⊢ M ⦂ A `× B
      -------------------------
    → Γ ⊢ cc-fst M ⦂ A

  ⊢snd× : ∀ {Γ A B}{M : cc-Term}
    → Γ ⊢ M ⦂ A `× B
      -------------------------
    → Γ ⊢ (cc-snd M) ⦂ B

  ⊢inl : ∀ {Γ A}{M : cc-Term}
    → (B : Type)
    → Γ ⊢ M ⦂ A
      -----------------------
    → Γ ⊢ (cc-inl M) ⦂ A `⊎ B

  ⊢inr : ∀ {Γ B}{M : cc-Term}
    → (A : Type)
    → Γ ⊢ M ⦂ B
      -----------------------
    → Γ ⊢ (cc-inr M) ⦂ A `⊎ B

  ⊢case : ∀{Γ A B C}{L M N : cc-Term}
    → Γ ⊢ L ⦂ A `⊎ B
    → Γ ⊢ M ⦂ A ⇒ C
    → Γ ⊢ N ⦂ B ⇒ C
      ----------------------------------
    → Γ ⊢ (cc-case L M N) ⦂ C

  ⊢cast : ∀ {Γ A B}{M : cc-Term}
    → Γ ⊢ M ⦂ A
    → A ~ B
      -----------------------
    → Γ ⊢ M ⟨ A ⇛ B ⟩ ⦂ B

  ⊢blame : ∀ {Γ A}
      -------------
    → Γ ⊢ blame ⦂ A
```

## Compile from GTCL to CC

```
compile : ∀{Γ A}{M : Term} → Γ ⊢G M ⦂ A → cc-Term
compile (⊢` {x = x} x∈) = ^ x
compile (⊢ƛ {N = N} ⊢N) = ƛ (compile ⊢N)
compile (⊢· {L = L}{M}{A}{A₁}{A₂}{B} ⊢L ⊢M m cn) =
   let L' = (compile ⊢L) ⟨ A ⇛ (A₁ ⇒ A₂) ⟩ in
   let M' = (compile ⊢M) ⟨ B ⇛ A₁ ⟩ in
   app L' M'
compile (⊢$ {p = p}{k} eq) = ! p k
compile (⊢pair ⊢L ⊢M) =
   let L' = compile ⊢L in
   let M' = compile ⊢M in
   cc-pair L' M'
compile (⊢fst {A = A}{A₁}{A₂} ⊢M m) =
   let M' = (compile ⊢M) ⟨ A ⇛ (A₁ `× A₂) ⟩ in
   cc-fst M'
compile (⊢snd {A = A}{A₁}{A₂} ⊢M m) =
   let M' = (compile ⊢M) ⟨ A ⇛ (A₁ `× A₂) ⟩ in
   cc-snd M'
compile (⊢inl B ⊢M) = cc-inl (compile ⊢M)
compile (⊢inr B ⊢M) = cc-inr (compile ⊢M)
compile (⊢case {Γ}{A}{A₁}{A₂}{B}{B₁}{B₂}{C}{C₁}{C₂} ⊢L ⊢M ⊢N 
          {ma}{mb}{mc}{ab}{ac}{bc}) =
      let L' = (compile ⊢L) ⟨ A ⇛ (A₁ `⊎ A₂) ⟩
                ⟨ (A₁ `⊎ A₂) ⇛ (B₁ `⊎ C₁) ⟩ in
      let M' = (compile ⊢M) ⟨ B ⇛ (B₁ ⇒ B₂) ⟩
                ⟨ (B₁ ⇒ B₂) ⇛ (B₁ ⇒ ⨆ bc) ⟩ in
      let N' = (compile ⊢N) ⟨ C ⇛ (C₁ ⇒ C₂) ⟩
                ⟨ (C₁ ⇒ C₂) ⇛ (C₁ ⇒ ⨆ bc) ⟩ in
      cc-case L' M' N'
```

## Cast Calculus Reduction

```
data Value : cc-Term → Set where

  V-ƛ : {N : cc-Term}
      -----------
    → Value (ƛ N)

  V-const : ∀ {p k}
      -------------
    → Value (! p k)

  V-pair : ∀ {V W : cc-Term}
    → Value V → Value W
      -----------------
    → Value (cc-pair V W)

  V-inl : ∀ {V : cc-Term}
    → Value V
      --------------------------
    → Value (cc-inl V)

  V-inr : ∀ {V : cc-Term}
    → Value V
      --------------------------
    → Value (cc-inr V)

  V-cast : ∀ {A : Type}{V : cc-Term}
    → Value V
      ---------------
    → Value (V ⟨ A ⇛ ⋆ ⟩)
```

```
data Frame : Set where

  F-·₁ : 
      cc-Term
    → Frame

  F-·₂ : 
      (M : cc-Term) → Value M
    → Frame

  F-×₁ : 
      cc-Term
    → Frame

  F-×₂ :
      cc-Term
    → Frame

  F-fst : Frame

  F-snd : Frame

  F-inl : Frame

  F-inr : Frame

  F-case : 
      cc-Term
    → cc-Term
    → Frame

  F-cast :
      Type → Type
    → Frame
```

```
plug : cc-Term → Frame → cc-Term
plug L (F-·₁ M)      = app L M
plug M (F-·₂ L v)      = app L M
plug L (F-×₁ M)      = cc-pair M L
plug M (F-×₂ L)      = cc-pair M L
plug M (F-fst)      = cc-fst M
plug M (F-snd)      = cc-snd M
plug M (F-inl)      = cc-inl M
plug M (F-inr)      = cc-inr M
plug L (F-case M N) = cc-case L M N
plug M (F-cast A B) = M ⟨ A ⇛ B ⟩
```

```
infix 2 _—→_
data _—→_ : cc-Term → cc-Term → Set where

  ξ : ∀ {M M′ : cc-Term} {F : Frame}
    → M —→ M′
      ---------------------
    → plug M F —→ plug M′ F

  ξ-blame : {F : Frame}
      ---------------------
    → plug blame F —→ blame

  β : ∀ {N W : cc-Term}
    → Value W
      ----------------------
    → app (ƛ N) W —→ N [ W ]

  δ : ∀ {p}{b} {f : base-rep b → rep p} {k : base-rep b}
      -------------------------------------------------------
    → app (! (b ⇒ p) f) (! (base b) k) —→ ! p (f k)

  β-fst :  ∀ {V W : cc-Term}
    → Value V → Value W
      --------------------
    → cc-fst (cc-pair V W) —→ V

  β-snd :  ∀ {V : cc-Term} {W : cc-Term}
    → Value V → Value W
      --------------------
    → cc-snd (cc-pair V W) —→ W

  β-caseL : ∀ {V L M : cc-Term}
    → Value V
      ---------------------------------
    → cc-case (cc-inl V) L M —→ app L V

  β-caseR : ∀ {V L M : cc-Term}
    → Value V
      ---------------------------------
    → cc-case (cc-inr V) L M —→ app M V

  cast⇒ : ∀ {V : cc-Term} {A B C D : Type}
    → (v : Value V)
      ----------------------------------------------------------------
    → V ⟨ (A ⇒ B) ⇛ (C ⇒ D) ⟩ —→ ƛ (app V ((^ 0) ⟨ C ⇛ A ⟩)) ⟨ B ⇛ D ⟩

  cast⋆ : ∀ {V : cc-Term} {A B : Type}
    → (v : Value V) → A ~ B
      ------------------------------------
    → V ⟨ A ⇛ ⋆ ⟩ ⟨ ⋆ ⇛ B ⟩ —→ V ⟨ A ⇛ B ⟩

  cast-fail : ∀ {V : cc-Term} {A B : Type}
    → (v : Value V) → ¬ (A ~ B)
      ------------------------------
    → V ⟨ A ⇛ ⋆ ⟩ ⟨ ⋆ ⇛ B ⟩ —→ blame

  cast× : ∀ {V : cc-Term} {A B C D : Type}
    → (v : Value V)
      -----------------------------------------------------------
    → V ⟨ (A `× B) ⇛ (C `× D) ⟩ —→ cc-pair ((cc-fst V) ⟨ A ⇛ C ⟩)
                                           ((cc-snd V) ⟨ B ⇛ D ⟩)

  cast-inl : ∀ {V : cc-Term} {A B C D : Type}
    → (v : Value V)
      --------------------------------------------------------
    → cc-inl V ⟨ (A `⊎ B) ⇛ (C `⊎ D) ⟩ —→ cc-inl (V ⟨ A ⇛ C ⟩)

  cast-inr : ∀ {V : cc-Term} {A B C D : Type}
    → (v : Value V)
      --------------------------------------------------------
    → cc-inr V ⟨ (A `⊎ B) ⇛ (C `⊎ D) ⟩ —→ cc-inr (V ⟨ B ⇛ D ⟩)

infix  2 _—↠_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : cc-Term → cc-Term → Set where
  _∎ : ∀ (M : cc-Term)
      ---------
    → M —↠ M

  _—→⟨_⟩_ : ∀ (L : cc-Term) {M N : cc-Term}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N
```
