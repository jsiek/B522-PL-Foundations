```
module STLC-Termination where
```

# A proof that all STLC programs terminate

## Imports

```
import Syntax
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
   renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂)
```

## Syntax

```
data Op : Set where
  op-lam : Op
  op-app : Op
  op-zero : Op
  op-suc : Op
  op-case : Op

sig : Op → List ℕ
sig op-lam = 1 ∷ []
sig op-app = 0 ∷ 0 ∷ []
sig op-zero = []
sig op-suc = 0 ∷ []
sig op-case = 0 ∷ 0 ∷ 1 ∷ []

open Syntax Op sig
  using (`_; _⦅_⦆; cons; nil; bind; ast;
         _[_]; Subst; ⟪_⟫; exts; _•_; id; exts-sub-cons)
  renaming (ABT to Term; ∣_∣ to ⟦_⟧)

infixl 7  _·_

pattern ƛ N  = op-lam ⦅ cons (bind (ast N)) nil ⦆
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern `zero = op-zero ⦅ nil ⦆
pattern `suc N = op-suc ⦅ cons (ast N) nil ⦆
pattern case L M N =
    op-case ⦅ cons (ast L) (cons (ast M) (cons (bind (ast N)) nil)) ⦆

_ : ∀ (L M : Term) → ⟪ M • L • id ⟫ (` 1 · ` 0) ≡ L · M
_ = λ L M → refl

_ : ∀ (L M : Term) (σ : Subst) → ⟪ σ ⟫ (L · M) ≡ (⟪ σ ⟫ L) · (⟪ σ ⟫ M)
_ = λ L M σ → refl

_ : ∀ (N : Term) (σ : Subst) → ⟪ σ ⟫ (ƛ N) ≡ ƛ (⟪ exts σ ⟫ N)
_ = λ N σ → refl 
```

## Types

This language includes types for functions and natural numbers.

```
data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type
```

We represent a typing context as a list of types.

```
Context : Set
Context = List Type

nth : ∀{A : Set} → List A → ℕ → Maybe A
nth [] k = nothing
nth (x ∷ ls) zero = just x
nth (x ∷ ls) (suc k) = nth ls k
```

The term typing judgement is defined as follows.

```
infix  4  _⊢_⦂_

data _⊢_⦂_ : Context → Term → Type → Set where

  -- Axiom 
  ⊢` : ∀ {Γ x A}
    → nth Γ x ≡ just A
      ----------------
    → Γ ⊢ ` x ⦂ A

  -- ⇒-I 
  ⊢ƛ : ∀ {Γ N A B}
    → A ∷ Γ ⊢ N ⦂ B
      -------------------
    → Γ ⊢ ƛ N ⦂ A ⇒ B

  -- ⇒-E
  ⊢· : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B

  -- ℕ-I₁
  ⊢zero : ∀ {Γ}
      --------------
    → Γ ⊢ `zero ⦂ `ℕ

  -- ℕ-I₂
  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ⦂ `ℕ
      ---------------
    → Γ ⊢ `suc M ⦂ `ℕ

  -- ℕ-E
  ⊢case : ∀ {Γ L M N A}
    → Γ ⊢ L ⦂ `ℕ
    → Γ ⊢ M ⦂ A
    → `ℕ ∷ Γ ⊢ N ⦂ A
      -------------------------------------
    → Γ ⊢ case L M N ⦂ A
```

## Values

```
data Value : Term → Set where

  V-ƛ : ∀ {N : Term}
      ---------------------------
    → Value (ƛ N)

  V-zero :
      -----------------
      Value (`zero)

  V-suc : ∀ {V : Term}
    → Value V
      --------------
    → Value (`suc V)
```

## Reduction

```
infix 2 _—→_

data _—→_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L′ M : Term}
    → L —→ L′
      ---------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {V M M′ : Term}
    → Value V
    → M —→ M′
      ---------------
    → V · M —→ V · M′

  β-ƛ : ∀ {N W : Term}
    → Value W
      --------------------
    → (ƛ N) · W —→ N [ W ]

  ξ-suc : ∀ {M M′ : Term}
    → M —→ M′
      -----------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {L L′ M N : Term}
    → L —→ L′
      -------------------------
    → case L M N —→ case L′ M N

  β-zero :  ∀ {M N : Term}
      -------------------
    → case `zero M N —→ M

  β-suc : ∀ {V M N : Term}
    → Value V
      ----------------------------
    → case (`suc V) M N —→ N [ V ]
```

## Multi-step reduction

```
infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infixr 2 _—↠⟨_⟩_
infix  3 _∎

data _—↠_ : Term → Term → Set where

  _∎ : (M : Term)
      ------
    → M —↠ M

  _—→⟨_⟩_ : ∀ (L : Term) {M N : Term}
    → L —→ M
    → M —↠ N
      ------
    → L —↠ N

begin_ : ∀ {M N : Term}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N
```

```
—↠-trans : ∀{M N L : Term} → M —↠ N → N —↠ L → M —↠ L
—↠-trans (M ∎) N—↠L = N—↠L
—↠-trans (L —→⟨ red ⟩ M—↠N) N—↠L =
  let IH = —↠-trans M—↠N N—↠L in
  L —→⟨ red ⟩ IH

_—↠⟨_⟩_ : ∀ (L : Term) {M N : Term}
    → L —↠ M
    → M —↠ N
      ------
    → L —↠ N
L —↠⟨ LM ⟩ MN = —↠-trans LM MN
```

## Termination via Logical Relations

```
WTE : (A : Type) → Term → Set
WTV : (A : Type) → Term → Set

WTE A M = Σ[ V ∈ Term ] (M —↠ V) × (Value V) × (WTV A V)

WTV `ℕ (` x) = ⊥
WTV `ℕ (ƛ N) = ⊥
WTV `ℕ (L · M) = ⊥
WTV `ℕ `zero = ⊤
WTV `ℕ (`suc M) = WTV `ℕ M
WTV `ℕ (case L M N) = ⊥
WTV (A ⇒ B) (` x) = ⊥
WTV (A ⇒ B) (ƛ N) = ∀ {V : Term} → WTV A V → WTE B (N [ V ])
WTV (A ⇒ B) (L · M) = ⊥
WTV (A ⇒ B) `zero = ⊥
WTV (A ⇒ B) (`suc M) = ⊥
WTV (A ⇒ B) (case L M N) = ⊥
```

### Canonical forms

```
WTV⇒→ƛ : ∀{M : Term}{A B} → WTV (A ⇒ B) M → Σ[ N ∈ Term ] M ≡ ƛ N
WTV⇒→ƛ {ƛ N} {A} {B} wtv = ⟨ N , refl ⟩
WTV⇒→ƛ {L · M} {A} {B} ()
WTV⇒→ƛ {`zero} {A} {B} ()
WTV⇒→ƛ {`suc M} {A} {B} ()
WTV⇒→ƛ {case L M N} {A} {B} ()

data Natural : Term → Set where
   Nat-Z : Natural (`zero)
   Nat-S : ∀ {V} → Natural V → Natural (`suc V)

WTVℕ→Nat : ∀{M : Term} → WTV `ℕ M → Natural M
WTVℕ→Nat {ƛ N} ()
WTVℕ→Nat {L · M} ()
WTVℕ→Nat {`zero} wtv = Nat-Z
WTVℕ→Nat {`suc M} wtv = Nat-S (WTVℕ→Nat wtv)
WTVℕ→Nat {case L M N} ()
```

```
WTV→Value : ∀{A}{M : Term} → WTV A M → Value M
WTV→Value {`ℕ} {` x} ()
WTV→Value {`ℕ} {ƛ N} ()
WTV→Value {`ℕ} {L · M} ()
WTV→Value {`ℕ} {`zero} wtv = V-zero
WTV→Value {`ℕ} {`suc M} wtv = V-suc (WTV→Value {`ℕ} wtv)
WTV→Value {`ℕ} {case L M N} ()
WTV→Value {A ⇒ B} {` x} ()
WTV→Value {A ⇒ B} {ƛ N} wtv = V-ƛ
WTV→Value {A ⇒ B} {L · M} ()
WTV→Value {A ⇒ B} {`zero} ()
WTV→Value {A ⇒ B} {`suc M} ()
WTV→Value {A ⇒ B} {case L M N} ()
```

The WTV function implies the WTE relation.

```
WTV→WTE : ∀{A}{M : Term} → WTV A M → WTE A M
WTV→WTE {A}{M = M} wtv = ⟨ M , ⟨ M ∎ , ⟨ WTV→Value {A} wtv , wtv ⟩ ⟩ ⟩
```


### Compatibility lemmas about reduction

```
suc-compat : ∀{M M' : Term} → M —↠ M' → `suc M —↠ `suc M'
suc-compat (M ∎) = `suc M ∎
suc-compat (_—→⟨_⟩_ L {M}{M'} L→M M—↠M') =
  begin
    `suc L       —→⟨ ξ-suc L→M ⟩
    `suc M       —↠⟨ suc-compat M—↠M' ⟩
    `suc M'
  ∎
```

```
case-compat : ∀{L L' M N : Term} → L —↠ L' → (case L M N) —↠ (case L' M N)
case-compat {L}{L}{M}{N}(L ∎) = case L M N ∎
case-compat {L}{L''}{M}{N}(_—→⟨_⟩_ L {L'} L→L' L'→L'') =
  begin
    case L M N   —→⟨ ξ-case L→L' ⟩
    case L' M N  —↠⟨ case-compat L'→L'' ⟩
    case L'' M N
  ∎
```

```
app-compat : ∀{L L' M M' : Term}
           → L —↠ L' → Value L'
           → M —↠ M' → L · M —↠ L' · M'
app-compat {L}{L}{M}{M} (L ∎) vL (M ∎) = L · M ∎
app-compat {L}{L}{M}{M''} (L ∎) vL (_—→⟨_⟩_ M {M'} M→M' M'→M'') =
  begin
     L · M     —→⟨ ξ-·₂ vL M→M' ⟩
     L · M'    —↠⟨ app-compat (L ∎) vL M'→M'' ⟩
     L · M''
  ∎
app-compat {L}{L''}{M}{M'}(_—→⟨_⟩_ L {L'}{L''} L→L' L'→L'') vL' M→M' =
  begin
    L · M             —→⟨ ξ-·₁ L→L' ⟩
    L' · M            —↠⟨ app-compat L'→L'' vL' M→M' ⟩
    L'' · M'
  ∎
```

### A technical lemma about extending substitutions

```
nth-cons : ∀{V : Term}{A}{Γ}{σ}
         → WTV A V
         → (∀ {C : Type} (x : ℕ) → nth Γ x ≡ just C → WTV C (⟦ σ ⟧ x))
         → ∀ {C : Type} (x : ℕ) →
            nth (A ∷ Γ) x ≡ just C → WTV C (⟦ V • σ ⟧ x)
nth-cons {V} wtv ⊢σ {C} zero refl = wtv
nth-cons {V} wtv ⊢σ {C} (suc x) eq rewrite eq = ⊢σ x eq
```

### The fundemantal property of the logical relation

```
fundamental-property : ∀ {A}{Γ}{M : Term} {σ : Subst}
  → Γ ⊢ M ⦂ A
  → (∀ {A}(x : ℕ) → nth Γ x ≡ just A → WTV A (⟦ σ ⟧ x))
  → WTE A (⟪ σ ⟫ M)
fundamental-property {A}(⊢` {x = x} x∈Γ) ⊢σ = WTV→WTE {A} ( ⊢σ x x∈Γ)
fundamental-property {A ⇒ B}{Γ}{ƛ M}{σ}(⊢ƛ ⊢M) ⊢σ =
  ⟨ ƛ ( ⟪ exts σ ⟫ M) , ⟨ (ƛ (⟪ exts σ ⟫ M) ∎) , ⟨ V-ƛ , G ⟩ ⟩ ⟩
  where

  G : {V : Term} → WTV A V → WTE B (( ⟪ exts σ ⟫ M) [ V ])
  G {V} wtv
      with fundamental-property {B}{A ∷ Γ}{M}{V • σ} ⊢M (nth-cons wtv ⊢σ)
  ... | ⟨ N' , ⟨ N→N' , ⟨ vN' , wtvN' ⟩ ⟩ ⟩
      rewrite exts-sub-cons σ M V =
      ⟨ N' , ⟨ N→N' , ⟨ vN' , wtvN' ⟩ ⟩ ⟩

fundamental-property {B}{Γ}{L · M}{σ} (⊢· {A = A} ⊢L ⊢M) ⊢σ
    with fundamental-property {A ⇒ B}{M = L}{σ} ⊢L ⊢σ
... | ⟨ L' , ⟨ L→L' , ⟨ vL' , wtvL' ⟩ ⟩ ⟩
    with WTV⇒→ƛ {L'} wtvL'
... | ⟨ N , eq ⟩ rewrite eq
    with fundamental-property {M = M}{σ} ⊢M ⊢σ
... | ⟨ M' , ⟨ M→M' , ⟨ vM' , wtvM' ⟩ ⟩ ⟩
    with wtvL' {M'} wtvM'
... | ⟨ V , ⟨ →V , ⟨ vV , wtvV ⟩ ⟩ ⟩ =    
      let r1 = app-compat L→L' vL' M→M' in
      ⟨ V , ⟨ (—↠-trans r1 ((ƛ N) · M' —→⟨ β-ƛ vM' ⟩ →V)) , ⟨ vV , wtvV ⟩ ⟩ ⟩
fundamental-property ⊢zero ⊢σ = WTV→WTE {`ℕ} tt
fundamental-property (⊢suc ⊢M) ⊢σ 
    with fundamental-property ⊢M ⊢σ
... | ⟨ V , ⟨ M→V , ⟨ vV , wtv ⟩ ⟩ ⟩ = 
      ⟨ (`suc V) , ⟨ suc-compat M→V , ⟨ (V-suc vV) , wtv ⟩ ⟩ ⟩
fundamental-property {M = case L M N}{σ = σ} (⊢case ⊢L ⊢M ⊢N) ⊢σ
    with fundamental-property {`ℕ}{σ = σ} ⊢L ⊢σ
... | ⟨ L' , ⟨ L→L' , ⟨ vL , wtvL' ⟩ ⟩ ⟩
    with WTVℕ→Nat {L'} wtvL'
... | Nat-Z
    with fundamental-property {σ = σ} ⊢M ⊢σ
... | ⟨ M' , ⟨ M→M' , ⟨ vM , wtvM ⟩ ⟩ ⟩ =
      ⟨ M' , ⟨ R , ⟨ vM , wtvM ⟩ ⟩ ⟩
    where
    R : case (⟪ σ ⟫ L) (⟪ σ ⟫ M) (⟪ exts σ ⟫ N) —↠ M'
    R = begin
        (case (⟪ σ ⟫ L) (⟪ σ ⟫ M) (⟪ exts σ ⟫ N))    —↠⟨ case-compat L→L' ⟩
        (case `zero (⟪ σ ⟫ M) (⟪ exts σ ⟫ N))        —→⟨ β-zero ⟩
        ⟪ σ ⟫ M                                      —↠⟨ M→M' ⟩
        M'                                           ∎
fundamental-property {M = case L M N}{σ} (⊢case {Γ}{A = A} ⊢L ⊢M ⊢N) ⊢σ
    | ⟨ L' , ⟨ L→L' , ⟨ vL , wtvL' ⟩ ⟩ ⟩
    | Nat-S {V = V} n
    with fundamental-property {σ = V • σ} ⊢N (nth-cons wtvL' ⊢σ)
... | ⟨ N' , ⟨ N→N' , ⟨ vN , wtvN ⟩ ⟩ ⟩ =
      ⟨ N' , ⟨ R , ⟨ vN , wtvN ⟩ ⟩ ⟩
    where
    S : (⟪ exts σ ⟫ N [ V ]) —↠ ⟪ V • σ ⟫ N
    S rewrite exts-sub-cons σ N V = ⟪ V • σ ⟫ N ∎
    
    R : case (⟪ σ ⟫ L) (⟪ σ ⟫ M) (⟪ exts σ ⟫ N) —↠ N'
    R = begin
        (case (⟪ σ ⟫ L) (⟪ σ ⟫ M) (⟪ exts σ ⟫ N))  —↠⟨ case-compat L→L' ⟩
        (case (`suc V) (⟪ σ ⟫ M) (⟪ exts σ ⟫ N))   —→⟨ β-suc (WTV→Value {`ℕ} wtvL') ⟩
        ⟪ exts σ ⟫ N [ V ]                         —↠⟨ S ⟩
        ⟪ V • σ ⟫ N                                —↠⟨ N→N' ⟩
        N'                                         ∎
```

