```
module lecture-notes-DeBruijn where
```

# STLC using de Bruijn representation of variables

## Imports

```
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product
  using (_×_; proj₁; proj₂; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
```

## Syntax

```
infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_

infix  5 ƛ_
infixl 7 _·_
infix  8 `suc_
infix  9 `_
infix  9 S_
```

## Types

```
data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type
```

## Contexts

```
data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context
```

## Variables

```
data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
      ---------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → Γ , B ∋ A
```

## Intrinsically Typed Terms

```
data _⊢_ : Context → Type → Set where

  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  ƛ_  : ∀ {Γ A B}
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B

  `zero : ∀ {Γ}
      ---------
    → Γ ⊢ `ℕ

  `suc_ : ∀ {Γ}
    → Γ ⊢ `ℕ
      ------
    → Γ ⊢ `ℕ

  case : ∀ {Γ A}
    → Γ ⊢ `ℕ
    → Γ ⊢ A
    → Γ , `ℕ ⊢ A
      ----------
    → Γ ⊢ A
```

## Renaming

```
ext : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ∋ A)
    ---------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)
```

```
rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x)          =  ` (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
rename ρ (`zero)        =  `zero
rename ρ (`suc M)       =  `suc (rename ρ M)
rename ρ (case L M N)   =  case (rename ρ L) (rename ρ M) (rename (ext ρ) N)
```

## Simultaneous Substitution


```
exts : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ⊢ A)
    ---------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)
```

```
subst : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst σ (` k)          =  σ k
subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)
subst σ (`zero)        =  `zero
subst σ (`suc M)       =  `suc (subst σ M)
subst σ (case L M N)   =  case (subst σ L) (subst σ M) (subst (exts σ) N)
```

## Single substitution

```
_[_] : ∀ {Γ A B}
        → Γ , B ⊢ A
        → Γ ⊢ B
          ---------
        → Γ ⊢ A
_[_] {Γ} {A} {B} N M =  subst {Γ , B} {Γ} σ {A} N
  where
  σ : ∀ {A} → Γ , B ∋ A → Γ ⊢ A
  σ Z      =  M
  σ (S x)  =  ` x
```

## Values

```
data Value : ∀ {Γ A} → Γ ⊢ A → Set where

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ N)

  V-zero : ∀ {Γ}
      -----------------
    → Value (`zero {Γ})

  V-suc : ∀ {Γ} {V : Γ ⊢ `ℕ}
    → Value V
      --------------
    → Value (`suc V)
```

## Reduction


```
infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      ---------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      ---------------
    → V · M —→ V · M′

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
      --------------------
    → (ƛ N) · W —→ N [ W ]

  ξ-suc : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
    → M —→ M′
      -----------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {Γ A} {L L′ : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → L —→ L′
      -------------------------
    → case L M N —→ case L′ M N

  β-zero :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
      -------------------
    → case `zero M N —→ M

  β-suc : ∀ {Γ A} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → Value V
      ----------------------------
    → case (`suc V) M N —→ N [ V ]
```

## Multi-step reduction

```
infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : ∀ {Γ A} (M : Γ ⊢ A)
      ------
    → M —↠ M

  _—→⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L —→ M
    → M —↠ N
      ------
    → L —↠ N

begin_ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N
```

```
—↠-trans : ∀{Γ}{A}{M N L : Γ ⊢ A} → M —↠ N → N —↠ L → M —↠ L
—↠-trans (M ∎) N—↠L = N—↠L
—↠-trans (L —→⟨ red ⟩ M—↠N) N—↠L =
  let IH = —↠-trans M—↠N N—↠L in
  L —→⟨ red ⟩ IH
```

## Termination via Logical Relations

```
WTE : (A : Type) → (∅ ⊢ A) → Set
WTV : (A : Type) → (∅ ⊢ A) → Set

WTE A M = Σ[ V ∈ ∅ ⊢ A ] (M —↠ V) × (Value V) × (WTV A V)

WTV `ℕ (` x) = ⊥
WTV `ℕ (L · M) = ⊥
WTV `ℕ `zero = ⊤
WTV `ℕ (`suc M) = WTV `ℕ M
WTV `ℕ (case L M N) = ⊥
WTV (A ⇒ B) (` x) = ⊥
WTV (A ⇒ B) (ƛ N) = ∀ {V : ∅ ⊢ A} → WTV A V → WTE B (N [ V ])
WTV (A ⇒ B) (L · M) = ⊥
WTV (A ⇒ B) (case L M N) = ⊥
```

```
WTV→Value : ∀{A}{M : ∅ ⊢ A} → WTV A M → Value M
WTV→Value {.(_ ⇒ _)} {ƛ M} wtv = V-ƛ
WTV→Value {A ⇒ A₁} {M · M₁} ()
WTV→Value {`ℕ} {M · M₁} ()
WTV→Value {.`ℕ} {`zero} wtv = V-zero
WTV→Value {.`ℕ} {`suc M} wtv =
  let IH = WTV→Value {`ℕ} {M} wtv in 
  V-suc IH
WTV→Value {A ⇒ A₁} {case M M₁ M₂} ()
WTV→Value {`ℕ} {case M M₁ M₂} ()

WTV→WTE : ∀{A}{M : ∅ ⊢ A} → WTV A M → WTE A M
WTV→WTE {M = M} wtv = ⟨ M , ⟨ M ∎ , ⟨ WTV→Value wtv , wtv ⟩ ⟩ ⟩
```

```
suc-compat : ∀{Γ}{M M' : Γ ⊢ `ℕ} → M —↠ M' → `suc M —↠ `suc M'
suc-compat = {!!}
```

```
case-compat : ∀{Γ}{L L' : Γ ⊢ `ℕ}{M}{N} → L —↠ L' → (case L M N) —↠ (case L' M N)
case-compat = {!!}
```

```
app-compat : ∀{Γ}{A B}{L L' : Γ ⊢ A ⇒ B}{M M' : Γ ⊢ A}
           → L —↠ L' → M —↠ M' → L · M —↠ L' · M'
app-compat = {!!}
```

```
fundamental-property : ∀ {Γ}{A}{M : Γ ⊢ A} {σ : ∀{A} → Γ ∋ A → ∅ ⊢ A}
  → (∀ {A}(x : Γ ∋ A) → WTV A (σ x))
  → WTE A (subst σ M)
fundamental-property {M = ` x}{σ} ⊢σ = WTV→WTE (⊢σ x)
fundamental-property {Γ}{A ⇒ B}{M = ƛ M}{σ} ⊢σ =
  ⟨ ƛ (subst (exts σ) M) , ⟨ (ƛ subst (exts σ) M ∎) , ⟨ V-ƛ , G ⟩ ⟩ ⟩
  where
  G : {V : ∅ ⊢ A} → WTV A V → WTE B ((subst (exts σ) M) [ V ])
  G {V} wtv = {!!}
  
fundamental-property {M = L · M}{σ} ⊢σ
    with fundamental-property {M = L}{σ} ⊢σ
... | ⟨ ƛ N , ⟨ L→L' , ⟨ vL' , wtvL' ⟩ ⟩ ⟩ 
    with fundamental-property {M = M}{σ} ⊢σ
... | ⟨ M' , ⟨ M→M' , ⟨ vM' , wtvM' ⟩ ⟩ ⟩
    with wtvL' {M'} wtvM'
... | ⟨ V , ⟨ →V , ⟨ vV , wtvV ⟩ ⟩ ⟩ =    
      let r1 = app-compat L→L' M→M' in
      ⟨ V , ⟨ (—↠-trans r1 ((ƛ N) · M' —→⟨ β-ƛ vM' ⟩ →V)) , ⟨ vV , wtvV ⟩ ⟩ ⟩

fundamental-property {M = `zero} ⊢σ = ⟨ `zero , ⟨ (`zero ∎) , ⟨ V-zero , tt ⟩ ⟩ ⟩
fundamental-property {M = `suc M}{σ} ⊢σ 
    with fundamental-property {M = M}{σ} ⊢σ
... | ⟨ V , ⟨ M→V , ⟨ vV , wtv ⟩ ⟩ ⟩ = 
      ⟨ (`suc V) , ⟨ suc-compat M→V , ⟨ (V-suc vV) , wtv ⟩ ⟩ ⟩
fundamental-property {M = case L M N}{σ} ⊢σ
    with fundamental-property {M = L}{σ} ⊢σ
... | ⟨ `zero , ⟨ M→V , ⟨ vV , wtv ⟩ ⟩ ⟩ =
      ⟨ {!!} , ⟨ {!!} , {!!} ⟩ ⟩
... | ⟨ `suc M' , ⟨ M→V , ⟨ vV , wtv ⟩ ⟩ ⟩ =  {!!}

```