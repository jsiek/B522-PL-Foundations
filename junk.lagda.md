```
module junk where
```

```
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
   renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; sym; cong; cong₂)
{-
open Relation.Binary.PropositionalEquality.≡-Reasoning
   using (begin_; _≡⟨_⟩_; _∎)
-}
open import Relation.Binary.PropositionalEquality using ()
open import STLC-Termination
```

```
ℛ : (A : Type) → Term → Term → Set
ℒ : (A : Type) → Term → Term → Set

ℛ A M₁ M₂ = Σ[ V₁ ∈ Term ] Σ[ V₂ ∈ Term ]
  (M₁ —↠ V₁) × (Value V₁) × (M₂ —↠ V₂) × (Value V₂) × (ℒ A V₁ V₂)

ℒ `ℕ `zero `zero = ⊤
ℒ `ℕ (`suc M₁) (`suc M₂) = ℒ `ℕ M₁ M₂
ℒ `ℕ _ _ = ⊥
ℒ (A ⇒ B) (ƛ N₁) (ƛ N₂) =
  ∀ {V₁ V₂ : Term} → ℒ A V₁ V₂ → ℛ B (N₁ [ V₁ ]) (N₂ [ V₂ ])
ℒ (A ⇒ B) _ _ = ⊥

ℒ→Value : ∀{A}{M₁ M₂ : Term} → ℒ A M₁ M₂ → Value M₁ × Value M₂
ℒ→Value {A ⇒ B} {ƛ N₁} {ƛ N₂} LM12 = ⟨ V-ƛ , V-ƛ ⟩
ℒ→Value {`ℕ} {`zero} {`zero} LM12 = ⟨ V-zero , V-zero ⟩
ℒ→Value {`ℕ} {`suc M₁} {`suc M₂} LM12 
    with ℒ→Value {`ℕ} {M₁} {M₂} LM12
... | ⟨ V₁ , V₂ ⟩ = ⟨ (V-suc V₁) , (V-suc V₂) ⟩

ℒ→ℛ : ∀{A}{M₁ M₂ : Term} → ℒ A M₁ M₂ → ℛ A M₁ M₂
ℒ→ℛ {A}{M₁}{M₂} LM12
    with ℒ→Value {A}{M₁}{M₂} LM12
... | ⟨ V₁ , V₂ ⟩ = 
    ⟨ M₁ , ⟨ M₂ , ⟨ M₁ ∎ , ⟨ V₁ , ⟨ (M₂ ∎) , ⟨ V₂ , LM12 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

ℒ⇒→ƛ : ∀{M₁ M₂ : Term}{A B} → ℒ (A ⇒ B) M₁ M₂
   → (Σ[ N₁ ∈ Term ] M₁ ≡ ƛ N₁) × (Σ[ N₂ ∈ Term ] M₂ ≡ ƛ N₂)
ℒ⇒→ƛ {ƛ N₁}{ƛ N₂} {A} {B} wtv = ⟨ ⟨ N₁ , refl ⟩ , ⟨ N₂ , refl ⟩ ⟩

_⊢_~_ : Context → Subst → Subst → Set
Γ ⊢ σ₁ ~ σ₂ = ∀ {C : Type} (x : ℕ) → nth Γ x ≡ just C
               → ℒ C (⟦ σ₁ ⟧ x) (⟦ σ₂ ⟧ x)

extend-sub2 : ∀{V₁ V₂ : Term}{A}{Γ}{σ₁ σ₂ : Subst}
         → ℒ A V₁ V₂   →   Γ ⊢ σ₁ ~ σ₂
         → (A ∷ Γ) ⊢ (V₁ • σ₁) ~ (V₂ • σ₂)
extend-sub2 {V₁}{V₂} wtv ⊢σ {C} zero refl = wtv
extend-sub2 {V₁}{V₂} wtv ⊢σ {C} (suc x) eq rewrite eq = ⊢σ x eq

_⊢_~_⦂_ : Context → Term → Term → Type → Set
Γ ⊢ M₁ ~ M₂ ⦂ A = ∀{σ₁ σ₂} → Γ ⊢ σ₁ ~ σ₂ → ℛ A (⟪ σ₁ ⟫ M₁) (⟪ σ₂ ⟫ M₂)

{-
  PFPL Theorem 47.13
-}

~-refl : ∀ {A}{Γ}{M : Term}
  → Γ ⊢ M ⦂ A
  → Γ ⊢ M ~ M ⦂ A
~-refl {A} {Γ} (⊢` {x = x} x∈Γ) Γ⊢σ =
  let ℒσx = Γ⊢σ x x∈Γ in
  ℒ→ℛ {A} ℒσx
~-refl {A ⇒ B} {Γ} {ƛ M} (⊢ƛ ⊢M) {σ₁}{σ₂} Γ⊢σ =
    ⟨ ⟪ σ₁ ⟫ (ƛ M) , ⟨ ⟪ σ₂ ⟫ (ƛ M) , ⟨ ƛ (⟪ exts σ₁ ⟫ M) ∎ , ⟨ V-ƛ ,
    ⟨ (ƛ (⟪ exts σ₂ ⟫ M) ∎) , ⟨ V-ƛ , G ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    where
    G : {V₁ V₂ : Term} →
        ℒ A V₁ V₂ → ℛ B (⟪ exts σ₁ ⟫ M [ V₁ ]) (⟪ exts σ₂ ⟫ M [ V₂ ])
    G {V₁}{V₂} ℒ12
        with ~-refl {B}{A ∷ Γ}{M} ⊢M {V₁ • σ₁}{V₂ • σ₂} (extend-sub2 ℒ12 Γ⊢σ)
    ... | ⟨ N₁ , ⟨ N₂ , ⟨ N→N'₁ , ⟨ vN'₁ , ⟨ N→N'₂ , ⟨ vN'₂ , ℒN'₁₂ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        rewrite exts-sub-cons σ₁ M V₁
        | exts-sub-cons σ₂ M V₂ =
        ⟨ N₁ , ⟨ N₂ , ⟨ N→N'₁ , ⟨ vN'₁ , ⟨ N→N'₂ , ⟨ vN'₂ , ℒN'₁₂ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
~-refl {B} {Γ}{L · M} (⊢· {A = A} ⊢L ⊢M) {σ₁}{σ₂} Γ⊢σ
    with ~-refl {A ⇒ B}{M = L} ⊢L {σ₁}{σ₂} Γ⊢σ
... | ⟨ L₁ , ⟨ L₂ , ⟨ L→L₁ , ⟨ vL₁ , ⟨ L→L₂ , ⟨ vL₂ , ℒL₁₂ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    with ℒ⇒→ƛ {L₁}{L₂} ℒL₁₂
... | ⟨ ⟨ N₁ , eq₁ ⟩  , ⟨ N₂ , eq₂ ⟩ ⟩
    rewrite eq₁ | eq₂ 
    with ~-refl {M = M} ⊢M {σ₁}{σ₂} Γ⊢σ
... | ⟨ M₁ , ⟨ M₂ , ⟨ M→M₁ , ⟨ vM₁ , ⟨ M→M₂ , ⟨ vM₂ , ℒM₁₂ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    with ℒL₁₂ {M₁}{M₂} ℒM₁₂
... | ⟨ V₁ , ⟨ V₂ , ⟨ →V₁ , ⟨ vV₁ , ⟨ →V₂ , ⟨ vV₂ , ℒV₁₂ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
      ⟨ V₁ , ⟨ V₂ , ⟨ R₁ , ⟨ vV₁ , ⟨ R₂ , ⟨ vV₂ , ℒV₁₂ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    where
    R₁ : ⟪ σ₁ ⟫ L · ⟪ σ₁ ⟫ M —↠ V₁
    R₁ = begin
         ⟪ σ₁ ⟫ L · ⟪ σ₁ ⟫ M     —↠⟨ app-compat L→L₁ vL₁ M→M₁ ⟩
         (ƛ N₁) · M₁            —→⟨ β-ƛ vM₁ ⟩
         N₁ [ M₁ ]              —↠⟨ →V₁ ⟩
         V₁                     ∎

    R₂ : ⟪ σ₂ ⟫ L · ⟪ σ₂ ⟫ M —↠ V₂
    R₂ = begin
         ⟪ σ₂ ⟫ L · ⟪ σ₂ ⟫ M     —↠⟨ app-compat L→L₂ vL₂ M→M₂ ⟩
         (ƛ N₂) · M₂            —→⟨ β-ƛ vM₂ ⟩
         N₂ [ M₂ ]              —↠⟨ →V₂ ⟩
         V₂                     ∎
~-refl {.`ℕ} {Γ} ⊢zero Γ⊢σ = ℒ→ℛ {`ℕ} tt
~-refl {.`ℕ} {Γ} (⊢suc ⊢M) Γ⊢σ = {!!}
~-refl {A} {Γ} (⊢case ⊢M ⊢M₁ ⊢M₂) Γ⊢σ = {!!}

determ : ∀{M}{V V'} → M —↠ V → Value V → M —↠ V' → Value V' → V ≡ V'
determ = {!!}

{-
  PFPL Lemma 47.9
-}

ℛ-sym : ∀{A}{M₁ M₂} → ℛ A M₁ M₂ → ℛ A M₂ M₁

ℒ-sym : ∀{A}{V₁ V₂} → ℒ A V₁ V₂ → ℒ A V₂ V₁

ℛ-sym {A} ⟨ V₁ , ⟨ V₂ , ⟨ →V₁ , ⟨ vV₁ , ⟨ →V₂ , ⟨ vV₂ , ℒ12 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ V₂ , ⟨ V₁ , ⟨ →V₂ , ⟨ vV₂ , ⟨ →V₁ , ⟨ vV₁ , (ℒ-sym {A} ℒ12) ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

ℒ-sym {A ⇒ B} {ƛ N₁}{ƛ N₂} ℒN12 {V₁}{V₂} ℒV12 
    with ℒN12 {V₂}{V₁} (ℒ-sym {A} ℒV12)
... | ℛN12
    with ℛN12 
... | ⟨ W₂ , ⟨ W₁ , ⟨ →W₂ , ⟨ vW₂ , ⟨ →W₁ , ⟨ vW₁ , ℒ21 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ⟨ W₁ , ⟨ W₂ , ⟨ →W₁ , ⟨ vW₁ , ⟨ →W₂ , ⟨ vW₂ , (ℒ-sym {B} ℒ21) ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

ℒ-sym {`ℕ} {`zero}{`zero} ℒ12 = tt
ℒ-sym {`ℕ} {`suc V₁}{`suc V₂} ℒ12 = ℒ-sym {`ℕ}{V₁}{V₂} ℒ12

ℛ-trans : ∀{A}{M₁ M₂ M₃} → ℛ A M₁ M₂ → ℛ A M₂ M₃ → ℛ A M₁ M₃

ℒ-trans : ∀{A}{V₁ V₂ V₃} → ℒ A V₁ V₂ → ℒ A V₂ V₃ → ℒ A V₁ V₃

ℛ-trans {A}
    ⟨ V₁ , ⟨ V₂ , ⟨ →V₁ , ⟨ vV₁ , ⟨ →V₂ , ⟨ vV₂ , ℒ12 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    ⟨ V₁' , ⟨ V₂' , ⟨ →V₁' , ⟨ vV₁' , ⟨ →V₂' , ⟨ vV₂' , ℒ23 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    rewrite determ →V₂ vV₂ →V₁' vV₁' =
      ⟨ V₁ , ⟨ V₂' , ⟨ →V₁ , ⟨ vV₁ , ⟨ →V₂' , ⟨ vV₂' , (ℒ-trans {A} ℒ12 ℒ23) ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

ℒ-trans {A ⇒ B}{ƛ N₁}{ƛ N₂}{ƛ N₃} L12 L23 {V₁}{V₃} ℒV13 =
  let ℛN12 = L12 {V₁}{V₃} ℒV13 in
  let ℛN23 = L23 {V₃}{V₃} (ℒ-trans {A} (ℒ-sym {A} ℒV13) ℒV13) in
  ℛ-trans {B} ℛN12 ℛN23
ℒ-trans {`ℕ} {`zero}{`zero}{`zero} L12 L23 = tt
ℒ-trans {`ℕ} {`suc V₁}{`suc V₂}{`suc V₃} L12 L23 = ℒ-trans {`ℕ} {V₁} L12 L23


```

