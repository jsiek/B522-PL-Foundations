```
open import Agda.Primitive using (lzero)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; z≤n; s≤s; _<?_){- ; _≤′_; ≤′-refl; ≤′-step; _<′_)-}
open import Data.Nat.Properties
  using (m≤m+n; m≤n+m; ≤-step; ≤-pred; n≤1+n; 1+n≰n; ≤-refl; +-comm; +-assoc;
         +-mono-≤; ≤-reflexive; ≤∧≢⇒<) {-≤⇒≤′; ≤′⇒≤; ≤-trans)-}
open Data.Nat.Properties.≤-Reasoning
  using (_≤⟨_⟩_)
  renaming (begin_ to begin≤_; _∎ to _QED)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
   renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
   using (_≡_; _≢_; refl; sym; inspect; [_]; cong; cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning
   using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import FiniteSet

module FirstOrderTerms
    (Op : Set)
    (op-eq? : (x : Op) → (y : Op) → Dec (x ≡ y))
    (arity : Op → ℕ) where
```

## Definitions of terms and substitution

```
Var = ℕ

_≟_ : (x : ℕ) → (y : ℕ) → Dec (x ≡ y)
zero ≟ zero = yes refl
zero ≟ suc y = no (λ ())
suc x ≟ zero = no (λ ())
suc x ≟ suc y
    with x ≟ y
... | yes refl = yes refl
... | no xy = no λ {refl → xy refl}

data Term : Set where
  `_ : Var → Term
  _⦅_⦆ : (op : Op) → Vec Term (arity op) → Term
```

```
Substitution : Set
Substitution = List (Term × Term)
```

```
[_::=_]_ : Var → Term → ∀{n} → Vec Term n → Vec Term n

[_:=_]_ : Var → Term → Term → Term
[ x := M ] (` y)
    with x ≟ y
... | yes xy = M
... | no xy = ` y
[ x := M ] (op ⦅ Ns ⦆) = op ⦅ [ x ::= M ] Ns ⦆

[ x ::= M ] [] = []
[ x ::= M ] (N ∷ Ns) = [ x := M ] N ∷ [ x ::= M ] Ns

[_/_]_ : Term → Var → Substitution → Substitution
[ M / x ] [] = []
[ M / x ] (⟨ L , N ⟩ ∷ eqs) = ⟨ [ x := M ] L , [ x := M ] N ⟩ ∷ ([ M / x ] eqs)

lookup : Substitution → Var → Maybe Term
lookup [] x = nothing
lookup (⟨ ` y , M ⟩ ∷ eqs) x
    with x ≟ y
... | yes xy = just M
... | no xy = lookup eqs x
lookup (⟨ op ⦅ Ms ⦆ , snd ⟩ ∷ eqs) x = lookup eqs x

subst-vec : Substitution → ∀{n} → Vec Term n → Vec Term n

subst : Substitution → Term → Term
subst σ (` x)
    with lookup σ x
... | nothing = ` x
... | just M = M 
subst σ (op ⦅ Ms ⦆) = op ⦅ subst-vec σ Ms ⦆

subst-vec σ {zero} Ms = []
subst-vec σ {suc n} (M ∷ Ms) = subst σ M ∷ subst-vec σ Ms

sub-sub : Substitution → Substitution → Substitution
sub-sub θ [] = []
sub-sub θ (⟨ L , M ⟩ ∷ σ) = ⟨ L , subst θ M ⟩ ∷ sub-sub θ σ

_∘_ : Substitution → Substitution → Substitution
τ ∘ σ = sub-sub τ σ ++ τ
```

Definition of the variables in a term.

```
vars-vec : ∀{n} → Vec Term n → FiniteSet

vars : Term → FiniteSet
vars (` x) = ⁅ x ⁆
vars (op ⦅ Ms ⦆) = vars-vec Ms

vars-vec {zero} Ms = ∅
vars-vec {suc n} (M ∷ Ms) = vars M  ∪  vars-vec Ms

vars-eqs : Substitution → FiniteSet
vars-eqs [] = ∅
vars-eqs (⟨ L , M ⟩ ∷ eqs) = vars L  ∪  vars M  ∪  vars-eqs eqs
```

Decision procedure for checking whether a variable occurs in a term.

```
occurs? : (x : Var) → (M : Term) → Dec (x ∈ vars M)
occurs-vec? : (x : Var) → ∀{n} → (Ms : Vec Term n) → Dec (x ∈ vars-vec Ms)

occurs? x (` y)
    with x ≟ y
... | yes refl = yes (x∈⁅x⁆ x)
... | no xy = no (x∉⁅y⁆ x y xy)
occurs? x (op ⦅ Ms ⦆) = occurs-vec? x Ms
occurs-vec? x {zero} [] = no (∉∅ {x})
occurs-vec? x {suc n} (M ∷ Ms)
    with occurs? x M
... | yes x∈M = yes ((p⊆p∪q _ _) {x} x∈M)
... | no x∉M
    with occurs-vec? x Ms
... | yes x∈Ms = yes ((q⊆p∪q _ _) {x} x∈Ms)
... | no x∉Ms = no G
    where
    G : ¬ x ∈ vars M ∪ vars-vec Ms
    G x∈M∪Ms
        with ∈p∪q→∈p⊎∈q x∈M∪Ms
    ... | inj₁ x∈M = x∉M x∈M
    ... | inj₂ x∈Ms = x∉Ms x∈Ms
```

The domain of a list of equations are the variables on the left-hand
sides.

```
dom : Substitution → FiniteSet
dom [] = ∅
dom (⟨ M , L ⟩ ∷ eqs) = vars M  ∪ dom eqs 
```

Definition of idempotent substitutions.

```
data IdemSubst : Substitution → Set where
  empty : IdemSubst []
  insert : ∀{eqs}{x}{M}
     → x ∉ vars M  →  x ∉ vars-eqs eqs
     → vars M ∩ dom eqs ⊆ ∅  →  IdemSubst eqs
     → IdemSubst (⟨ ` x , M ⟩ ∷ eqs)
```

## Properites of terms

```
op≡-inversion : ∀{op op' Ms Ms'} → op ⦅ Ms ⦆ ≡ op' ⦅ Ms' ⦆ → op ≡ op'
op≡-inversion refl = refl

Ms≡-inversion : ∀{op Ms Ms'} → op ⦅ Ms ⦆ ≡ op ⦅ Ms' ⦆ → Ms ≡ Ms'
Ms≡-inversion refl = refl

∷≡-inversion : ∀{n}{x y : Term}{xs ys : Vec Term n}
   → _≡_ {a = Agda.Primitive.lzero}{A = Vec Term (suc n)} (x ∷ xs) (y ∷ ys)
   → x ≡ y  ×  xs ≡ ys
∷≡-inversion refl = ⟨ refl , refl ⟩
```

## Properties of substitution

The empty substitution is the identity function.

```
subst-empty : ∀ M → subst [] M ≡ M
subst-vec-empty : ∀ {n} (Ms : Vec Term n) → subst-vec [] Ms ≡ Ms
subst-empty (` x) = refl
subst-empty (op ⦅ Ms ⦆)
    rewrite subst-vec-empty Ms = refl
subst-vec-empty {.0} [] = refl
subst-vec-empty {.(suc _)} (M ∷ Ms)
    rewrite subst-empty M
    | subst-vec-empty Ms = refl
```

When the variable matches the variable in the first pair, the result
of substitution is the associated term.

```
subst-var-eq : ∀{x}{M}{σ}
   → subst (⟨ ` x , M ⟩ ∷ σ) (` x) ≡ M
subst-var-eq {x}{M}{σ}
    with x ≟ x
... | yes refl = refl
... | no xx = ⊥-elim (xx refl)
```

When the variable does not match the variable in the first pair, the
result is the rest of the substitution applied to the variable.

```
subst-var-neq : ∀{x}{y}{M}{σ}
   → x ≢ y
   → subst (⟨ ` x , M ⟩ ∷ σ) (` y) ≡ subst σ (` y)
subst-var-neq {x}{y}{M}{σ} x≢y
    with y ≟ x
... | yes refl = ⊥-elim (x≢y refl)
... | no yx = refl
```

Single substitution is the identity when the variable being
substituted does not occur in the term.

```
no-vars→subst-id : ∀{N x M}
  → ¬ x ∈ vars N
  → [ x := M ] N ≡ N
no-vars→subst-vec-id : ∀{n}{Ns : Vec Term n} {x M}
  → ¬ x ∈ vars-vec Ns
  → [ x ::= M ] Ns ≡ Ns
  
no-vars→subst-id {` y}{x} ¬x∈M
    with x ≟ y
... | yes refl = ⊥-elim (¬x∈M (x∈⁅x⁆ y))
... | no xy = refl
no-vars→subst-id {op ⦅ Ns ⦆} ¬x∈M =
    cong (λ □ → op ⦅ □ ⦆) (no-vars→subst-vec-id ¬x∈M)
no-vars→subst-vec-id {zero} {[]} ¬x∈M = refl
no-vars→subst-vec-id {suc n} {N ∷ Ns} {x}{M} ¬x∈M
    with occurs? x N | occurs-vec? x Ns
... | yes x∈N | _ =
      ⊥-elim (¬x∈M (p⊆p∪q (vars N) (vars-vec Ns) x∈N))
... | no x∉N | yes x∈Ns = ⊥-elim (¬x∈M ((q⊆p∪q (vars N) (vars-vec Ns) x∈Ns))) 
... | no x∉N | no x∉Ns
    rewrite no-vars→subst-id {N}{x}{M} x∉N
    | no-vars→subst-vec-id {n}{Ns}{x}{M} x∉Ns = refl
```

Simultaneous substitution is the identity when the domain of the
substitution has not variables in common with the term.
First we prove two lemmas to help with the variable case.

```
x∉domσ→no-lookup : ∀{σ}{x}
   → x ∉ dom σ
   → lookup σ x ≡ nothing
x∉domσ→no-lookup {[]} {x} x∉σ = refl
x∉domσ→no-lookup {⟨ ` y , M ⟩ ∷ σ} {x} x∉σ
    with x ≟ y
... | yes refl = ⊥-elim (x∉σ (p⊆p∪q _ _ (x∈⁅x⁆ y)))
... | no x≠y =
    x∉domσ→no-lookup {σ}{x} λ x∈σ → x∉σ (q⊆p∪q _ _ x∈σ)
x∉domσ→no-lookup {⟨ op ⦅ Ls ⦆ , M ⟩ ∷ σ} {x} x∉σ =
    x∉domσ→no-lookup {σ}{x} λ x∈σ → x∉σ (q⊆p∪q _ _ x∈σ)
```

```
x∉domσ→subst-id : ∀{σ}{x}
   → x ∉ dom σ
   → subst σ (` x) ≡ ` x
x∉domσ→subst-id {σ}{x} x∉σ
    with lookup σ x | inspect (lookup σ) x
... | nothing | [ σx ] = refl
... | just M | [ σx ]
    rewrite x∉domσ→no-lookup {σ} x∉σ
    with σx
... | ()    
```

```
M∩domσ⊆∅→subst-id : ∀{M}{σ}
   → vars M ∩ dom σ ⊆ ∅
   → subst σ M ≡ M
M∩domσ⊆∅→subst-vec-id : ∀{n}{Ms : Vec Term n}{σ}
   → vars-vec Ms ∩ dom σ ⊆ ∅
   → subst-vec σ Ms ≡ Ms
   
M∩domσ⊆∅→subst-vec-id {zero} {[]} {σ} M∩domσ⊆∅ = refl
M∩domσ⊆∅→subst-vec-id {suc n} {M ∷ Ms} {σ} M∩domσ⊆∅
    rewrite ∪-distrib-∩ {vars M} {vars-vec Ms} {dom σ} =
    cong₂ _∷_ (M∩domσ⊆∅→subst-id Mσ⊆∅) (M∩domσ⊆∅→subst-vec-id {n}{Ms}{σ} Msσ⊆∅)
    where
    Mσ⊆∅ : vars M ∩ dom σ ⊆ ∅
    Mσ⊆∅ {x} x∈M∩domσ = M∩domσ⊆∅ {x} (p⊆p∪q _ _ {x} x∈M∩domσ)

    Msσ⊆∅ : vars-vec Ms ∩ dom σ ⊆ ∅
    Msσ⊆∅ {x} x∈Ms∩domσ = M∩domσ⊆∅ {x} (q⊆p∪q _ _ {x} x∈Ms∩domσ)

M∩domσ⊆∅→subst-id {` x} {σ} M∩domσ⊆∅ = x∉domσ→subst-id {σ} G
    where
    G : x ∉ dom σ
    G x∈domσ rewrite x∈p→⁅x⁆∩p≡⁅x⁆ x (dom σ) x∈domσ =
       let x∈∅ = M∩domσ⊆∅ {x} (x∈⁅x⁆ x) in
       ∉∅ {x} x∈∅
M∩domσ⊆∅→subst-id {op ⦅ Ms ⦆} {σ} M∩domσ⊆∅ =
    cong (λ □ → op ⦅ □ ⦆) (M∩domσ⊆∅→subst-vec-id {Ms = Ms} M∩domσ⊆∅)
```

Special case for dom of a list of equations.

```
x∉p∪q→x∉p×x∉q : ∀ {p q x} → x ∉ p ∪ q → x ∉ p × x ∉ q
x∉p∪q→x∉p×x∉q {p}{q}{x} x∉pq = ⟨ x∉p , x∉q ⟩
    where
    x∉p : x ∉ p
    x∉p x∈p = x∉pq (p⊆p∪q _ _ x∈p)
    x∉q : x ∉ q
    x∉q x∈q = x∉pq (q⊆p∪q _ _ x∈q)

```

```
subst-dom : ∀{x}{M}{σ}
   → x ∉ dom σ
   → dom ([ M / x ] σ) ≡ dom σ
subst-dom {x} {M} {[]} x∉σ = refl
subst-dom {x} {M} {⟨ L , N ⟩ ∷ σ} x∉Lσ
    with x∉p∪q→x∉p×x∉q x∉Lσ
... | ⟨ x∉L , x∉σ ⟩
    rewrite no-vars→subst-id {L}{x}{M} x∉L
    | subst-dom {x} {M} {σ} x∉σ = refl
```

Substitution removes variables from terms.

```
vars-subst-∪ : ∀{N}{x M}
   → vars ([ x := M ] N) ⊆ vars M  ∪  (vars N - ⁅ x ⁆)
vars-vec-subst-∪ : ∀{n}{Ns : Vec Term n}{x M}
   → vars-vec ([ x ::= M ] Ns) ⊆ vars M  ∪  (vars-vec Ns - ⁅ x ⁆)
vars-subst-∪ {` y} {x} {M}
    with x ≟ y
... | yes refl =
    begin⊆
    vars M                   ⊆⟨ ∪-identityʳ₁ (vars M) ⟩
    vars M ∪ ∅               ⊆⟨ p⊆r→q⊆s→p∪q⊆r∪s ⊆-refl ∅⊆p ⟩
    vars M ∪ (⁅ y ⁆ - ⁅ y ⁆)
    ■
... | no xy =
    begin⊆
    ⁅ y ⁆                      ⊆⟨ q⊆p∪q (vars M) ⁅ y ⁆ ⟩
    vars M ∪ ⁅ y ⁆             ⊆⟨ p⊆r→q⊆s→p∪q⊆r∪s ⊆-refl (⊆-reflexive (sym (⁅y⁆-⁅x⁆≡⁅y⁆ xy) )) ⟩
    vars M ∪ (⁅ y ⁆ - ⁅ x ⁆)
    ■
vars-subst-∪ {op ⦅ Ns ⦆} {x} {M} = vars-vec-subst-∪ {Ns = Ns} 
vars-vec-subst-∪ {zero} {[]} {x} {M} = ∅⊆p
vars-vec-subst-∪ {suc n} {N ∷ Ns} {x} {M} =
    begin⊆
    vars ([ x := M ] N) ∪ vars-vec ([ x ::= M ] Ns)                 ⊆⟨ p⊆r→q⊆s→p∪q⊆r∪s (vars-subst-∪ {N}{x}{M}) (vars-vec-subst-∪ {Ns = Ns}{x}{M}) ⟩
    (vars M ∪ (vars N - ⁅ x ⁆)) ∪ (vars M ∪ (vars-vec Ns - ⁅ x ⁆))  ⊆⟨ ⊆-reflexive (∪-assoc _ _ _) ⟩
    vars M ∪ ((vars N - ⁅ x ⁆) ∪ (vars M ∪ (vars-vec Ns - ⁅ x ⁆)))  ⊆⟨ ⊆-reflexive (cong (λ □ → vars M ∪ □) (sym (∪-assoc _ _ _))) ⟩
    vars M ∪ (((vars N - ⁅ x ⁆) ∪ vars M) ∪ (vars-vec Ns - ⁅ x ⁆))  ⊆⟨ ⊆-reflexive (cong (λ □ → vars M ∪ (□ ∪ (vars-vec Ns - ⁅ x ⁆))) (∪-comm _ _)) ⟩
    vars M ∪ ((vars M ∪ (vars N - ⁅ x ⁆)) ∪ (vars-vec Ns - ⁅ x ⁆))  ⊆⟨ ⊆-reflexive (cong (λ □ → vars M ∪ □) (∪-assoc _ _ _)) ⟩
    vars M ∪ (vars M ∪ ((vars N - ⁅ x ⁆) ∪ (vars-vec Ns - ⁅ x ⁆)))  ⊆⟨ ⊆-reflexive (sym (∪-assoc _ _ _)) ⟩
    (vars M ∪ vars M) ∪ ((vars N - ⁅ x ⁆) ∪ (vars-vec Ns - ⁅ x ⁆))  ⊆⟨ p⊆r→q⊆s→p∪q⊆r∪s ⊆-refl (⊆-reflexive (distrib-∪- _ _ _)) ⟩
    (vars M ∪ vars M) ∪ ((vars N ∪ vars-vec Ns) - ⁅ x ⁆)            ⊆⟨ p⊆r→q⊆s→p∪q⊆r∪s (⊆-reflexive (∪-idem _)) ⊆-refl ⟩
    vars M ∪ ((vars N ∪ vars-vec Ns) - ⁅ x ⁆)                       ■

vars-eqs-subst-∪ : ∀{eqs}{x M}
   → vars-eqs ([ M / x ] eqs) ⊆ vars M  ∪ (vars-eqs eqs - ⁅ x ⁆)
vars-eqs-subst-∪ {[]} {x} {M} = ∅⊆p
vars-eqs-subst-∪ {⟨ L , N ⟩ ∷ eqs} {x} {M} =
    let IH = vars-eqs-subst-∪ {eqs} {x} {M} in
    begin⊆
    vars ([ x := M ] L) ∪ vars ([ x := M ] N) ∪ vars-eqs ([ M / x ] eqs)                            ⊆⟨ p⊆r→q⊆s→p∪q⊆r∪s (vars-subst-∪ {L}) (p⊆r→q⊆s→p∪q⊆r∪s (vars-subst-∪ {N}) IH) ⟩
    (vars M ∪ (vars L - ⁅ x ⁆)) ∪ (vars M ∪ (vars N - ⁅ x ⁆)) ∪ (vars M ∪ (vars-eqs eqs - ⁅ x ⁆))   ⊆⟨ ⊆-reflexive G ⟩
    vars M ∪ (vars L ∪ vars N ∪ vars-eqs eqs) - ⁅ x ⁆
    ■
    where
    L-x = (vars L - ⁅ x ⁆)
    N-x = (vars N - ⁅ x ⁆)
    eqs-x = (vars-eqs eqs - ⁅ x ⁆)
    G : (vars M ∪ (vars L - ⁅ x ⁆)) ∪ (vars M ∪ (vars N - ⁅ x ⁆)) ∪ (vars M ∪ eqs-x)
         ≡ vars M ∪ (vars L ∪ vars N ∪ vars-eqs eqs) - ⁅ x ⁆
    G rewrite ∪-assoc (vars M) L-x ((vars M ∪ N-x) ∪ (vars M ∪ eqs-x))
      | ∪-assoc (vars M) N-x (vars M ∪ eqs-x)
      | sym (∪-assoc L-x (vars M) (N-x ∪ vars M ∪ eqs-x))
      | ∪-comm L-x (vars M)
      | ∪-assoc (vars M) L-x (N-x ∪ vars M ∪ eqs-x)
      | sym (∪-assoc L-x N-x (vars M ∪ eqs-x))
      | sym (∪-assoc (L-x ∪ N-x) (vars M) eqs-x)
      | ∪-comm (L-x ∪ N-x) (vars M) 
      | ∪-assoc (vars M) (L-x ∪ N-x) eqs-x
      | sym (∪-assoc (vars M) (vars M) (vars M ∪ (L-x ∪ N-x) ∪ eqs-x))
      | distrib-∪- (vars L) (vars N) ⁅ x ⁆
      | distrib-∪- (vars L ∪ vars N) (vars-eqs eqs) ⁅ x ⁆
      | ∪-idem (vars M)
      | sym (∪-assoc (vars M) (vars M) (((vars L ∪ vars N) ∪ vars-eqs eqs) - ⁅ x ⁆))
      | ∪-idem (vars M)
      | ∪-assoc (vars L) (vars N) (vars-eqs eqs) = refl
```



## Substitution preserves idempotent substitutions

```
subst-pres-idem : ∀{x}{M}{σ}
   → IdemSubst σ
   → x ∉ dom σ
   → vars M ∩ dom σ ⊆ ∅
   → IdemSubst ([ M / x ] σ)
subst-pres-idem {x} {M} {[]} empty x∉σ M∩σ⊆∅ = empty
subst-pres-idem {x} {M} {(⟨ ` y , N ⟩ ∷ σ)} (insert y∉N y∉σ N∩domσ⊆∅ Sσ) x∉σ M∩σ⊆∅
    with x ≟ y
... | yes refl = ⊥-elim (x∉σ (p⊆p∪q _ _ (x∈⁅x⁆ y)))
... | no xy = insert G1 G2 G3 G4
    where
    G1 : y ∉ vars ([ x := M ] N)
    G1 y∈[x:=M]N 
        with proj₁ (∈∪ _ _ _) (vars-subst-∪ {N}{x}{M} y∈[x:=M]N)
    ... | inj₁ y∈M =
          let y∈M∩[y]∪σ = proj₂ (∈∩ _ _ _) ⟨ y∈M , p⊆p∪q _ (dom σ) (x∈⁅x⁆ y) ⟩ in
          ⊥-elim (∉∅ (M∩σ⊆∅ y∈M∩[y]∪σ))
    ... | inj₂ y∈N-x =
          let y∈N = p-q⊆p _ _ y∈N-x in
          ⊥-elim (y∉N y∈N)
    G5 : vars M ∩ dom σ ⊆ ∅
    G5 {z} z∈
        with proj₁ (∈∩ _ _ _) z∈
    ... | ⟨ z∈M , z∈σ ⟩ =
        M∩σ⊆∅ {z} (proj₂ (∈∩ _ _ _) ⟨ z∈M , (q⊆p∪q _ _ z∈σ) ⟩)
    G2 : y ∉ vars-eqs ([ M / x ] σ)
    G2 y∈[M/x]σ 
        with proj₁ (∈∪ _ _ _) (vars-eqs-subst-∪ {σ}{x}{M} y∈[M/x]σ)
    ... | inj₁ y∈M = ∉∅ (M∩σ⊆∅ {y} (proj₂ (∈∩ _ _ _) ⟨ y∈M , (p⊆p∪q _ _ (x∈⁅x⁆ y)) ⟩))
    ... | inj₂ y∈σ-[x] = ⊥-elim (y∉σ (p-q⊆p _ _ y∈σ-[x]))

    G3 : vars ([ x := M ] N) ∩ dom ([ M / x ] σ) ⊆ ∅
    G3 = begin⊆
         vars ([ x := M ] N) ∩ dom ([ M / x ] σ)  ⊆⟨ p⊆r→q⊆s→p∩q⊆r∩s (vars-subst-∪ {N}{x}{M}) (⊆-reflexive (subst-dom{x}{M}{σ} λ x∈σ → (x∉σ (q⊆p∪q _ _ x∈σ)))) ⟩
         (vars M ∪ (vars N - ⁅ x ⁆)) ∩ dom σ      ⊆⟨ p⊆r→q⊆s→p∩q⊆r∩s (p⊆r→q⊆s→p∪q⊆r∪s ⊆-refl (p-q⊆p _ _)) ⊆-refl ⟩
         (vars M ∪ vars N) ∩ dom σ                ⊆⟨ ⊆-reflexive ∪-distrib-∩ ⟩
         (vars M ∩ dom σ) ∪ (vars N ∩ dom σ)      ⊆⟨ p⊆r→q⊆s→p∪q⊆r∪s G5 N∩domσ⊆∅ ⟩
         ∅ ∪ ∅                                    ⊆⟨ ⊆-reflexive (∅∪p≡p _) ⟩
         ∅
         ■
      
    G4 : IdemSubst ([ M / x ] σ)
    G4 = subst-pres-idem {x} {M}{σ} Sσ (λ x∈σ → x∉σ (q⊆p∪q _ _ x∈σ)) G5
```

```
M∩domσ⊆∅ : ∀{x}{M}{σ}{eqs}
   → IdemSubst σ
   → (⁅ x ⁆ ∪ vars M ∪ vars-eqs eqs) ∩ dom σ ⊆ ∅
   → vars M ∩ dom ([ M / x ] σ) ⊆ ∅
M∩domσ⊆∅ {x} {M} {[]} {eqs} empty sub {y} y∈
    with proj₁ (∈∩ y _ _) y∈
... | ⟨ y∈M , y∈∅ ⟩ = y∈∅ 
M∩domσ⊆∅ {x} {M} {(⟨ ` y , N ⟩ ∷ σ)} {eqs} (insert x₁ x₂ x₃ Sσ) sub =
    G
    where
    sub' : (⁅ x ⁆ ∪ vars M ∪ vars-eqs eqs) ∩ dom σ ⊆ ∅
    sub' {y} y∈
        with proj₁ (∈∩ y _ _) y∈
    ... | ⟨ y∈[x]Meqs , y∈domσ ⟩ = sub {y} (proj₂ (∈∩ y _ _) ⟨ y∈[x]Meqs , (p⊆r→p⊆q∪r _ _ _ ⊆-refl y∈domσ) ⟩)
    
    IH : vars M ∩ dom ([ M / x ] σ) ⊆ ∅
    IH = M∩domσ⊆∅ {x} {M} {σ} {eqs} Sσ sub'
    x≢y : x ≢ y
    x≢y refl rewrite ∪-distrib-∩ {⁅ y ⁆} {vars M ∪ vars-eqs eqs} {⁅ y ⁆ ∪ dom σ} =
        ∉∅ (sub {y} K)
        where
        K : y ∈ (⁅ y ⁆ ∩ (⁅ y ⁆ ∪ dom σ)) ∪ ((vars M ∪ vars-eqs eqs) ∩ (⁅ y ⁆ ∪ dom σ))
        K = p⊆p∪q _ _ (proj₂ (∈∩ y _ _) ⟨ (x∈⁅x⁆ y) , (p⊆p∪q _ _ (x∈⁅x⁆ y)) ⟩)

    x∉domσ : x ∉ dom σ
    x∉domσ x∈domσ = ∉∅ (sub {x} J)
        where
        J : x ∈ (⁅ x ⁆ ∪ vars M ∪ vars-eqs eqs) ∩ (⁅ y ⁆ ∪ dom σ)
        J = proj₂ (∈∩ x _ _ ) ⟨ (p⊆p∪q _ _ (x∈⁅x⁆ x)) , (q⊆p∪q _ _ x∈domσ) ⟩
    H : vars M ∩ (⁅ y ⁆ ∪ dom ([ M / x ] σ)) ⊆ ∅
    H {z} z∈
        with proj₁ (∈∩ z _ _) z∈
    ... | ⟨ z∈M , z∈[y]∪domσ ⟩
        rewrite subst-dom{x}{M}{σ} x∉domσ =
        sub {z} ((proj₂ (∈∩ z _ _) ⟨ (p⊆r→p⊆q∪r _ _ _ ⊆-refl (p⊆q→p⊆q∪r _ _ _ ⊆-refl z∈M)) ,
                                     z∈[y]∪domσ ⟩))
    G : vars M ∩ dom ([ M / x ] (⟨ ` y , N ⟩ ∷ σ)) ⊆ ∅
    G
        with x ≟ y
    ... | yes refl = ⊥-elim (x≢y refl)
    ... | no xy = H

```

```
insert-subst : ∀{x}{M}{σ}{eqs}
   → x ∉ vars M
   → (⁅ x ⁆ ∪ vars M ∪ vars-eqs eqs) ∩ dom σ ⊆ ∅
   → IdemSubst σ
   → IdemSubst (⟨ ` x , M ⟩ ∷ ([ M / x ] σ))
insert-subst {x}{M}{σ}{eqs} x∉M eqs∩domσ⊆∅ Sσ =
    insert x∉M K (M∩domσ⊆∅ {x}{M}{σ}{eqs} Sσ eqs∩domσ⊆∅)
        (subst-pres-idem Sσ H G)
    where
    K : x ∉ vars-eqs ([ M / x ] σ)
    K x∈[M/x]σ
        with proj₁ (∈∪ _ _ _) (vars-eqs-subst-∪ {σ}{x}{M} x∈[M/x]σ)
    ... | inj₁ x∈M = x∉M x∈M
    ... | inj₂ x∈σ-x = x∉p-⁅x⁆ _ _ x∈σ-x
    
    H : x ∉ dom σ
    H x∈domσ =
       let x∈∅ = eqs∩domσ⊆∅ {x} (proj₂ (∈∩ _ _ _) ⟨ (p⊆p∪q _ _ (x∈⁅x⁆ x)) , x∈domσ ⟩) in
       ∉∅ x∈∅
    G : vars M ∩ dom σ ⊆ ∅
    G {y} y∈
        with proj₁ (∈∩ _ _ _) y∈
    ... | ⟨ y∈M , y∈domσ ⟩ =
        eqs∩domσ⊆∅ {y} (proj₂ (∈∩ _ _ _) ⟨ (q⊆p∪q _ _ (p⊆p∪q _ _ y∈M) ) , y∈domσ ⟩)
```

## Composition of substitutions

```
subst-compose-var : ∀ σ' σ α
   → subst (σ' ∘ σ) (` α) ≡ subst σ' (subst σ (` α))
subst-compose-var σ' [] α = refl
subst-compose-var σ' (⟨ A , B ⟩ ∷ σ) α = G A
    where
    IH : subst (σ' ∘ σ) (` α) ≡ subst σ' (subst σ (` α))
    IH = subst-compose-var σ' σ α
    G : ∀ A → subst (σ' ∘ (⟨ A , B ⟩ ∷ σ)) (` α)
            ≡ subst σ' (subst (⟨ A , B ⟩ ∷ σ) (` α))
    G (` β)
        with α ≟ β
    ... | yes refl = refl
    G (` β) | no α≠β = IH
    G (op ⦅ Ts ⦆) = IH
```

```
subst-compose : ∀ σ σ' A
   → subst (σ' ∘ σ) A ≡ subst σ' (subst σ A)
subst-vec-compose : ∀ σ σ' {n} (As : Vec Term n)
   → subst-vec (σ' ∘ σ) As ≡ subst-vec σ' (subst-vec σ As)
subst-compose σ σ' (` α) = subst-compose-var σ' σ α
subst-compose σ σ' (op ⦅ Ts ⦆)
    rewrite subst-vec-compose σ σ' Ts = refl
subst-vec-compose σ σ' {zero} [] = refl
subst-vec-compose σ σ' {suc n} (T ∷ Ts)
    rewrite subst-compose σ σ' T 
    | subst-vec-compose σ σ' {n} Ts = refl
```
