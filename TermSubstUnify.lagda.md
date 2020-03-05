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

module TermSubstUnify
    (Op : Set)
    (op-eq? : (x : Op) → (y : Op) → Dec (x ≡ y))
    (arity : Op → ℕ) where
```

## Definitions of terms, substitution, and unifies

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

data AST : Set where
  `_ : Var → AST
  _⦅_⦆ : (op : Op) → Vec AST (arity op) → AST

Equations : Set
Equations = List (AST × AST)
```

```
append-eqs : ∀{n} → Vec AST n → Vec AST n → Equations → Equations
append-eqs {zero} Ms Ls eqs = eqs
append-eqs {suc n} (M ∷ Ms) (L ∷ Ls) eqs = ⟨ M , L ⟩ ∷ append-eqs Ms Ls eqs
```

```
[_::=_]_ : Var → AST → ∀{n} → Vec AST n → Vec AST n

[_:=_]_ : Var → AST → AST → AST
[ x := M ] (` y)
    with x ≟ y
... | yes xy = M
... | no xy = ` y
[ x := M ] (op ⦅ Ns ⦆) = op ⦅ [ x ::= M ] Ns ⦆

[ x ::= M ] [] = []
[ x ::= M ] (N ∷ Ns) = [ x := M ] N ∷ [ x ::= M ] Ns

[_/_]_ : AST → Var → Equations → Equations
[ M / x ] [] = []
[ M / x ] (⟨ L , N ⟩ ∷ eqs) = ⟨ [ x := M ] L , [ x := M ] N ⟩ ∷ ([ M / x ] eqs)

lookup : Equations → Var → Maybe AST
lookup [] x = nothing
lookup (⟨ ` y , M ⟩ ∷ eqs) x
    with x ≟ y
... | yes xy = just M
... | no xy = lookup eqs x
lookup (⟨ op ⦅ Ms ⦆ , snd ⟩ ∷ eqs) x = lookup eqs x

subst-vec : Equations → ∀{n} → Vec AST n → Vec AST n

subst : Equations → AST → AST
subst σ (` x)
    with lookup σ x
... | nothing = ` x
... | just M = M 
subst σ (op ⦅ Ms ⦆) = op ⦅ subst-vec σ Ms ⦆

subst-vec σ {zero} Ms = []
subst-vec σ {suc n} (M ∷ Ms) = subst σ M ∷ subst-vec σ Ms
```

Definition of what it means to unify a list of equations.

```
_unifies_ : Equations → Equations → Set
θ unifies [] = ⊤
θ unifies (⟨ M , L ⟩ ∷ eqs) = subst θ M ≡ subst θ L  ×  θ unifies eqs
```

Definition of the variables in a term.

```
vars-vec : ∀{n} → Vec AST n → FiniteSet

vars : AST → FiniteSet
vars (` x) = ⁅ x ⁆
vars (op ⦅ Ms ⦆) = vars-vec Ms

vars-vec {zero} Ms = ∅
vars-vec {suc n} (M ∷ Ms) = vars M  ∪  vars-vec Ms

vars-eqs : Equations → FiniteSet
vars-eqs [] = ∅
vars-eqs (⟨ L , M ⟩ ∷ eqs) = vars L  ∪  vars M  ∪  vars-eqs eqs
```

Decision procedure for checking whether a variable occurs in a term.

```
occurs? : (x : Var) → (M : AST) → Dec (x ∈ vars M)
occurs-vec? : (x : Var) → ∀{n} → (Ms : Vec AST n) → Dec (x ∈ vars-vec Ms)

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
dom : Equations → FiniteSet
dom [] = ∅
dom (⟨ M , L ⟩ ∷ eqs) = vars M  ∪ dom eqs 
```

Definition of idempotent substitutions.

```
data IdemSubst : Equations → Set where
  empty : IdemSubst []
  insert : ∀{eqs}{x}{M}
     → x ∉ vars M
     → x ∉ vars-eqs eqs
     → vars M ∩ dom eqs ⊆ ∅
     → IdemSubst eqs
     → IdemSubst (⟨ ` x , M ⟩ ∷ eqs)
```

## Properites of terms

```
op≡-inversion : ∀{op op' Ms Ms'} → op ⦅ Ms ⦆ ≡ op' ⦅ Ms' ⦆ → op ≡ op'
op≡-inversion refl = refl

Ms≡-inversion : ∀{op Ms Ms'} → op ⦅ Ms ⦆ ≡ op ⦅ Ms' ⦆ → Ms ≡ Ms'
Ms≡-inversion refl = refl

∷≡-inversion : ∀{n}{x y : AST}{xs ys : Vec AST n}
   → _≡_ {a = Agda.Primitive.lzero}{A = Vec AST (suc n)} (x ∷ xs) (y ∷ ys)
   → x ≡ y  ×  xs ≡ ys
∷≡-inversion refl = ⟨ refl , refl ⟩
```

## Properties of substitution

Single substitution is the identity when the variable being
substituted does not occur in the term.

```
no-vars→subst-id : ∀{N x M}
  → ¬ x ∈ vars N
  → [ x := M ] N ≡ N
no-vars→subst-vec-id : ∀{n}{Ns : Vec AST n} {x M}
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
x∉domθ→no-lookup : ∀{θ}{x}
   → IdemSubst θ
   → x ∉ dom θ
   → lookup θ x ≡ nothing
x∉domθ→no-lookup {[]} {x} Sθ x∉θ = refl
x∉domθ→no-lookup {⟨ ` y , M ⟩ ∷ θ} {x} (insert y∉M y∉θ M∩θ⊆∅ Sθ) x∉θ
    with x ≟ y
... | yes refl = ⊥-elim (x∉θ (p⊆p∪q _ _ (x∈⁅x⁆ y)))
... | no x≠y =
    let IH = x∉domθ→no-lookup {θ}{x} Sθ λ x∈θ → x∉θ (q⊆p∪q _ _ x∈θ) in
    IH
```

```
x∉domθ→subst-id : ∀{θ}{x}
   → IdemSubst θ
   → x ∉ dom θ
   → subst θ (` x) ≡ ` x
x∉domθ→subst-id {θ}{x} Sθ x∉θ
    with lookup θ x | inspect (lookup θ) x
... | nothing | [ θx ] = refl
... | just M | [ θx ]
    rewrite x∉domθ→no-lookup Sθ x∉θ
    with θx
... | ()    
```

```
M∩domθ⊆∅→subst-id : ∀{M}{θ}
   → IdemSubst θ
   → vars M ∩ dom θ ⊆ ∅
   → subst θ M ≡ M
M∩domθ⊆∅→subst-vec-id : ∀{n}{Ms : Vec AST n}{θ}
   → IdemSubst θ
   → vars-vec Ms ∩ dom θ ⊆ ∅
   → subst-vec θ Ms ≡ Ms
   
M∩domθ⊆∅→subst-vec-id {zero} {[]} {θ} Sθ M∩domθ⊆∅ = refl
M∩domθ⊆∅→subst-vec-id {suc n} {M ∷ Ms} {θ} Sθ M∩domθ⊆∅
    rewrite ∪-distrib-∩ {vars M} {vars-vec Ms} {dom θ} =
    cong₂ _∷_ (M∩domθ⊆∅→subst-id Sθ Mθ⊆∅) (M∩domθ⊆∅→subst-vec-id {n}{Ms}{θ} Sθ Msθ⊆∅)
    where
    Mθ⊆∅ : vars M ∩ dom θ ⊆ ∅
    Mθ⊆∅ {x} x∈M∩domθ = M∩domθ⊆∅ {x} (p⊆p∪q _ _ {x} x∈M∩domθ)

    Msθ⊆∅ : vars-vec Ms ∩ dom θ ⊆ ∅
    Msθ⊆∅ {x} x∈Ms∩domθ = M∩domθ⊆∅ {x} (q⊆p∪q _ _ {x} x∈Ms∩domθ)

M∩domθ⊆∅→subst-id {` x} {θ} Sθ M∩domθ⊆∅ = x∉domθ→subst-id Sθ G
    where
    G : x ∉ dom θ
    G x∈domθ rewrite x∈p→⁅x⁆∩p≡⁅x⁆ x (dom θ) x∈domθ =
       let x∈∅ = M∩domθ⊆∅ {x} (x∈⁅x⁆ x) in
       ∉∅ {x} x∈∅
M∩domθ⊆∅→subst-id {op ⦅ Ms ⦆} {θ} Sθ M∩domθ⊆∅ =
    cong (λ □ → op ⦅ □ ⦆) (M∩domθ⊆∅→subst-vec-id {Ms = Ms} Sθ M∩domθ⊆∅)
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
vars-vec-subst-∪ : ∀{n}{Ns : Vec AST n}{x M}
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

## Unifies is reflexive

```
ext-subst : ∀{θ}{x}{M}{L}
   → x ∉ vars L
   → x ∉ vars-eqs θ
   → subst (⟨ ` x , M ⟩ ∷ θ) L ≡ subst θ L
ext-subst-vec : ∀{θ}{x}{M}{n}{Ls : Vec AST n}
   → x ∉ vars-vec Ls
   → x ∉ vars-eqs θ
   → subst-vec (⟨ ` x , M ⟩ ∷ θ) Ls ≡ subst-vec θ Ls

ext-subst {θ} {x} {M} {` y} x∉L x∉θ
    with x ≟ y
... | yes refl = ⊥-elim (x∉L (x∈⁅x⁆ x))
... | no xy = G
    where
    G : subst (⟨ ` x , M ⟩ ∷ θ) (` y)  ≡ subst θ (` y)
    G
        with y ≟ x
    ... | yes refl = ⊥-elim (xy refl)
    ... | no yx = refl
ext-subst {θ} {x} {M} {op ⦅ Ls ⦆} x∉L x∉θ = cong (λ □ → op ⦅ □ ⦆) (ext-subst-vec {θ}{x}{M}{Ls = Ls} x∉L x∉θ)

ext-subst-vec {θ} {x} {M} {zero} {Ls} x∉Ls x∉θ = refl
ext-subst-vec {θ} {x} {M} {suc n} {L ∷ Ls} x∉L∪Ls x∉θ =
    cong₂ _∷_ (ext-subst {θ}{x}{M}{L} (λ x∈L → x∉L∪Ls (p⊆p∪q (vars L) (vars-vec Ls) x∈L)) x∉θ)
              (ext-subst-vec {θ} {x} {M} {n} {Ls} (λ x∈Ls → x∉L∪Ls (q⊆p∪q (vars L) (vars-vec Ls) x∈Ls)) x∉θ)
```

```
no-vars→ext-unifies : ∀{θ}{x}{M}{eqs}
   → θ unifies eqs
   → x ∉ vars-eqs eqs
   → x ∉ vars-eqs θ
   → (⟨ ` x , M ⟩ ∷ θ) unifies eqs
no-vars→ext-unifies {θ} {x} {M} {[]} θeqs x∉eqs x∉θ = tt
no-vars→ext-unifies {θ} {x} {M} {⟨ L , N ⟩ ∷ eqs} ⟨ θL=θN , θeqs ⟩ x∉L∪N∪eqs x∉θ =
  let IH = no-vars→ext-unifies {θ} {x} {M} {eqs} θeqs x∉eqs x∉θ in
  ⟨ L=N , IH ⟩
    where
    x∉L : x ∉ vars L
    x∉L = λ x∈L → x∉L∪N∪eqs (p⊆p∪q (vars L) (vars N ∪ vars-eqs eqs) x∈L ) 
    x∉N : x ∉ vars N
    x∉N = λ x∈N →
        let x∈L∪N∪eqs = p⊆r→p⊆q∪r _ _ _ (p⊆p∪q _ _) x∈N in
        x∉L∪N∪eqs x∈L∪N∪eqs
    x∉eqs : x ∉ vars-eqs eqs
    x∉eqs = λ x∈eqs →
      let x∈L∪N∪eqs = p⊆r→p⊆q∪r _ _ _ (p⊆r→p⊆q∪r _ _ _ ⊆-refl) x∈eqs in
      x∉L∪N∪eqs x∈L∪N∪eqs
    L=N : subst (⟨ ` x , M ⟩ ∷ θ) L ≡ subst (⟨ ` x , M ⟩ ∷ θ) N
    L=N = begin
        subst (⟨ ` x , M ⟩ ∷ θ) L     ≡⟨ ext-subst {θ}{x}{M}{L} x∉L x∉θ ⟩
        subst θ L                     ≡⟨ θL=θN ⟩
        subst θ N                     ≡⟨ sym (ext-subst {θ}{x}{M}{N} x∉N x∉θ) ⟩
        subst (⟨ ` x , M ⟩ ∷ θ) N
        ∎

subst-var-eq : ∀{x}{M}{θ}
   → subst (⟨ ` x , M ⟩ ∷ θ) (` x) ≡ M
subst-var-eq {x}{M}{θ}
    with x ≟ x
... | yes refl = refl
... | no xx = ⊥-elim (xx refl)

unifies-refl : ∀{θ} → IdemSubst θ → θ unifies θ
unifies-refl {[]} empty = tt
unifies-refl {⟨ ` x , M ⟩ ∷ θ} (insert x∉M x∉θ M∩θ⊆∅ SΘ) =
    ⟨ G1 , G2 ⟩
    where
    IH : θ unifies θ
    IH = unifies-refl {θ} SΘ 
    H : vars M ∩ (⁅ x ⁆ ∪ dom θ) ⊆ ∅
    H {y} y∈
        rewrite ∪-distribˡ-∩ {vars M} {⁅ x ⁆} {dom θ}
        with (proj₁ (∈∪ _ _ _)) y∈
    ... | inj₁ y∈Mx
        with (proj₁ (∈∩ _ _ _)) y∈Mx
    ... | ⟨ y∈M , y∈x ⟩
        with x∈⁅y⁆→x≡y _ _ y∈x
    ... | refl = ⊥-elim (x∉M y∈M)
    H {y} y∈
        | inj₂ y∈M∩θ = M∩θ⊆∅ y∈M∩θ
    G1 : subst (⟨ ` x , M ⟩ ∷ θ) (` x) ≡ subst (⟨ ` x , M ⟩ ∷ θ) M
    G1 = begin
        subst (⟨ ` x , M ⟩ ∷ θ) (` x)     ≡⟨ subst-var-eq {x}{M}{θ} ⟩
        M                                 ≡⟨ sym (M∩domθ⊆∅→subst-id (insert x∉M x∉θ M∩θ⊆∅ SΘ) H) ⟩
        subst (⟨ ` x , M ⟩ ∷ θ) M
        ∎

    G2 : (⟨ ` x , M ⟩ ∷ θ) unifies θ
    G2 = no-vars→ext-unifies IH x∉θ x∉θ
```

## A failed occurs-check implies no solutions

```
num-ops-vec : ∀{n} → Vec AST n → ℕ

num-ops : AST → ℕ
num-ops (` x) = 0
num-ops (op ⦅ Ms ⦆) = suc (num-ops-vec Ms)

num-ops-vec {zero} Ms = 0
num-ops-vec {suc n} (M ∷ Ms) = num-ops M + num-ops-vec Ms

num-ops-eqs : Equations → ℕ
num-ops-eqs [] = 0
num-ops-eqs (⟨ L , M ⟩ ∷ eqs) = num-ops L + num-ops M + num-ops-eqs eqs

is-op : AST → Set
is-op (` x) = ⊥
is-op (op ⦅ Ms ⦆) = ⊤

num-ops-less-vec : ∀ {n}{Ms : Vec AST n}{x θ}
   → x ∈ vars-vec Ms
   → num-ops (subst θ (` x)) ≤ num-ops-vec (subst-vec θ Ms)

num-ops-less : ∀ {M}{x θ}
   → x ∈ vars M
   → is-op M
   → num-ops (subst θ (` x)) < num-ops (subst θ M)
num-ops-less {op ⦅ Ms ⦆}{x}{θ} x∈Ms opM =
   s≤s (num-ops-less-vec {Ms = Ms}{x}{θ} x∈Ms)

num-ops-less-vec {zero} {[]} {x} {θ} x∈Ms = ⊥-elim (∉∅ {x} x∈Ms)
num-ops-less-vec {suc n} {(` y) ∷ Ms} {x} {θ} x∈MMs
    with ∈p∪q→∈p⊎∈q x∈MMs
... | inj₁ x∈M
    with x ≟ y
... | yes refl = m≤m+n (num-ops (subst θ (` y))) (num-ops-vec (subst-vec θ Ms))
... | no xy = ⊥-elim ((x∉⁅y⁆ x y xy) x∈M)
num-ops-less-vec {suc n} {(` y) ∷ Ms} {x} {θ} x∈MMs
    | inj₂ x∈Ms =
    let IH = num-ops-less-vec {n} {Ms}{x}{θ} x∈Ms in
    begin≤
    num-ops (subst θ (` x))         ≤⟨ IH ⟩
    num-ops-vec (subst-vec θ Ms)    ≤⟨ m≤n+m _ _ ⟩
    num-ops (subst θ (` y)) + num-ops-vec (subst-vec θ Ms)
    QED
num-ops-less-vec {suc n} {(op ⦅ Ls ⦆) ∷ Ms} {x} {θ} x∈MMs
    with ∈p∪q→∈p⊎∈q x∈MMs
... | inj₁ x∈M =
    let θx<1+θLS = num-ops-less {(op ⦅ Ls ⦆)}{x}{θ} x∈M tt in
    begin≤
       num-ops (subst θ (` x))       ≤⟨ ≤-pred θx<1+θLS ⟩
       num-ops-vec (subst-vec θ Ls)  ≤⟨ m≤m+n _ _ ⟩
       num-ops-vec (subst-vec θ Ls) + num-ops-vec (subst-vec θ Ms) ≤⟨ n≤1+n _ ⟩
       suc (num-ops-vec (subst-vec θ Ls) + num-ops-vec (subst-vec θ Ms))
      QED
num-ops-less-vec {suc n} {M ∷ Ms} {x} {θ} x∈MMs
    | inj₂ x∈Ms =
    let IH = num-ops-less-vec {n} {Ms}{x}{θ} x∈Ms in
    begin≤
    num-ops (subst θ (` x))         ≤⟨ IH ⟩
    num-ops-vec (subst-vec θ Ms)    ≤⟨ m≤n+m _ _ ⟩
    num-ops (subst θ M) + num-ops-vec (subst-vec θ Ms)
    QED

occurs-no-soln : ∀{θ x M}
  → x ∈ vars M → is-op M
  → subst θ (` x) ≢ subst θ M
occurs-no-soln {θ} x∈M opM θxM
    with num-ops-less {θ = θ} x∈M opM
... | θx<θM rewrite θxM =
      ⊥-elim (1+n≰n θx<θM)
```

## Substitution preserves unifiers

```
subst-vec-sub1 : ∀{n}{Ns : Vec AST n}{z}{θ}{M}
  → subst θ (` z) ≡ subst θ M
  → subst-vec θ Ns ≡ subst-vec θ ([ z ::= M ] Ns)

subst-sub1 : ∀{N}{z}{θ}{M}
  → subst θ (` z) ≡ subst θ M
  → subst θ N ≡ subst θ ([ z := M ] N)
subst-sub1 {` x} {z} {θ} {M} θzM
    with z ≟ x
... | yes refl = θzM
... | no zx = refl
subst-sub1 {op ⦅ Ns ⦆} {z} {θ} {M} θzM =
    cong (λ □ → op ⦅ □ ⦆) (subst-vec-sub1 θzM)

subst-vec-sub1 {zero} {Ns} θzM = refl
subst-vec-sub1 {suc n} {N ∷ Ns}{z}{θ}{M} θzM
    rewrite subst-sub1 {N}{z}{θ}{M} θzM
    | subst-vec-sub1 {n} {Ns}{z}{θ}{M} θzM = refl
```

```
subst-sub : ∀{L}{N}{z}{θ}{M}
  → subst θ (` z) ≡ subst θ M
  → subst θ L ≡ subst θ N
  → subst θ ([ z := M ] L) ≡ subst θ ([ z := M ] N)
subst-sub {L}{N}{z}{θ}{M} θzM θLM =   begin
    subst θ ([ z := M ] L)    ≡⟨ sym (subst-sub1 {L} θzM) ⟩
    subst θ L                 ≡⟨ θLM ⟩
    subst θ N                 ≡⟨ subst-sub1 {N} θzM ⟩
    subst θ ([ z := M ] N)    ∎
```

```
subst-pres : ∀{eqs θ x M}
  → subst θ (` x) ≡ subst θ M
  → θ unifies eqs
  → θ unifies ([ M / x ] eqs)
subst-pres {[]} eq θeqs = tt
subst-pres {⟨ L , N ⟩ ∷ eqs} {θ}{x}{M} eq ⟨ θLM , θeqs ⟩ =
  ⟨ subst-sub {L = L}{N = N} eq θLM , (subst-pres {eqs} eq θeqs) ⟩
```

```
subst-vec-pres : ∀{n}{Ms Ls : Vec AST n}{eqs}{θ}
   → θ unifies eqs
   → subst-vec θ Ms ≡ subst-vec θ Ls
   → θ unifies append-eqs Ms Ls eqs
subst-vec-pres {zero} {Ms} {Ls} θeqs θMsLs = θeqs
subst-vec-pres {suc n} {M ∷ Ms} {L ∷ Ls} θeqs θMLMsLs
    with ∷≡-inversion θMLMsLs
... | ⟨ θML , θMsLs ⟩ = ⟨ θML , (subst-vec-pres θeqs θMsLs) ⟩
```

## Substitution reflects unifiers

```
subst-ref : ∀{L}{N}{z}{θ}{M}
  → subst θ (` z) ≡ subst θ M
  → subst θ ([ z := M ] L) ≡ subst θ ([ z := M ] N)
  → subst θ L ≡ subst θ N
subst-ref {L}{N}{z}{θ}{M} θzM θLM = begin
    subst θ L                ≡⟨ subst-sub1 {L} θzM ⟩
    subst θ ([ z := M ] L)   ≡⟨ θLM ⟩
    subst θ ([ z := M ] N)   ≡⟨ sym (subst-sub1 {N} θzM) ⟩
    subst θ N   ∎
```

```
subst-reflect : ∀{eqs θ x M}
  → θ unifies ([ M / x ] eqs)
  → subst θ (` x) ≡ subst θ M
  → θ unifies eqs
subst-reflect {[]} {θ} {x} {M} θ[M/x]eqs θx=θM = tt
subst-reflect {⟨ L , N ⟩ ∷ eqs} {θ} {x} {M} ⟨ θ[x:=M]L=θ[x:=M]N , θ[M/x]eqs ⟩ θx=θM =
    ⟨ subst-ref {L = L}{N} θx=θM θ[x:=M]L=θ[x:=M]N , subst-reflect {eqs}{θ}{x}{M} θ[M/x]eqs θx=θM ⟩
```

```
subst-vec-reflect : ∀{n}{Ms Ls : Vec AST n}{eqs}{θ}
   → θ unifies append-eqs Ms Ls eqs
   → (subst-vec θ Ms ≡ subst-vec θ Ls)  × θ unifies eqs
subst-vec-reflect {zero} {[]} {[]} {eqs} {θ} θMs,Ls,eqs = ⟨ refl , θMs,Ls,eqs ⟩
subst-vec-reflect {suc n} {M ∷ Ms} {L ∷ Ls} {eqs} {θ} ⟨ θM=θL , θMs,Ls,eqs ⟩ 
    with subst-vec-reflect {n} {Ms} {Ls} {eqs} {θ} θMs,Ls,eqs
... | ⟨ θMs=θLs , θeqs ⟩ =     
    ⟨ cong₂ _∷_ θM=θL θMs=θLs , θeqs ⟩
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
