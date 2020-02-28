```
open import Agda.Primitive using (lzero)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_; length)
{-
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.DecPropositional using (_∈?_)
-}
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; z≤n; s≤s; _<?_)
open import Data.Nat.Properties
  using (m≤m+n; m≤n+m; ≤-step; ≤-pred; n≤1+n; 1+n≰n; ≤-refl; +-comm; +-mono-≤; ≤-reflexive)
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
   using (_≡_; _≢_; refl; sym; inspect; [_]; cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning
   using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import FiniteSet

module UnifyMM
    (Op : Set)
    (op-eq? : (x : Op) → (y : Op) → Dec (x ≡ y))
    (arity : Op → ℕ) where
```

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

```
append-eqs : ∀{n} → Vec AST n → Vec AST n → Equations → Equations
append-eqs {zero} Ms Ls eqs = eqs
append-eqs {suc n} (M ∷ Ms) (L ∷ Ls) eqs = ⟨ M , L ⟩ ∷ append-eqs Ms Ls eqs
```

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

```
occurs-vec : Var → ∀{n} → Vec AST n → Set
occurs : Var → AST → Set
occurs x M = x ∈ vars M
occurs-vec x {n} Ms = x ∈ vars-vec Ms

occurs-eqs : Var → Equations → Set
occurs-eqs x [] = ⊥
occurs-eqs x (⟨ M , L ⟩ ∷ eqs) = occurs x M  ⊎  occurs x L  ⊎  occurs-eqs x eqs 
```

```
occurs-vec? : (x : Var) → ∀{n} → (Ms : Vec AST n) → Dec (occurs-vec x Ms)

occurs? : (x : Var) → (M : AST) → Dec (occurs x M)
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

```
data State : Set where
  middle : Equations → Equations → State
  done : Equations → State
  error : State
```


Martelli and Montanari's Algorithm 1.

```
step : Equations → Equations → State
step [] σ = done σ
step (⟨ ` x , ` y ⟩ ∷ eqs) σ
    with x ≟ y
... | yes xy = middle eqs σ
... | no xy = middle ([ ` y / x ] eqs) (⟨ ` x , ` y ⟩ ∷ [ ` y / x ] σ)
step (⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ eqs) σ
    with occurs? x (op ⦅ Ms ⦆)
... | yes x∈M = error
... | no x∉M =
    middle ([ op ⦅ Ms ⦆ / x ] eqs) (⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ [ op ⦅ Ms ⦆ / x ] σ)
step (⟨ op ⦅ Ms ⦆ , ` x ⟩ ∷ eqs) σ
    with occurs? x (op ⦅ Ms ⦆)
... | yes x∈M = error
... | no x∉M =
    middle ([ op ⦅ Ms ⦆ / x ] eqs) (⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ [ op ⦅ Ms ⦆ / x ] σ)
step (⟨ op ⦅ Ms ⦆ , op' ⦅ Ls ⦆ ⟩ ∷ eqs) σ
    with op-eq? op op'
... | yes refl = middle (append-eqs Ms Ls eqs) σ
... | no neq = error
```

```
_unifies-eqs_ : Equations → Equations → Set
θ unifies-eqs [] = ⊤
θ unifies-eqs (⟨ M , L ⟩ ∷ eqs) = subst θ M ≡ subst θ L  ×  θ unifies-eqs eqs

_unifies_ : Equations → State → Set
θ unifies middle eqs σ = θ unifies-eqs eqs × θ unifies-eqs σ
θ unifies done σ = θ unifies-eqs σ
θ unifies error = ⊥
```

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
   → occurs-vec x Ms
   → num-ops (subst θ (` x)) ≤ num-ops-vec (subst-vec θ Ms)

num-ops-less : ∀ {M}{x θ}
   → occurs x M
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
  → occurs x M → is-op M
  → subst θ (` x) ≢ subst θ M
occurs-no-soln {θ} x∈M opM θxM
    with num-ops-less {θ = θ} x∈M opM
... | θx<θM rewrite θxM =
      ⊥-elim (1+n≰n θx<θM)

soln-no-occurs : ∀{θ x M}
   → subst θ (` x) ≡ subst θ M
   → is-op M
   → ¬ (occurs x M)
soln-no-occurs θxM opM x∈M = occurs-no-soln x∈M opM θxM

subst-vec-id-no-occurs : ∀{n}{Ns : Vec AST n} {x M}
  → ¬ occurs-vec x Ns
  → [ x ::= M ] Ns ≡ Ns
  
subst-id-no-occurs : ∀{N x M}
  → ¬ occurs x N
  → [ x := M ] N ≡ N
subst-id-no-occurs {` y}{x} ¬x∈M
    with x ≟ y
... | yes refl = ⊥-elim (¬x∈M (x∈⁅x⁆ y))
... | no xy = refl
subst-id-no-occurs {op ⦅ Ns ⦆} ¬x∈M =
    cong (λ □ → op ⦅ □ ⦆) (subst-vec-id-no-occurs ¬x∈M)

subst-vec-id-no-occurs {zero} {[]} ¬x∈M = refl
subst-vec-id-no-occurs {suc n} {N ∷ Ns} {x}{M} ¬x∈M
    with occurs? x N | occurs-vec? x Ns
... | yes x∈N | _ =
      ⊥-elim (¬x∈M (p⊆p∪q (vars N) (vars-vec Ns) x∈N))
... | no x∉N | yes x∈Ns = ⊥-elim (¬x∈M ((q⊆p∪q (vars N) (vars-vec Ns) x∈Ns))) 
... | no x∉N | no x∉Ns
    rewrite subst-id-no-occurs {N}{x}{M} x∉N
    | subst-vec-id-no-occurs {n}{Ns}{x}{M} x∉Ns = refl

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
  → θ unifies-eqs eqs
  → θ unifies-eqs ([ M / x ] eqs)
subst-pres {[]} eq θeqs = tt
subst-pres {⟨ L , N ⟩ ∷ eqs} {θ}{x}{M} eq ⟨ θLM , θeqs ⟩ =
  ⟨ subst-sub {L = L}{N = N} eq θLM , (subst-pres {eqs} eq θeqs) ⟩
```

```
subst-vec-pres : ∀{n}{Ms Ls : Vec AST n}{eqs}{θ}
   → θ unifies-eqs eqs
   → subst-vec θ Ms ≡ subst-vec θ Ls
   → θ unifies-eqs append-eqs Ms Ls eqs
subst-vec-pres {zero} {Ms} {Ls} θeqs θMsLs = θeqs
subst-vec-pres {suc n} {M ∷ Ms} {L ∷ Ls} θeqs θMLMsLs
    with ∷≡-inversion θMLMsLs
... | ⟨ θML , θMsLs ⟩ = ⟨ θML , (subst-vec-pres θeqs θMsLs) ⟩
```

```
unifier-pres : ∀{eqs σ θ}
   → θ unifies (middle eqs σ)
   → θ unifies (step eqs σ)
unifier-pres {[]}{eqs'} {θ} ⟨ θeqs , θeqs' ⟩ = θeqs'
unifier-pres {⟨ ` x , ` y ⟩ ∷ eqs}{eqs'} {θ} ⟨ ⟨ θxy , θeqs ⟩  , θeqs' ⟩
    with x ≟ y
... | yes xy = ⟨ θeqs , θeqs' ⟩
... | no xy = ⟨ subst-pres θxy θeqs , ⟨ θxy , subst-pres θxy θeqs' ⟩ ⟩
unifier-pres {⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ eqs}{eqs'}{θ} ⟨ ⟨ θxM , θeqs ⟩ , θeqs' ⟩ 
    with occurs? x (op ⦅ Ms ⦆)
... | yes x∈M = soln-no-occurs {θ}{x}{op ⦅ Ms ⦆} θxM tt x∈M
... | no x∉M = 
    ⟨ subst-pres θxM θeqs , ⟨ θxM , subst-pres θxM θeqs' ⟩ ⟩
unifier-pres {⟨ op ⦅ Ms ⦆ , ` x ⟩ ∷ eqs}{eqs'}{θ}
    ⟨ ⟨ θxM , θeqs ⟩ , θeqs' ⟩
    with occurs? x (op ⦅ Ms ⦆)
... | yes x∈M = soln-no-occurs {θ}{x}{op ⦅ Ms ⦆} (sym θxM) tt x∈M
... | no x∉M = 
    ⟨ subst-pres (sym θxM) θeqs , ⟨ sym θxM , subst-pres (sym θxM) θeqs' ⟩ ⟩
unifier-pres {⟨ op ⦅ Ms ⦆ , op' ⦅ Ls ⦆ ⟩ ∷ eqs}{eqs'}
    ⟨ ⟨ θMsLs , θeqs ⟩ , θeqs' ⟩
    with op-eq? op op'
... | yes refl = ⟨ subst-vec-pres θeqs (Ms≡-inversion θMsLs) , θeqs' ⟩
... | no neq = ⊥-elim (neq (op≡-inversion θMsLs))
```

## Proof of Termination

```
measure : State → ℕ × ℕ × ℕ
measure (middle eqs θ) = ⟨ ∣ vars-eqs eqs ∣ , ⟨ num-ops-eqs eqs , suc (length eqs) ⟩ ⟩
measure (done θ) = ⟨ 0 , ⟨ 0 , 0 ⟩ ⟩
measure error = ⟨ 0 , ⟨ 0 , 0 ⟩ ⟩

data mless : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ → Set where
   first-less : ∀{n₁ n₂ n₃ k₁ k₂ k₃}
     → n₁ < k₁
     → mless ⟨ n₁ , ⟨ n₂ , n₃ ⟩ ⟩ ⟨ k₁ , ⟨ k₂ , k₃ ⟩ ⟩ 

   second-less : ∀{n₁ n₂ n₃ k₁ k₂ k₃}
     → n₁ ≤ k₁ → n₂ < k₂
     → mless ⟨ n₁ , ⟨ n₂ , n₃ ⟩ ⟩ ⟨ k₁ , ⟨ k₂ , k₃ ⟩ ⟩ 

   third-less : ∀{n₁ n₂ n₃ k₁ k₂ k₃}
     → n₁ ≤ k₁ → n₂ ≤ k₂ → n₃ < k₃
     → mless ⟨ n₁ , ⟨ n₂ , n₃ ⟩ ⟩ ⟨ k₁ , ⟨ k₂ , k₃ ⟩ ⟩ 

middle? : State → Set
middle? (middle x x₁) = ⊤
middle? (done x) = ⊥
middle? error = ⊥

length-union-LB2 : ∀{xs ys : FiniteSet} → ∣ ys ∣ ≤ ∣ xs ∪ ys ∣
length-union-LB2 {xs}{ys} = p⊆q⇒∣p∣≤∣q∣ {ys}{xs ∪ ys} (q⊆p∪q xs ys)

vars-subst-∪ : ∀{N}{x M} → vars ([ x := M ] N) ⊆ vars M  ∪  (vars N - ⁅ x ⁆)
vars-vec-subst-∪ : ∀{n}{Ns : Vec AST n}{x M} → vars-vec ([ x ::= M ] Ns) ⊆ vars M  ∪  (vars-vec Ns - ⁅ x ⁆)
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

vars-eqs-sub-less : ∀{op Ms x eqs}
   → ¬ x ∈ vars-vec Ms
   → ∣ vars-eqs ([ op ⦅ Ms ⦆ / x ] eqs) ∣ < ∣ ⁅ x ⁆ ∪ vars-vec Ms ∪ vars-eqs eqs ∣
vars-eqs-sub-less {op}{Ms}{x}{eqs} x∉Ms = begin≤
         suc ∣ vars-eqs ([ M / x ] eqs) ∣          ≤⟨ s≤s (p⊆q⇒∣p∣≤∣q∣ (vars-eqs-subst-∪ {eqs}{x}{M})) ⟩
         suc ∣ vars M ∪ (vars-eqs eqs - ⁅ x ⁆) ∣   ≤⟨ ≤-reflexive (cong (λ □ → suc ∣ □ ∣) (distrib-∪-2 (vars M) (vars-eqs eqs) ⁅ x ⁆ G2)) ⟩
         suc ∣ (vars M ∪ vars-eqs eqs) - ⁅ x ⁆ ∣   ≤⟨ ∣p-x∣<∣p∪x∣ (vars M ∪ vars-eqs eqs) x ⟩
         ∣ (vars M ∪ vars-eqs eqs) ∪ ⁅ x ⁆ ∣       ≤⟨ ≤-reflexive (cong (λ □ → ∣ □ ∣) (∪-comm _ _)) ⟩
         ∣ ⁅ x ⁆ ∪ vars M ∪ vars-eqs eqs ∣
         QED
    where
    M = op ⦅ Ms ⦆
    G2 : vars M ∩ ⁅ x ⁆ ⊆ ∅
    G2 {z} z∈Ms∩x
        with x∈⁅y⁆→x≡y z x (∈p∩q→∈q z∈Ms∩x)
    ... | refl =
        let z∈Ms = ∈p∩q→∈p z∈Ms∩x in
        ⊥-elim (x∉Ms z∈Ms)

var-eqs-append-⊆ : ∀ {n} (Ms Ls : Vec AST n) eqs
   → vars-eqs (append-eqs Ms Ls eqs) ⊆ vars-vec Ms ∪ vars-vec Ls ∪ vars-eqs eqs
var-eqs-append-⊆ {zero} [] [] eqs x∈eqs
    rewrite ∅∪p≡p (vars-eqs eqs) | ∅∪p≡p (vars-eqs eqs) = x∈eqs
var-eqs-append-⊆ {suc n} (M ∷ Ms) (L ∷ Ls) eqs {x} x∈M∪L∪app-Ms-Ls-eqs
    rewrite sym (∪-assoc (vars M) (vars L) (vars-eqs (append-eqs Ms Ls eqs)))
    with ∈p∪q→∈p⊎∈q x∈M∪L∪app-Ms-Ls-eqs
... | inj₁ x∈M∪L = sub x∈M∪L
    where
    sub : vars M ∪ vars L ⊆ (vars M ∪ vars-vec Ms) ∪ (vars L ∪ vars-vec Ls) ∪ vars-eqs eqs
    sub = p⊆r→q⊆r→p∪q⊆r _ _ _ (p⊆q→p⊆q∪r _ _ _ (p⊆q→p⊆q∪r _ _ _ ⊆-refl))
            (p⊆r→p⊆q∪r _ _ _ (p⊆q→p⊆q∪r _ _ _ (p⊆q→p⊆q∪r _ _ _ ⊆-refl)))
    
... | inj₂ x∈app-Ms-Ls-eqs
    rewrite ∪-assoc (vars L) (vars-vec Ls) (vars-eqs eqs)
    | ∪-assoc (vars M) (vars-vec Ms) (vars L ∪ vars-vec Ls ∪ vars-eqs eqs)
    | sym (∪-assoc (vars-vec Ms) (vars L) (vars-vec Ls ∪ vars-eqs eqs))
    | ∪-comm (vars-vec Ms) (vars L) 
    | ∪-assoc (vars L) (vars-vec Ms) (vars-vec Ls ∪ vars-eqs eqs)
    | sym (∪-assoc (vars M) (vars L) (vars-vec Ms ∪ vars-vec Ls ∪ vars-eqs eqs)) =
    let IH = var-eqs-append-⊆ {n} Ms Ls eqs {x} x∈app-Ms-Ls-eqs in
    q⊆p∪q (vars M ∪ vars L) (vars-vec Ms ∪ vars-vec Ls ∪ vars-eqs eqs) {x} IH 

step-down : ∀ eqs θ → mless (measure (step eqs θ)) (measure (middle eqs θ))
step-down [] θ = third-less z≤n z≤n (s≤s z≤n)
step-down (⟨ ` x , ` y ⟩ ∷ eqs) θ 
    with x ≟ y
... | yes refl = third-less G1 ≤-refl (s≤s (s≤s ≤-refl))
    where
    G1 : ∣ vars-eqs eqs ∣ ≤ ∣ vars-eqs (⟨ ` x , ` x ⟩ ∷ eqs) ∣
    G1 = begin≤
         ∣ vars-eqs eqs ∣                         ≤⟨ length-union-LB2 {⁅ x ⁆} {vars-eqs eqs} ⟩
         ∣ ⁅ x ⁆ ∪ vars-eqs eqs ∣                 ≤⟨ length-union-LB2 {⁅ x ⁆} {⁅ x ⁆ ∪  vars-eqs eqs} ⟩
         ∣ ⁅ x ⁆ ∪ ⁅ x ⁆ ∪ vars-eqs eqs ∣         ≤⟨ ≤-refl ⟩
         ∣ vars-eqs (⟨ ` x , ` x ⟩ ∷ eqs) ∣       QED
... | no xy = first-less G1
    where
    G1 : ∣ vars-eqs ([ ` y / x ] eqs) ∣ < ∣ vars-eqs (⟨ ` x , ` y ⟩ ∷ eqs) ∣
    G1 = begin≤
         suc ∣ vars-eqs ([ ` y / x ] eqs) ∣       ≤⟨ s≤s (p⊆q⇒∣p∣≤∣q∣ (vars-eqs-subst-∪ {eqs} {x} {` y})) ⟩
         suc ∣ ⁅ y ⁆ ∪ (vars-eqs eqs - ⁅ x ⁆) ∣   ≤⟨ ≤-reflexive (cong (λ □ → suc ∣ □ ∣) (distrib-∪-2 ⁅ y ⁆ (vars-eqs eqs) ⁅ x ⁆ (⁅y⁆∩⁅x⁆⊆∅ x y xy))) ⟩
         suc ∣ (⁅ y ⁆ ∪ vars-eqs eqs) - ⁅ x ⁆ ∣   ≤⟨ ∣p-x∣<∣p∪x∣ (⁅ y ⁆ ∪ vars-eqs eqs) x ⟩
         ∣ (⁅ y ⁆ ∪ vars-eqs eqs) ∪ ⁅ x ⁆ ∣       ≤⟨ ≤-reflexive (cong ∣_∣ (∪-comm _ _)) ⟩
         ∣ ⁅ x ⁆ ∪ ⁅ y ⁆ ∪ vars-eqs eqs ∣         ≤⟨ ≤-reflexive refl ⟩
         ∣ vars-eqs (⟨ ` x , ` y ⟩ ∷ eqs) ∣       QED
step-down (⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ eqs) θ
    with occurs? x (op ⦅ Ms ⦆)
... | yes x∈M = second-less z≤n (s≤s z≤n)
... | no x∉M = first-less (vars-eqs-sub-less {op}{Ms}{x}{eqs} x∉M)
step-down (⟨ op ⦅ Ms ⦆ , ` x ⟩ ∷ eqs) θ
    with occurs? x (op ⦅ Ms ⦆)
... | yes x∈M = second-less z≤n (s≤s z≤n)
... | no x∉M = first-less G
    where
    G : ∣ vars-eqs ([ op ⦅ Ms ⦆ / x ] eqs) ∣ < ∣ vars-vec Ms ∪ ⁅ x ⁆ ∪ vars-eqs eqs ∣
    G = begin≤
        suc ∣ vars-eqs ([ op ⦅ Ms ⦆ / x ] eqs) ∣ ≤⟨ vars-eqs-sub-less {op}{Ms}{x}{eqs} x∉M ⟩
        ∣ ⁅ x ⁆ ∪ vars-vec Ms ∪ vars-eqs eqs ∣ ≤⟨ ≤-reflexive (cong (λ □ → ∣ □ ∣) (sym (∪-assoc _ _ _))) ⟩
        ∣ (⁅ x ⁆ ∪ vars-vec Ms) ∪ vars-eqs eqs ∣ ≤⟨ ≤-reflexive (cong (λ □ → ∣ □ ∪ vars-eqs eqs ∣) (∪-comm _ _)) ⟩
        ∣ (vars-vec Ms ∪ ⁅ x ⁆) ∪ vars-eqs eqs ∣ ≤⟨ ≤-reflexive (cong (λ □ → ∣ □ ∣) (∪-assoc _ _ _)) ⟩
        ∣ vars-vec Ms ∪ ⁅ x ⁆ ∪ vars-eqs eqs ∣
        QED
step-down (⟨ op ⦅ Ms ⦆ , op' ⦅ Ls ⦆ ⟩ ∷ eqs) θ
    with op-eq? op op'
... | no neq = second-less z≤n (s≤s z≤n)
... | yes refl = second-less G1 G2
    where
    G1 : ∣ vars-eqs (append-eqs Ms Ls eqs) ∣ ≤ ∣ vars-vec Ms ∪ vars-vec Ls ∪ vars-eqs eqs ∣
    G1 = p⊆q⇒∣p∣≤∣q∣ (var-eqs-append-⊆ Ms Ls eqs)
    G2 : num-ops-eqs (append-eqs Ms Ls eqs) < suc (num-ops-vec Ms + suc (num-ops-vec Ls) + num-ops-eqs eqs)
    G2 = {!!}

{-
solve : ∀{n₁ n₂ n₃ : ℕ} → (s : State)
   → {m : mless (measure s) ⟨ n₁ , ⟨ n₂ , n₃ ⟩ ⟩} → State
solve {zero} {zero} {zero} s {m} = {!!}
solve {zero} {zero} {suc n₃} s {m} = {!!}
solve {zero} {suc n₂} {n₃} s {m} = {!!}
solve {suc n₁} {n₂} {n₃} s {m} = {!!}
-}

```
