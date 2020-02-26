```
open import Agda.Primitive using (lzero)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.DecPropositional using (_∈?_)
open import Data.Maybe
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; z≤n; s≤s; _<?_)
open import Data.Nat.Properties
  using (m≤m+n; m≤n+m; ≤-step; ≤-pred; n≤1+n; 1+n≰n)
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
occurs-vec : Var → ∀{n} → Vec AST n → Set

occurs : Var → AST → Set
occurs x (` y)
    with x ≟ y
... | yes xy = ⊤
... | no xy = ⊥
occurs x (op ⦅ Ms ⦆) = occurs-vec x Ms

occurs-vec x {zero} Ms = ⊥
occurs-vec x {suc n} (M ∷ Ms) = occurs x M  ⊎  occurs-vec x Ms

occurs-eqs : Var → Equations → Set
occurs-eqs x [] = ⊥
occurs-eqs x (⟨ M , L ⟩ ∷ eqs) = occurs x M  ⊎  occurs x L  ⊎  occurs-eqs x eqs 
```

```
occurs-vec? : (x : Var) → ∀{n} → (Ms : Vec AST n) → Dec (occurs-vec x Ms)

occurs? : (x : Var) → (M : AST) → Dec (occurs x M)
occurs? x (` y)
    with x ≟ y
... | yes xy = yes tt
... | no xy = no (λ z → z)
occurs? x (op ⦅ Ms ⦆) = occurs-vec? x Ms

occurs-vec? x {zero} Ms = no (λ z → z)
occurs-vec? x {suc n} (M ∷ Ms)
    with occurs? x M
... | yes x∈M = yes (inj₁ x∈M)
... | no x∉M
    with occurs-vec? x Ms
... | yes x∈Ms = yes (inj₂ x∈Ms)
... | no x∉Ms = no λ { (inj₁ x∈M) → x∉M x∈M ; (inj₂ x∈Ms) → x∉Ms x∈Ms }
```

```
data State : Set where
  middle : Equations → Equations → State
  done : Equations → State
  error : State
```


Martelli and Montanari's Algorithm 1.

```
step : State → State
step (done σ) = (done σ)
step error = error
step (middle [] σ) = done σ
step (middle (⟨ ` x , ` y ⟩ ∷ eqs) σ)
    with x ≟ y
... | yes xy = middle eqs σ
... | no xy = middle ([ ` y / x ] eqs) (⟨ ` x , ` y ⟩ ∷ [ ` y / x ] σ)

step (middle (⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ eqs) σ) =
  middle ([ op ⦅ Ms ⦆ / x ] eqs) (⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ [ op ⦅ Ms ⦆ / x ] σ)

step (middle (⟨ op ⦅ Ms ⦆ , ` x ⟩ ∷ eqs) σ) =
  middle ([ op ⦅ Ms ⦆ / x ] eqs) (⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ [ op ⦅ Ms ⦆ / x ] σ)

step (middle (⟨ op ⦅ Ms ⦆ , op' ⦅ Ls ⦆ ⟩ ∷ eqs) σ)
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
   s≤s (num-ops-less-vec {θ = θ} x∈Ms)

num-ops-less-vec {suc n} {(` y) ∷ Ms}{x}{θ} (inj₁ x∈M)
    with x ≟ y
... | yes refl = m≤m+n (num-ops (subst θ (` y))) (num-ops-vec (subst-vec θ Ms))
... | no xy = ⊥-elim x∈M
num-ops-less-vec {suc n} {(op ⦅ Ls ⦆) ∷ Ms}{x}{θ} (inj₁ x∈M) =
  let θx<1+θLS = num-ops-less {(op ⦅ Ls ⦆)}{x}{θ} x∈M tt in
  begin≤
     num-ops (subst θ (` x))       ≤⟨ ≤-pred θx<1+θLS ⟩
     num-ops-vec (subst-vec θ Ls)  ≤⟨ m≤m+n _ _ ⟩
     num-ops-vec (subst-vec θ Ls) + num-ops-vec (subst-vec θ Ms) ≤⟨ n≤1+n _ ⟩
     suc (num-ops-vec (subst-vec θ Ls) + num-ops-vec (subst-vec θ Ms))
    QED
num-ops-less-vec {suc n} {M ∷ Ms}{x}{θ} (inj₂ x∈Ms) =
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
... | yes refl = ⊥-elim (¬x∈M tt)
... | no xy = refl
subst-id-no-occurs {op ⦅ Ns ⦆} ¬x∈M =
    cong (λ □ → op ⦅ □ ⦆) (subst-vec-id-no-occurs ¬x∈M)

subst-vec-id-no-occurs {zero} {[]} ¬x∈M = refl
subst-vec-id-no-occurs {suc n} {N ∷ Ns} {x}{M} ¬x∈M
    with occurs? x N | occurs-vec? x Ns
... | yes x∈N | _ = ⊥-elim (¬x∈M (inj₁ x∈N))
... | no x∉N | yes x∈Ns = ⊥-elim (¬x∈M (inj₂ x∈Ns)) 
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
unifier-pres : ∀{σ θ}
   → θ unifies σ
   → θ unifies (step σ)
unifier-pres {middle [] eqs'} {θ} ⟨ θeqs , θeqs' ⟩ = θeqs'
unifier-pres {middle (⟨ ` x , ` y ⟩ ∷ eqs) eqs'} {θ} ⟨ ⟨ θxy , θeqs ⟩  , θeqs' ⟩
    with x ≟ y
... | yes xy = ⟨ θeqs , θeqs' ⟩
... | no xy = ⟨ subst-pres θxy θeqs , ⟨ θxy , subst-pres θxy θeqs' ⟩ ⟩
unifier-pres {middle (⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ eqs) eqs'}
    ⟨ ⟨ θxM , θeqs ⟩ , θeqs' ⟩ =
    ⟨ subst-pres θxM θeqs , ⟨ θxM , subst-pres θxM θeqs' ⟩ ⟩
unifier-pres {middle (⟨ op ⦅ Ms ⦆ , ` x ⟩ ∷ eqs) eqs'}
    ⟨ ⟨ θxM , θeqs ⟩ , θeqs' ⟩ =
    ⟨ subst-pres (sym θxM) θeqs , ⟨ sym θxM , subst-pres (sym θxM) θeqs' ⟩ ⟩
unifier-pres {middle (⟨ op ⦅ Ms ⦆ , op' ⦅ Ls ⦆ ⟩ ∷ eqs) eqs'}
    ⟨ ⟨ θMsLs , θeqs ⟩ , θeqs' ⟩
    with op-eq? op op'
... | yes refl = ⟨ subst-vec-pres θeqs (Ms≡-inversion θMsLs) , θeqs' ⟩
... | no neq = ⊥-elim (neq (op≡-inversion θMsLs))
unifier-pres {done eqs} θσ = θσ
```

## Proof of Termination

```
union : List ℕ → List ℕ → List ℕ
union [] ys = ys
union (x ∷ xs) ys
    with (_∈?_ _≟_) x ys
... | yes x∈ys = union xs ys
... | no x∉ys = x ∷ (union xs ys)

vars-vec : ∀{n} → Vec AST n → List ℕ

vars : AST → List ℕ
vars (` x) = x ∷ []
vars (op ⦅ Ms ⦆) = vars-vec Ms

vars-vec {zero} Ms = []
vars-vec {suc n} (M ∷ Ms) = union (vars M) (vars-vec Ms)

vars-eqs : Equations → List ℕ
vars-eqs [] = []
vars-eqs (⟨ L , M ⟩ ∷ eqs) = union (vars L) (union (vars M) (vars-eqs eqs))

num-vars : Equations → ℕ
num-vars eqs = length (vars-eqs eqs)

measure : State → ℕ × ℕ × ℕ
measure (middle eqs θ) = ⟨ num-vars eqs , ⟨ num-ops-eqs eqs , suc (length eqs) ⟩ ⟩
measure (done θ) = ⟨ 0 , ⟨ 0 , 0 ⟩ ⟩
measure error = ⟨ 0 , ⟨ 0 , 0 ⟩ ⟩

data mless : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ → Set where
   first-less : ∀{n₁ n₂ n₃ k₁ k₂ k₃}
     → n₁ < k₁
     → mless ⟨ n₁ , ⟨ n₂ , n₃ ⟩ ⟩ ⟨ k₁ , ⟨ k₂ , k₃ ⟩ ⟩ 

   second-less : ∀{n₁ n₂ n₃ k₁ k₂ k₃}
     → n₁ ≡ k₁ → n₂ < k₂
     → mless ⟨ n₁ , ⟨ n₂ , n₃ ⟩ ⟩ ⟨ k₁ , ⟨ k₂ , k₃ ⟩ ⟩ 

   third-less : ∀{n₁ n₂ n₃ k₁ k₂ k₃}
     → n₁ ≡ k₁ → n₂ ≡ k₂ → n₃ < k₃
     → mless ⟨ n₁ , ⟨ n₂ , n₃ ⟩ ⟩ ⟨ k₁ , ⟨ k₂ , k₃ ⟩ ⟩ 

middle? : State → Set
middle? (middle x x₁) = ⊤
middle? (done x) = ⊥
middle? error = ⊥

step-down : ∀ s → (m : middle? s) → mless (measure (step s)) (measure s)
step-down (middle [] θ) m = third-less refl refl (s≤s z≤n)
step-down (middle (⟨ ` x , ` y ⟩ ∷ eqs) θ) m
    with x ≟ y
... | yes xy = third-less {!!} refl {!!}
... | no xy = {!!}
step-down (middle (⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ eqs) θ) m = {!!}
step-down (middle (⟨ op ⦅ Ms ⦆ , ` y ⟩ ∷ eqs) θ) m = {!!}
step-down (middle (⟨ op ⦅ Ms ⦆ , op' ⦅ Ls ⦆ ⟩ ∷ eqs) θ) m = {!!}

{-
solve : ∀{n₁ n₂ n₃ : ℕ} → (s : State)
   → {m : mless (measure s) ⟨ n₁ , ⟨ n₂ , n₃ ⟩ ⟩} → State
solve {zero} {zero} {zero} s {m} = {!!}
solve {zero} {zero} {suc n₃} s {m} = {!!}
solve {zero} {suc n₂} {n₃} s {m} = {!!}
solve {suc n₁} {n₂} {n₃} s {m} = {!!}
-}

```
