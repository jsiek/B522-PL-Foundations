```
open import Agda.Primitive using (lzero)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
   renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; sym; inspect; [_]; cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning
   using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import UnionFind

module UnifyMM
    (Op : Set)
    (op-eq? : (x : Op) → (y : Op) → Dec (x ≡ y))
    (arity : Op → ℕ) where
```

```
Var = ℕ

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
occurs-vec : Var → ∀{n} → Vec AST n → Bool

occurs : Var → AST → Bool
occurs x (` y)
    with x ≟ y
... | yes xy = true
... | no xy = false
occurs x (op ⦅ Ms ⦆) = occurs-vec x Ms

occurs-vec x {zero} Ms = false
occurs-vec x {suc n} (M ∷ Ms) = occurs x M  ∨  occurs-vec x Ms

occurs-eqs : Var → Equations → Bool
occurs-eqs x [] = false
occurs-eqs x (⟨ M , L ⟩ ∷ eqs) = occurs x M  ∨  occurs x L  ∨  occurs-eqs x eqs 
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
no-just : ∀{M : AST} → nothing ≡ just M → ⊥
no-just ()
```

```
subst-sub : ∀{L N}{z}{θ}{M}
  → (∀ {x M} → lookup θ x ≡ just M → subst θ M ≡ M)
  → (∀ {x M N} → lookup θ x ≡ just M → [ x := N ] M ≡ M)
  → lookup θ z ≡ just M
  → subst θ L ≡ subst θ N
  → subst θ ([ z := M ] L) ≡ subst θ ([ z := M ] N)
subst-sub {` x} {` y}{z}{θ}{M} θidem θidem2 θzM θLM
    with z ≟ x | z ≟ y
... | yes zx | yes zy = refl
... | no zx  | no zy = θLM
... | yes refl | no zy
    with lookup θ x | lookup θ y | inspect (lookup θ) x | inspect (lookup θ) y
... | nothing | _ | [ θx ] | [ θy ] = ⊥-elim (no-just θzM)
subst-sub {` x} {` y}{z}{θ}{M} θidem θidem2 θzM θLM | yes refl | no zy
    | just M' | just L' | [ θx ] | [ θy ]
    with θLM | θzM
... | refl | refl = θidem θx
subst-sub {` x} {` y}{z}{θ}{M} θidem θidem2 θzM θLM | yes refl | no zy
    | just M' | nothing | [ θx ] | [ θy ]
    with θzM | θLM
... | refl | refl
    with lookup θ y | inspect (lookup θ) y
... | nothing | [ θy' ] = refl
... | just M'' | [ θy' ] = ⊥-elim (no-just (sym θy))
subst-sub {` x} {` y}{z}{θ}{M} θidem θidem2 θzM θLM | no zx  | yes refl
    with lookup θ x | lookup θ y | inspect (lookup θ) x | inspect (lookup θ) y
... | nothing | just L' | [ θx ] | [ θy ]
    with θLM | θzM
... | refl | refl
    with lookup θ x
... | nothing = refl
... | just M' = ⊥-elim (no-just (sym θx))
subst-sub {` x} {` y}{z}{θ}{M} θidem θidem2 θzM θLM | no zx  | yes refl
    | just M' | just L' | [ θx ] | [ θy ]
    with θLM | θzM
... | refl | refl = sym (θidem θy)
subst-sub {` x} {` y}{z}{θ}{M} θidem θidem2 θzM θLM | no zx  | yes refl
    | just M' | nothing | [ θx ] | [ θy ]
    with θzM
... | ()
subst-sub {` x} {op ⦅ Ns ⦆}{z}{θ} θidem θidem2 θzM θLM
    with z ≟ x 
... | yes refl
    with lookup θ x | inspect (lookup θ) x
... | nothing | [ θx ] = ⊥-elim (no-just θzM)
... | just M' | [ θx ]
    with θLM | θzM
... | refl | refl =
    cong (λ □ → op ⦅ □ ⦆) G
    where
    G : subst-vec θ (subst-vec θ Ns) ≡
        subst-vec θ ([ x ::= op ⦅ subst-vec θ Ns ⦆ ] Ns)
    G = begin
        subst-vec θ (subst-vec θ Ns)                    ≡⟨ Ms≡-inversion (θidem θx) ⟩
        subst-vec θ Ns                                  ≡⟨ cong (λ □ → subst-vec θ □) (sym {!!}) ⟩
        subst-vec θ ([ x ::= op ⦅ subst-vec θ Ns ⦆ ] Ns) ∎

{-    
    with Ms≡-inversion (θidem2 {N = op ⦅ subst-vec θ Ns ⦆} θx)
... | eq    
    rewrite Ms≡-inversion (θidem θx) =
    {!!}
-}

subst-sub {` x} {op ⦅ Ns ⦆}{z} θidem θidem2 θzM θLM | no zx = {!!}
subst-sub {op ⦅ Ls ⦆} {` x} θidem θidem2 θzM θLM = {!!}
subst-sub {op ⦅ Ls ⦆} {op' ⦅ Ns ⦆} θidem θidem2 θzM θLM = {!!}


subst-sub2 : ∀{L}{N}{z}{θ}{M}
  → subst θ (` z) ≡ subst θ M
  → subst θ L ≡ subst θ N
  → subst θ ([ z := M ] L) ≡ subst θ ([ z := M ] N)
subst-sub2 {` x} {` y} {z} {θ} {M} θzM θLM
    with z ≟ x | z ≟ y
... | yes refl | yes refl = refl
... | yes refl | no zy =
                             begin
        subst θ M            ≡⟨ sym θzM ⟩
        subst θ (` x)        ≡⟨ θLM ⟩
        subst θ (` y)
        ∎
... | no zx | yes refl =
                             begin
        subst θ (` x)        ≡⟨ θLM ⟩
        subst θ (` y)        ≡⟨ θzM ⟩
        subst θ M
        ∎
... | no zx | no zy = θLM
subst-sub2 {` x} {op ⦅ Ns ⦆} {z} {θ} {M} θzM θLM
    with z ≟ x
... | yes refl
    with lookup θ x
... | nothing = {!!}
... | just M' =
                                 begin
        subst θ M                           ≡⟨ sym θzM ⟩
        M'                                  ≡⟨ θLM ⟩
        op ⦅ subst-vec θ Ns ⦆                ≡⟨ {!!} ⟩
        op ⦅ subst-vec θ ([ x ::= M ] Ns) ⦆  ≡⟨⟩
        subst θ ([ x := M ] (op ⦅ Ns ⦆))
        ∎
subst-sub2 {` x} {op ⦅ Ns ⦆} {z} {θ} {M} θzM θLM
    | no zx = {!!}
subst-sub2 {op ⦅ Ls ⦆} {` y} {z} {θ} {M} θzM θLM = {!!}
subst-sub2 {op ⦅ Ls ⦆} {op' ⦅ Ns ⦆} {z} {θ} {M} θzM θLM = {!!}
```
 

```
subst-pres : ∀{eqs θ x M}
  → subst θ (` x) ≡ subst θ M
  → θ unifies-eqs eqs
  → θ unifies-eqs ([ M / x ] eqs)
subst-pres {[]} eq θeqs = tt
subst-pres {⟨ L , N ⟩ ∷ eqs} {θ}{x}{M} eq ⟨ θLM , θeqs ⟩ =
  ⟨ subst-sub2 {L = L}{N = N} eq θLM , (subst-pres {eqs} eq θeqs) ⟩
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
