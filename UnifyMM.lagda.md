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

module UnifyMM
    (Op : Set)
    (op-eq? : (x : Op) → (y : Op) → Dec (x ≡ y))
    (arity : Op → ℕ) where

open import TermSubstUnify Op op-eq? arity public
```



```
data State : Set where
  s-in-progress : Equations → Equations → State
  s-finished : Equations → State
  s-no-solution : State
```




## Proof of Termination

```
measure : Equations → Equations → ℕ × ℕ × ℕ
measure eqs θ = ⟨ ∣ vars-eqs eqs ∣ , ⟨ num-ops-eqs eqs , suc (length eqs) ⟩ ⟩

open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import LexicographicOrdering {-using (×-Lex; ×-wellFounded)-}
open import Induction.WellFounded using (WellFounded)
open import Relation.Binary {-using (Rel)-}

_<₃_ : Rel (ℕ × ℕ × ℕ) _
_<₃_ = ×-Lex _≡_ _<_ (×-Lex _≡_ _<_ _<_)

<₃-wellFounded : WellFounded _<₃_
<₃-wellFounded = ×-wellFounded <-wellFounded
                   (×-wellFounded <-wellFounded <-wellFounded)

first-< : ∀ {k l m k' l' m'}
        → k < k'
        → ⟨ k , ⟨ l , m ⟩ ⟩ <₃ ⟨ k' , ⟨ l' , m' ⟩ ⟩
first-< k<k' = inj₁ k<k'

second-< : ∀ {k l m k' l' m'}
        → k ≤ k' → l < l'
        → ⟨ k , ⟨ l , m ⟩ ⟩ <₃ ⟨ k' , ⟨ l' , m' ⟩ ⟩
second-< {k}{k' = k'} k≤k' l<l'
    with k ≟ k'
... | yes refl = inj₂ ⟨ refl , inj₁ l<l' ⟩
... | no k≢k' = inj₁ (≤∧≢⇒< k≤k' k≢k')

third-< : ∀ {k l m k' l' m'}
        → k ≤ k' → l ≤ l' → m < m'
        → ⟨ k , ⟨ l , m ⟩ ⟩ <₃ ⟨ k' , ⟨ l' , m' ⟩ ⟩
third-< {k}{l}{k' = k'}{l'} k≤k' l≤l' m<m'
    with k ≟ k'
... | no k≢k' = inj₁ (≤∧≢⇒< k≤k' k≢k')
... | yes refl
    with l ≟ l'
... | no l≢l' = inj₂ ⟨ refl , (inj₁ (≤∧≢⇒< l≤l' l≢l')) ⟩
... | yes refl = inj₂ ⟨ refl , (inj₂ ⟨ refl , m<m' ⟩) ⟩


vars-eqs-sub-less : ∀{M x eqs}
   → ¬ x ∈ vars M
   → ∣ vars-eqs ([ M / x ] eqs) ∣ < ∣ ⁅ x ⁆ ∪ vars M ∪ vars-eqs eqs ∣
vars-eqs-sub-less {M}{x}{eqs} x∉M = begin≤
         suc ∣ vars-eqs ([ M / x ] eqs) ∣          ≤⟨ s≤s (p⊆q⇒∣p∣≤∣q∣ (vars-eqs-subst-∪ {eqs}{x}{M})) ⟩
         suc ∣ vars M ∪ (vars-eqs eqs - ⁅ x ⁆) ∣   ≤⟨ ≤-reflexive (cong (λ □ → suc ∣ □ ∣) (distrib-∪-2 (vars M) (vars-eqs eqs) ⁅ x ⁆ G2)) ⟩
         suc ∣ (vars M ∪ vars-eqs eqs) - ⁅ x ⁆ ∣   ≤⟨ ∣p-x∣<∣p∪x∣ (vars M ∪ vars-eqs eqs) x ⟩
         ∣ (vars M ∪ vars-eqs eqs) ∪ ⁅ x ⁆ ∣       ≤⟨ ≤-reflexive (cong (λ □ → ∣ □ ∣) (∪-comm _ _)) ⟩
         ∣ ⁅ x ⁆ ∪ vars M ∪ vars-eqs eqs ∣
         QED
    where
    G2 : vars M ∩ ⁅ x ⁆ ⊆ ∅
    G2 {z} z∈M∩x
        with x∈⁅y⁆→x≡y z x (∈p∩q→∈q z∈M∩x)
    ... | refl =
        let z∈M = ∈p∩q→∈p z∈M∩x in
        ⊥-elim (x∉M z∈M)

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

open import Data.Nat.Solver using (module +-*-Solver)

num-ops-append : ∀ {n} (Ms Ls : Vec AST n) eqs
   → num-ops-eqs (append-eqs Ms Ls eqs) ≡ num-ops-vec Ms + num-ops-vec Ls + num-ops-eqs eqs
num-ops-append {zero} [] [] eqs = refl
num-ops-append {suc n} (M ∷ Ms) (L ∷ Ls) eqs
    rewrite num-ops-append {n} Ms Ls eqs = G (num-ops M) (num-ops L) (num-ops-vec Ms) (num-ops-vec Ls) (num-ops-eqs eqs)
    where
    open +-*-Solver
    G : (nM nL nMs nLs neqs : ℕ) → (nM + nL) + ((nMs + nLs) + neqs) ≡ ((nM + nMs) + (nL + nLs)) + neqs
    G = solve 5 (λ nM nL nMs nLs neqs →
          (nM :+ nL) :+ ((nMs :+ nLs) :+ neqs) := ((nM :+ nMs) :+ (nL :+ nLs)) :+ neqs) refl
```

```
measure1 : ∀{eqs}{θ}{x} → measure eqs θ <₃ measure (⟨ ` x , ` x ⟩ ∷ eqs) θ
measure1 {eqs}{θ}{x} = third-< vars≤ ≤-refl (s≤s (s≤s ≤-refl))
    where
    vars≤ : ∣ vars-eqs eqs ∣ ≤ ∣ vars-eqs (⟨ ` x , ` x ⟩ ∷ eqs) ∣
    vars≤ =                                       begin≤
          ∣ vars-eqs eqs ∣                         ≤⟨ ∣q∣≤∣p∪q∣ {⁅ x ⁆} {vars-eqs eqs} ⟩
          ∣ ⁅ x ⁆ ∪ vars-eqs eqs ∣                 ≤⟨ ∣q∣≤∣p∪q∣ {⁅ x ⁆} {⁅ x ⁆ ∪  vars-eqs eqs} ⟩
          ∣ ⁅ x ⁆ ∪ ⁅ x ⁆ ∪ vars-eqs eqs ∣         ≤⟨ ≤-refl ⟩
          ∣ vars-eqs (⟨ ` x , ` x ⟩ ∷ eqs) ∣       QED
```

```
measure2 : ∀{eqs}{θ}{M}{x}
   → x ∉ vars M
   → measure ([ M / x ] eqs) (⟨ ` x , M ⟩ ∷ [ M / x ] θ)
     <₃ measure (⟨ ` x , M ⟩ ∷ eqs) θ
measure2{eqs}{θ}{M}{x} x∉M = (first-< (vars-eqs-sub-less {M}{x}{eqs} x∉M))
```

```
measure3 : ∀{eqs}{θ}{op}{Ms}{x}
   → x ∉ vars (op ⦅ Ms ⦆)
   → measure  ([ op ⦅ Ms ⦆ / x ] eqs) (⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ [ op ⦅ Ms ⦆ / x ] θ)
     <₃ measure (⟨ op ⦅ Ms ⦆ , ` x ⟩ ∷ eqs) θ
measure3 {eqs}{θ}{op}{Ms}{x} x∉M
    with vars-eqs-sub-less {op ⦅ Ms ⦆}{x}{eqs} x∉M
... | vars< 
    rewrite sym (∪-assoc ⁅ x ⁆ (vars-vec Ms) (vars-eqs eqs))
    | ∪-comm ⁅ x ⁆ (vars-vec Ms)
    | ∪-assoc (vars-vec Ms) ⁅ x ⁆ (vars-eqs eqs) = 
   first-< vars< 
```

```
measure4 : ∀{eqs}{θ}{op}{Ms Ls : Vec AST (arity op)}
   → measure (append-eqs Ms Ls eqs) θ
     <₃ measure (⟨ op ⦅ Ms ⦆ , op ⦅ Ls ⦆ ⟩ ∷ eqs) θ
measure4 {eqs}{θ}{op}{Ms}{Ls} = second-< vars≤ ops<
    where
    vars≤ : ∣ vars-eqs (append-eqs Ms Ls eqs) ∣ ≤ ∣ vars-vec Ms ∪ vars-vec Ls ∪ vars-eqs eqs ∣
    vars≤ = p⊆q⇒∣p∣≤∣q∣ (var-eqs-append-⊆ Ms Ls eqs)
    
    ops< : num-ops-eqs (append-eqs Ms Ls eqs) < suc (num-ops-vec Ms + suc (num-ops-vec Ls) + num-ops-eqs eqs)
    ops< rewrite num-ops-append Ms Ls eqs
         | +-comm (num-ops-vec Ms) (suc (num-ops-vec Ls))
         | +-comm (num-ops-vec Ls) (num-ops-vec Ms) = s≤s (≤-step ≤-refl)

```

## The Unify Function

Martelli and Montanari's Algorithm 1.

```
data Result : Set where
  finished : Equations → Result
  no-solution : Result

unify-aux : (eqs : Equations) → (θ : Equations)
          → Acc _<₃_ (measure eqs θ) → Result
unify-aux [] θ rec = finished θ
unify-aux (⟨ ` x , ` y ⟩ ∷ eqs) θ (acc rec)
    with x ≟ y
... | yes refl = unify-aux eqs θ (rec _ (measure1 {eqs}{θ}))
... | no xy =
    let eqs' = [ ` y / x ] eqs in
    let θ' = ⟨ ` x , ` y ⟩ ∷ [ ` y / x ] θ in
    unify-aux eqs' θ' (rec _ (measure2{eqs}{θ} (x∉⁅y⁆ _ _ xy)))
unify-aux (⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ eqs) θ (acc rec)
    with occurs? x (op ⦅ Ms ⦆)
... | yes x∈M = no-solution
... | no x∉M =
    let eqs' = [ op ⦅ Ms ⦆ / x ] eqs in
    let θ' = ⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ [ op ⦅ Ms ⦆ / x ] θ in
    unify-aux eqs' θ' (rec _ (measure2{eqs}{θ} x∉M))
unify-aux (⟨ op ⦅ Ms ⦆ , ` x ⟩ ∷ eqs) θ (acc rec)
    with occurs? x (op ⦅ Ms ⦆)
... | yes x∈M = no-solution
... | no x∉M =
    let eqs' = [ op ⦅ Ms ⦆ / x ] eqs in
    let θ' = ⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ [ op ⦅ Ms ⦆ / x ] θ in
    unify-aux eqs' θ' (rec _ (measure3{eqs}{θ} x∉M))
unify-aux (⟨ op ⦅ Ms ⦆ , op' ⦅ Ls ⦆ ⟩ ∷ eqs) θ (acc rec)
    with op-eq? op op'
... | yes refl = unify-aux (append-eqs Ms Ls eqs) θ (rec _ (measure4 {eqs}{θ}))
... | no neq = no-solution

unify : (eqs : Equations) → Result
unify eqs = unify-aux eqs [] (<₃-wellFounded (measure eqs []))
```

## Proof that Unify is Correct

```
xx-eqs∩dom⊆∅ : ∀ {x eqs σ}
   → (⁅ x ⁆ ∪ ⁅ x ⁆ ∪ vars-eqs eqs) ∩ dom σ ⊆ ∅
   → vars-eqs eqs ∩ dom σ ⊆ ∅
xx-eqs∩dom⊆∅ {x} sub {y} y∈
    with proj₁ (∈∩ y _ _) y∈
... | ⟨ y∈eqs , y∈σ ⟩ = sub (proj₂ (∈∩ _ _ _) ⟨ p⊆r→p⊆q∪r _ _ _ (p⊆r→p⊆q∪r _ _ _ ⊆-refl) y∈eqs , y∈σ ⟩)

x∉p∪q→x∉p×x∉q : ∀ {p q x} → x ∉ p ∪ q → x ∉ p × x ∉ q
x∉p∪q→x∉p×x∉q {p}{q}{x} x∉pq = ⟨ x∉p , x∉q ⟩
    where
    x∉p : x ∉ p
    x∉p x∈p = x∉pq (p⊆p∪q _ _ x∈p)
    x∉q : x ∉ q
    x∉q x∈q = x∉pq (q⊆p∪q _ _ x∈q)

subst-dom : ∀{x}{M}{σ}
   → x ∉ dom σ
   → dom ([ M / x ] σ) ≡ dom σ
subst-dom {x} {M} {[]} x∉σ = refl
subst-dom {x} {M} {⟨ L , N ⟩ ∷ σ} x∉Lσ
    with x∉p∪q→x∉p×x∉q x∉Lσ
... | ⟨ x∉L , x∉σ ⟩
    rewrite no-vars→subst-id {L}{x}{M} x∉L
    | subst-dom {x} {M} {σ} x∉σ = refl

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

M∪x∪eqs : ∀ {M}{x}{eqs}{σ}
   → (vars M ∪ ⁅ x ⁆ ∪ vars-eqs eqs) ∩ dom σ ⊆ ∅
   → (⁅ x ⁆ ∪ vars M ∪ vars-eqs eqs) ∩ dom σ ⊆ ∅
M∪x∪eqs {M}{x}{eqs}{σ} sub {y} y∈
    with proj₁ (∈∩ y _ _) y∈
... | ⟨ y∈[x]Meqs , y∈σ ⟩
    rewrite sym (∪-assoc (vars M) ⁅ x ⁆ (vars-eqs eqs))
    | ∪-comm (vars M) ⁅ x ⁆
    | ∪-assoc ⁅ x ⁆ (vars M) (vars-eqs eqs)
    = sub {y} (proj₂ (∈∩ y _ _) ⟨ y∈[x]Meqs , y∈σ ⟩ )


[x∪p]∩q⊆∅→x∉q : ∀{x p q} → (⁅ x ⁆ ∪ p) ∩ q ⊆ ∅ → x ∉ q
[x∪p]∩q⊆∅→x∉q {x}{p}{q} xpq x∈q =
    let x∈∅ = xpq {x} (proj₂ (∈∩ _ _ _) ⟨ (p⊆p∪q _ _ (x∈⁅x⁆ x)) , x∈q ⟩) in
    ⊥-elim (∉∅ x∈∅)

eqs∩x∪σ⊆∅ : ∀{x}{M}{σ}{eqs}
   → x ∉ vars M
   → (⁅ x ⁆ ∪ vars M ∪ vars-eqs eqs) ∩ dom σ ⊆ ∅
   → vars-eqs ([ M / x ] eqs) ∩ (⁅ x ⁆ ∪ dom ([ M / x ] σ)) ⊆ ∅
eqs∩x∪σ⊆∅ {x}{M}{σ}{eqs} x∉M eqs∩domσ⊆∅ {y} y∈
    rewrite subst-dom {x}{M}{σ} ([x∪p]∩q⊆∅→x∉q eqs∩domσ⊆∅)
    with proj₁ (∈∩ y _ _) y∈
... | ⟨ y∈[M/x]eqs , y∈[x]∪domσ ⟩
    with proj₁ (∈∪ y _ _) (vars-eqs-subst-∪ {eqs}{x}{M} y∈[M/x]eqs)
... | inj₂ y∈eqs-x
    with proj₁ (∈∪ y _ _) y∈[x]∪domσ
... | inj₁ y∈[x] rewrite (x∈⁅y⁆→x≡y _ _ y∈[x]) = ⊥-elim (x∉p-⁅x⁆ _ _ y∈eqs-x)
... | inj₂ y∈domσ = eqs∩domσ⊆∅ {y} (proj₂ (∈∩ y _ _) ⟨ y∈[x]∪M∪eqs , y∈domσ ⟩)
    where
    y∈eqs : y ∈ vars-eqs eqs
    y∈eqs = p-q⊆p _ _ y∈eqs-x
    y∈[x]∪M∪eqs : y ∈ ⁅ x ⁆ ∪ vars M ∪ vars-eqs eqs
    y∈[x]∪M∪eqs = p⊆r→p⊆q∪r _ _ _ (q⊆p∪q _ _) y∈eqs
eqs∩x∪σ⊆∅ {x}{M}{σ}{eqs} x∉M eqs∩domσ⊆∅ {y} y∈
    | ⟨ y∈[M/x]eqs , y∈[x]∪domσ ⟩
    | inj₁ y∈M
    with proj₁ (∈∪ y _ _) y∈[x]∪domσ
... | inj₁ y∈[x] rewrite x∈⁅y⁆→x≡y _ _ y∈[x] = ⊥-elim (x∉M y∈M)
... | inj₂ y∈domσ = eqs∩domσ⊆∅ {y} (proj₂ (∈∩ y _ _) ⟨ G , y∈domσ ⟩)
    where
    G : y ∈ ⁅ x ⁆ ∪ vars M ∪ vars-eqs eqs
    G = p⊆r→p⊆q∪r _ _ _ (p⊆p∪q _ _) y∈M

MsLseqs∩domσ⊆∅ : ∀{n}{Ms Ls : Vec AST n}{eqs}{σ}
   → (vars-vec Ms ∪ vars-vec Ls ∪ vars-eqs eqs) ∩ dom σ ⊆ ∅
   → vars-eqs (append-eqs Ms Ls eqs) ∩ dom σ ⊆ ∅
MsLseqs∩domσ⊆∅ {n}{Ms}{Ls}{eqs}{σ} prem =
   begin⊆
     vars-eqs (append-eqs Ms Ls eqs) ∩ dom σ              ⊆⟨ p⊆r→q⊆s→p∩q⊆r∩s _ _ _ _ (var-eqs-append-⊆ Ms Ls eqs) ⊆-refl ⟩
     (vars-vec Ms ∪ vars-vec Ls ∪ vars-eqs eqs) ∩ dom σ   ⊆⟨ prem ⟩
     ∅
   ■

subst-subst : ∀{x}{M}{σ}
   → IdemSubst σ
   → x ∉ dom σ
   → vars M ∩ dom σ ⊆ ∅
   → IdemSubst ([ M / x ] σ)
subst-subst {x} {M} {[]} empty x∉σ M∩σ⊆∅ = empty
subst-subst {x} {M} {(⟨ ` y , N ⟩ ∷ σ)} (insert y∉N y∉σ N∩domσ⊆∅ Sσ) x∉σ M∩σ⊆∅
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
         vars ([ x := M ] N) ∩ dom ([ M / x ] σ)  ⊆⟨ p⊆r→q⊆s→p∩q⊆r∩s _ _ _ _ (vars-subst-∪ {N}{x}{M}) (⊆-reflexive (subst-dom{x}{M}{σ} λ x∈σ → (x∉σ (q⊆p∪q _ _ x∈σ)))) ⟩
         (vars M ∪ (vars N - ⁅ x ⁆)) ∩ dom σ      ⊆⟨ p⊆r→q⊆s→p∩q⊆r∩s _ _ _ _ (p⊆r→q⊆s→p∪q⊆r∪s ⊆-refl (p-q⊆p _ _)) ⊆-refl ⟩
         (vars M ∪ vars N) ∩ dom σ                ⊆⟨ ⊆-reflexive ∪-distrib-∩ ⟩
         (vars M ∩ dom σ) ∪ (vars N ∩ dom σ)      ⊆⟨ p⊆r→q⊆s→p∪q⊆r∪s G5 N∩domσ⊆∅ ⟩
         ∅ ∪ ∅                                    ⊆⟨ ⊆-reflexive (∅∪p≡p _) ⟩
         ∅
         ■
      
    G4 : IdemSubst ([ M / x ] σ)
    G4 = subst-subst {x} {M}{σ} Sσ (λ x∈σ → x∉σ (q⊆p∪q _ _ x∈σ)) G5
    
insert-subst : ∀{x}{M}{σ}{eqs}
   → x ∉ vars M
   → (⁅ x ⁆ ∪ vars M ∪ vars-eqs eqs) ∩ dom σ ⊆ ∅
   → IdemSubst σ
   → IdemSubst (⟨ ` x , M ⟩ ∷ ([ M / x ] σ))
insert-subst {x}{M}{σ}{eqs} x∉M eqs∩domσ⊆∅ Sσ =
    insert x∉M K (M∩domσ⊆∅ {x}{M}{σ}{eqs} Sσ eqs∩domσ⊆∅)
        (subst-subst Sσ H G)
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


unify-aux-sound : ∀{eqs}{σ}{θ}{ac}
   → IdemSubst σ
   → vars-eqs eqs ∩ dom σ ⊆ ∅
   → unify-aux eqs σ ac ≡ finished θ
   → θ unifies eqs × θ unifies σ
unify-aux-sound {[]} {σ}{θ}{ac} Sσ eqs∩domσ⊆∅ refl = ⟨ tt , unifies-refl Sσ ⟩
unify-aux-sound {⟨ ` x , ` y ⟩ ∷ eqs} {σ} {θ} {acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡θ
    with x ≟ y 
... | yes refl
    with unify-aux-sound {eqs}{σ}{θ} {rs _ (measure1 {eqs}{θ})}
            Sσ (xx-eqs∩dom⊆∅ {x}{eqs}{σ} eqs∩domσ⊆∅) unify[eqs,σ]≡θ
... | ⟨ θeqs , θσ ⟩ =    
      ⟨ ⟨ refl , θeqs ⟩ , θσ ⟩
unify-aux-sound {⟨ ` x , ` y ⟩ ∷ eqs} {σ} {θ} {acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡θ
    | no xy
    with unify-aux-sound {[ ` y / x ] eqs}{(⟨ ` x , ` y ⟩ ∷ [ ` y / x ] σ)}{θ}
             {rs _ (measure2{eqs}{θ} (x∉⁅y⁆ _ _ xy))}
             (insert-subst {x}{` y}{σ}{eqs} (x∉⁅y⁆ x y xy) eqs∩domσ⊆∅ Sσ)
             (eqs∩x∪σ⊆∅ {x}{` y}{σ}{eqs} (x∉⁅y⁆ x y xy) eqs∩domσ⊆∅)
             unify[eqs,σ]≡θ
... | ⟨ θeqs , ⟨ θx=θy , θσ ⟩ ⟩ =     
       ⟨ ⟨ θx=θy , subst-reflect θeqs θx=θy ⟩ , subst-reflect θσ θx=θy ⟩
unify-aux-sound {⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ eqs} {σ} {θ}{acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡θ
    with occurs? x (op ⦅ Ms ⦆)
... | yes x∈M
    with unify[eqs,σ]≡θ
... | ()    
unify-aux-sound {⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ eqs} {σ} {θ}{acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡θ
    | no x∉M 
    with unify-aux-sound {([ op ⦅ Ms ⦆ / x ] eqs)} {(⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ [ op ⦅ Ms ⦆ / x ] σ)} {θ}
             {rs _ (measure2{eqs}{σ} x∉M)}
             (insert-subst {x}{op ⦅ Ms ⦆}{σ}{eqs} x∉M eqs∩domσ⊆∅ Sσ)
             (eqs∩x∪σ⊆∅ {x}{op ⦅ Ms ⦆}{σ}{eqs} x∉M eqs∩domσ⊆∅)
             unify[eqs,σ]≡θ
... | ⟨ θeqs , ⟨ θxM , θσ ⟩ ⟩ =
    ⟨ ⟨ θxM , subst-reflect θeqs θxM ⟩ , subst-reflect θσ θxM ⟩
unify-aux-sound {⟨ op ⦅ Ms ⦆ , ` x ⟩ ∷ eqs} {σ} {θ}{acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡θ
    with occurs? x (op ⦅ Ms ⦆)
... | yes x∈M
    with unify[eqs,σ]≡θ
... | ()    
unify-aux-sound {⟨ op ⦅ Ms ⦆ , ` x ⟩ ∷ eqs} {σ} {θ}{acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡θ
    | no x∉M
    with unify-aux-sound {([ op ⦅ Ms ⦆ / x ] eqs)} {(⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ [ op ⦅ Ms ⦆ / x ] σ)} {θ}
             {rs _ (measure3{eqs}{θ} x∉M)}
             ((insert-subst {x}{op ⦅ Ms ⦆}{σ}{eqs} x∉M (M∪x∪eqs {op ⦅ Ms ⦆}{x}{eqs}{σ} eqs∩domσ⊆∅) Sσ))
             (eqs∩x∪σ⊆∅ {x}{op ⦅ Ms ⦆}{σ}{eqs} x∉M (M∪x∪eqs {op ⦅ Ms ⦆}{x}{eqs}{σ} eqs∩domσ⊆∅))
             unify[eqs,σ]≡θ
... | ⟨ θeqs , ⟨ θxM , θσ ⟩ ⟩ =
    ⟨ ⟨ sym θxM , subst-reflect θeqs θxM ⟩ , subst-reflect θσ θxM ⟩
unify-aux-sound {⟨ op ⦅ Ms ⦆ , op' ⦅ Ls ⦆ ⟩ ∷ eqs} {σ} {θ}{acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡θ
    with op-eq? op op'
... | yes refl
    with unify-aux-sound {append-eqs Ms Ls eqs}{σ}{θ}{rs _ (measure4{eqs}{θ})} Sσ (MsLseqs∩domσ⊆∅ {Ms = Ms}{Ls = Ls}{σ = σ} eqs∩domσ⊆∅) unify[eqs,σ]≡θ
... | ⟨ θMs,Ls,eqs , θσ ⟩
    with subst-vec-reflect {Ms = Ms}{Ls} θMs,Ls,eqs
... | ⟨ θMs=θLs , θeqs ⟩ =
    ⟨ ⟨ cong (λ □ → op ⦅ □ ⦆) θMs=θLs  , θeqs ⟩ , θσ ⟩
unify-aux-sound {⟨ op ⦅ Ms ⦆ , op' ⦅ Ls ⦆ ⟩ ∷ eqs} {σ} {θ}{acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡θ
    | no neq
    with unify[eqs,σ]≡θ
... | ()    

unify-sound : ∀{eqs}{θ}
   → unify eqs ≡ finished θ
   → θ unifies eqs
unify-sound {eqs}{θ} unify-eqs-θ =
    let m = (<₃-wellFounded (measure eqs [])) in
    proj₁ (unify-aux-sound {eqs}{[]}{θ}{m} empty G unify-eqs-θ)
    where
    G : vars-eqs eqs ∩ ∅ ⊆ ∅
    G rewrite p∩∅≡∅ (vars-eqs eqs) = λ z → z
```


```
unify-aux-complete : ∀{eqs}{σ}{ac}
   → IdemSubst σ
   → vars-eqs eqs ∩ dom σ ⊆ ∅
   → unify-aux eqs σ ac ≡ no-solution
   → ∀ θ → ¬ (θ unifies eqs × θ unifies σ)
unify-aux-complete {⟨ ` x , ` y ⟩ ∷ eqs} {σ} {acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡no θ ⟨ ⟨ θxy , θeqs ⟩ , θσ ⟩
    with x ≟ y
... | yes refl =
    unify-aux-complete {eqs}{σ} {rs _ (measure1 {eqs}{θ})}
        Sσ (xx-eqs∩dom⊆∅ {x}{eqs}{σ} eqs∩domσ⊆∅) unify[eqs,σ]≡no θ ⟨ θeqs , θσ ⟩ 
... | no xy =
    let eqs' = [ ` y / x ] eqs in
    let σ' = ⟨ ` x , ` y ⟩ ∷ [ ` y / x ] σ in
    unify-aux-complete {eqs'}{σ'}{rs _ (measure2{eqs}{θ} (x∉⁅y⁆ _ _ xy))}
        (insert-subst {x}{` y}{σ}{eqs} (x∉⁅y⁆ x y xy) eqs∩domσ⊆∅ Sσ)
        (eqs∩x∪σ⊆∅ {x}{` y}{σ}{eqs} (x∉⁅y⁆ x y xy) eqs∩domσ⊆∅)
        unify[eqs,σ]≡no θ ⟨ subst-pres θxy θeqs , ⟨ θxy , (subst-pres θxy θσ) ⟩ ⟩
unify-aux-complete {⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ eqs} {σ} {acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡no θ ⟨ ⟨ θxM , θeqs ⟩ , θσ ⟩
    with occurs? x (op ⦅ Ms ⦆)
... | yes x∈M = occurs-no-soln {M = op ⦅ Ms ⦆} x∈M tt θxM
... | no x∉M =
    let eqs' = [ op ⦅ Ms ⦆ / x ] eqs in
    let σ' = ⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ [ op ⦅ Ms ⦆ / x ] σ in
    unify-aux-complete {eqs'}{σ'}{rs _ (measure2{eqs}{θ} x∉M)}
        (insert-subst {x}{op ⦅ Ms ⦆}{σ}{eqs} x∉M eqs∩domσ⊆∅ Sσ)
        (eqs∩x∪σ⊆∅ {x}{op ⦅ Ms ⦆}{σ}{eqs} x∉M eqs∩domσ⊆∅)
        unify[eqs,σ]≡no θ ⟨ subst-pres θxM θeqs , ⟨ θxM , (subst-pres θxM θσ) ⟩ ⟩
unify-aux-complete {⟨ op ⦅ Ms ⦆ , ` x ⟩ ∷ eqs} {σ} {acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡no θ ⟨ ⟨ θMx , θeqs ⟩ , θσ ⟩
    with occurs? x (op ⦅ Ms ⦆)
... | yes x∈M = occurs-no-soln {M = op ⦅ Ms ⦆} x∈M tt (sym θMx)
... | no x∉M =
    let eqs' = [ op ⦅ Ms ⦆ / x ] eqs in
    let σ' = ⟨ ` x , op ⦅ Ms ⦆ ⟩ ∷ [ op ⦅ Ms ⦆ / x ] σ in
    unify-aux-complete {eqs'}{σ'}{rs _ (measure3{eqs}{θ} x∉M)}
        (insert-subst {x}{op ⦅ Ms ⦆}{σ}{eqs} x∉M (M∪x∪eqs {op ⦅ Ms ⦆}{x}{eqs}{σ} eqs∩domσ⊆∅) Sσ)
        (eqs∩x∪σ⊆∅ {x}{op ⦅ Ms ⦆}{σ}{eqs} x∉M (M∪x∪eqs {op ⦅ Ms ⦆}{x}{eqs}{σ} eqs∩domσ⊆∅))
        unify[eqs,σ]≡no θ ⟨ subst-pres (sym θMx) θeqs , ⟨ (sym θMx) , (subst-pres (sym θMx) θσ) ⟩ ⟩
unify-aux-complete {⟨ op ⦅ Ms ⦆ , op' ⦅ Ls ⦆ ⟩ ∷ eqs} {σ} {acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡no θ ⟨ ⟨ θML , θeqs ⟩ , θσ ⟩
    with op-eq? op op'
... | yes refl =    
    unify-aux-complete {append-eqs Ms Ls eqs}{σ}{rs _ (measure4{eqs}{θ})} Sσ
        (MsLseqs∩domσ⊆∅ {Ms = Ms}{Ls = Ls}{σ = σ} eqs∩domσ⊆∅) unify[eqs,σ]≡no θ
        ⟨ subst-vec-pres {Ms = Ms}{Ls = Ls} θeqs (Ms≡-inversion θML) , θσ ⟩
unify-aux-complete {⟨ op ⦅ Ms ⦆ , op' ⦅ Ls ⦆ ⟩ ∷ eqs} {σ} {acc rs} Sσ eqs∩domσ⊆∅ unify[eqs,σ]≡no θ ⟨ ⟨ θML , θeqs ⟩ , θσ ⟩
    | no neq = neq (op≡-inversion θML)

unify-complete :  ∀{eqs}
   → unify eqs ≡ no-solution
   → ∀ θ → ¬ θ unifies eqs
unify-complete {eqs} unify[eqs]=no θ θeqs =
    let m = (<₃-wellFounded (measure eqs [])) in
    unify-aux-complete {eqs}{[]}{m} empty G unify[eqs]=no θ ⟨ θeqs , tt ⟩
    where
    G : vars-eqs eqs ∩ ∅ ⊆ ∅
    G rewrite p∩∅≡∅ (vars-eqs eqs) = λ z → z
```
