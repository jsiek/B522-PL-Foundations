module FiniteSet where

{-

  The FiniteSet type represents a finite set of natural numbers.
  It does so using a list of bits.
  This module is based on the Data.Fin.Subset module, but doesn't
  index the finite set type with the size of the full set. 

-}

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat
open import Data.Nat.Properties using (∣n-n∣≡0; +-comm; ⊔-comm; ≤-refl; ≤-reflexive; ≤-step)
open Data.Nat.Properties.≤-Reasoning
  using (_≤⟨_⟩_)
  renaming (begin_ to begin≤_; _∎ to _QED)
open import Data.Bool
  using (Bool; true; false; T; _∨_; _∧_)
open import Data.Bool.Properties
  using (∨-comm; ∨-assoc)
open import Data.List
open import Data.Product
  using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
   using (_≡_; _≢_; refl; sym; inspect; [_]; cong; subst)
open Relation.Binary.PropositionalEquality.≡-Reasoning
   using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

abstract

{---------------------------------------------------
  Definitions
----------------------------------------------------}  

  FiniteSet : Set
  FiniteSet = List Bool

  ∅ : FiniteSet
  ∅ = []

  ⁅_⁆ : ℕ → FiniteSet
  ⁅ 0 ⁆ = true ∷ []
  ⁅ suc n ⁆ = false ∷ ⁅ n ⁆

  infix 4 _∈_ _∉_ _⊆_ _⇔_
  infixr 8 _-_
  infixr 7 _∩_
  infixr 6 _∪_

  _∈_ : ℕ → FiniteSet → Set
  x ∈ [] = ⊥
  zero ∈ b ∷ p = T b
  suc x ∈ b ∷ p = x ∈ p

_∉_ : ℕ → FiniteSet → Set
x ∉ p = ¬ (x ∈ p)

_⊆_ : FiniteSet → FiniteSet → Set
p ⊆ q = ∀ {x} → x ∈ p → x ∈ q  

_⇔_ : FiniteSet → FiniteSet → Set
p ⇔ q = p ⊆ q × q ⊆ p

abstract

  _∪_ : FiniteSet → FiniteSet → FiniteSet
  [] ∪ ys = ys
  (x ∷ xs) ∪ [] = x ∷ xs
  (b ∷ xs) ∪ (c ∷ ys) = (b ∨ c) ∷ (xs ∪ ys)

  _∩_ : FiniteSet → FiniteSet → FiniteSet
  [] ∩ ys = []
  (x ∷ xs) ∩ [] = []
  (b ∷ xs) ∩ (c ∷ ys) = (b ∧ c) ∷ (xs ∩ ys)

  subtract : Bool → Bool → Bool
  subtract false b = false
  subtract true false = true
  subtract true true = false

  _-_ : FiniteSet → FiniteSet → FiniteSet
  [] - ys = []
  (x ∷ xs) - [] = x ∷ xs
  (b ∷ xs) - (c ∷ ys) = (subtract b c) ∷ (xs - ys)

  ∣_∣ : FiniteSet → ℕ
  ∣ [] ∣ = 0
  ∣ false ∷ p ∣ = ∣ p ∣
  ∣ true ∷ p ∣ = suc ∣ p ∣

{---------------------------------------------------
  Properties
----------------------------------------------------}  

  ∉∅ : ∀{x} → x ∉ ∅
  ∉∅ {x} ()

  ∅⊆p : ∀{p} → ∅ ⊆ p
  ∅⊆p {p} ()

  ∣∅∣≡0 : ∣ ∅ ∣ ≡ 0  
  ∣∅∣≡0 = refl

  ∣⁅x⁆∣≡1 : ∀ x → ∣ ⁅ x ⁆ ∣ ≡ 1
  ∣⁅x⁆∣≡1 zero = refl
  ∣⁅x⁆∣≡1 (suc x) = ∣⁅x⁆∣≡1 x

  x∈⁅x⁆ : ∀ x → x ∈ ⁅ x ⁆
  x∈⁅x⁆ zero = tt
  x∈⁅x⁆ (suc x) = x∈⁅x⁆ x

  x∉⁅y⁆ : ∀ x y → x ≢ y → x ∉ ⁅ y ⁆
  x∉⁅y⁆ zero zero x∈ = ⊥-elim (x∈ refl)
  x∉⁅y⁆ (suc x) zero x∈ = λ z → z
  x∉⁅y⁆ zero (suc y) x∈ = λ z → z
  x∉⁅y⁆ (suc x) (suc y) x∈ = x∉⁅y⁆ x y λ z → x∈ (cong suc z)
  
  ⊆-refl : ∀ {S} → S ⊆ S
  ⊆-refl {S} = λ z → z
  
  ⊆-trans : ∀ {S T U} → S ⊆ T → T ⊆ U → S ⊆ U
  ⊆-trans {S}{T}{U} = λ z z₁ {x} z₂ → z₁ (z z₂)

  p⊆q⇒∣p∣≤∣q∣ : ∀ {S T} → S ⊆ T → ∣ S ∣ ≤ ∣ T ∣
  p⊆q⇒∣p∣≤∣q∣ {[]} {[]} S⊆T = z≤n
  p⊆q⇒∣p∣≤∣q∣ {[]} {false ∷ T} S⊆T = p⊆q⇒∣p∣≤∣q∣ {[]}{T} λ {x} ()
  p⊆q⇒∣p∣≤∣q∣ {[]} {true ∷ T} S⊆T = z≤n
  p⊆q⇒∣p∣≤∣q∣ {false ∷ S} {[]} S⊆T =
      p⊆q⇒∣p∣≤∣q∣ {S} {[]} λ {x} x∈ → S⊆T {suc x} x∈
  p⊆q⇒∣p∣≤∣q∣ {true ∷ S} {[]} S⊆T = ⊥-elim (S⊆T {0} tt)
  p⊆q⇒∣p∣≤∣q∣ {false ∷ S} {false ∷ T} S⊆T =
      p⊆q⇒∣p∣≤∣q∣ {S} {T} λ {x} x∈ → S⊆T {suc x} x∈
  p⊆q⇒∣p∣≤∣q∣ {false ∷ S} {true ∷ T} S⊆T =
      let IH = p⊆q⇒∣p∣≤∣q∣ {S} {T} λ {x} x∈ → S⊆T {suc x} x∈ in
      ≤-step IH
  p⊆q⇒∣p∣≤∣q∣ {true ∷ S} {false ∷ T} S⊆T = ⊥-elim (S⊆T {0} tt)
  p⊆q⇒∣p∣≤∣q∣ {true ∷ S} {true ∷ T} S⊆T =
      s≤s (p⊆q⇒∣p∣≤∣q∣ {S} {T} λ {x} x∈ → S⊆T {suc x} x∈)

  ∣p∪q∣≤∣p∣+∣q∣ : ∀{p q} → ∣ p ∪ q ∣ ≤ ∣ p ∣ + ∣ q ∣
  ∣p∪q∣≤∣p∣+∣q∣ {[]} {q} = ≤-refl
  ∣p∪q∣≤∣p∣+∣q∣ {x ∷ p} {[]} rewrite +-comm ∣ x ∷ p ∣ 0 = ≤-refl
  ∣p∪q∣≤∣p∣+∣q∣ {false ∷ p} {false ∷ q} = ∣p∪q∣≤∣p∣+∣q∣ {p} {q}
  ∣p∪q∣≤∣p∣+∣q∣ {false ∷ p} {true ∷ q}
      rewrite +-comm ∣ p ∣ (suc ∣ q ∣)
      | +-comm ∣ q ∣ ∣ p ∣ = s≤s (∣p∪q∣≤∣p∣+∣q∣ {p} {q})
  ∣p∪q∣≤∣p∣+∣q∣ {true ∷ p} {false ∷ q} = s≤s (∣p∪q∣≤∣p∣+∣q∣ {p} {q})
  ∣p∪q∣≤∣p∣+∣q∣ {true ∷ p} {true ∷ q}
      rewrite +-comm ∣ p ∣ (suc ∣ q ∣)
      | +-comm ∣ q ∣ ∣ p ∣ = s≤s (≤-step (∣p∪q∣≤∣p∣+∣q∣ {p} {q}))

  ∪-comm : ∀ p q → p ∪ q ≡ q ∪ p
  ∪-comm [] [] = refl
  ∪-comm [] (x ∷ q) = refl
  ∪-comm (x ∷ p) [] = refl
  ∪-comm (b ∷ p) (c ∷ q) rewrite ∨-comm b c | ∪-comm p q = refl
  
  ∪-assoc : ∀ p q r → (p ∪ q) ∪ r ≡ p ∪ (q ∪ r)
  ∪-assoc [] q r = refl
  ∪-assoc (a ∷ p) [] r = refl
  ∪-assoc (a ∷ p) (b ∷ q) [] = refl
  ∪-assoc (a ∷ p) (b ∷ q) (c ∷ r)
      rewrite ∨-assoc a b c
      | ∪-assoc p q r = refl

  p⊆p∪q : (p q : FiniteSet) → p ⊆ p ∪ q
  p⊆p∪q p [] x∈p rewrite ∪-comm p [] = x∈p
  p⊆p∪q (true ∷ p) (c ∷ q) {zero} x∈p = tt
  p⊆p∪q (b ∷ p) (c ∷ q) {suc x} x∈p = p⊆p∪q p q x∈p

  q⊆p∪q : ∀ (p q : FiniteSet) → q ⊆ p ∪ q
  q⊆p∪q [] (c ∷ q) {x} x∈q = x∈q
  q⊆p∪q (false ∷ p) (true ∷ q) {zero} x∈q = tt
  q⊆p∪q (true ∷ p) (true ∷ q) {zero} x∈q = tt
  q⊆p∪q (b ∷ p) (c ∷ q) {suc x} x∈q = q⊆p∪q p q {x} x∈q

  ∈p∪q→∈p⊎∈q : ∀{p q x} → x ∈ p ∪ q → x ∈ p ⊎ x ∈ q
  ∈p∪q→∈p⊎∈q {[]} {q} {x} x∈pq = inj₂ x∈pq
  ∈p∪q→∈p⊎∈q {b ∷ p} {[]} {x} x∈pq = inj₁ x∈pq
  ∈p∪q→∈p⊎∈q {false ∷ p} {c ∷ q} {zero} x∈pq = inj₂ x∈pq
  ∈p∪q→∈p⊎∈q {true ∷ p} {c ∷ q} {zero} x∈pq = inj₁ tt
  ∈p∪q→∈p⊎∈q {b ∷ p} {c ∷ q} {suc x} x∈pq = ∈p∪q→∈p⊎∈q {p} {q} {x} x∈pq

  ∈p∩q→∈p : ∀{p q x} → x ∈ p ∩ q → x ∈ p
  ∈p∩q→∈p {true ∷ p} {true ∷ q} {zero} x∈p∩q = tt
  ∈p∩q→∈p {a ∷ p} {b ∷ q} {suc x} x∈p∩q = ∈p∩q→∈p {p} {q} {x} x∈p∩q

  ∈p∩q→∈q : ∀{p q x} → x ∈ p ∩ q → x ∈ q
  ∈p∩q→∈q {true ∷ p} {true ∷ q} {zero} x∈p∩q = tt
  ∈p∩q→∈q {a ∷ p} {b ∷ q} {suc x} x∈p∩q = ∈p∩q→∈q {p} {q} {x} x∈p∩q
  
  ∪-lub : ∀ {p q r } → p ⊆ r → q ⊆ r → p ∪ q ⊆ r
  ∪-lub {p}{q}{r} pr qr {x} x∈p∪q
      with ∈p∪q→∈p⊎∈q {p}{q}{x} x∈p∪q
  ... | inj₁ x∈p = pr x∈p
  ... | inj₂ x∈q = qr x∈q

  p⊆r→q⊆s→p∪q⊆r∪s : ∀{p q r s} → p ⊆ r → q ⊆ s → p ∪ q ⊆ r ∪ s
  p⊆r→q⊆s→p∪q⊆r∪s {p}{q}{r}{s} pr qs {x} x∈p∪q
      with ∈p∪q→∈p⊎∈q {p}{q}{x} x∈p∪q
  ... | inj₁ x∈p = (p⊆p∪q r s) (pr x∈p)
  ... | inj₂ x∈q = (q⊆p∪q r s) (qs x∈q)

  infix  1 begin⊆_
  infixr 2 _⊆⟨_⟩_
  infix  3 _■

  begin⊆_ : ∀{p q} → p ⊆ q → p ⊆ q
  begin⊆_ pq = pq

  _⊆⟨_⟩_ : ∀ p {q r} → p ⊆ q → q ⊆ r → p ⊆ r
  _⊆⟨_⟩_ p {q}{r} p⊆q q⊆r = ⊆-trans {p}{q}{r} p⊆q q⊆r

  _■ : ∀ p → p ⊆ p
  _■ p = ⊆-refl {p}

  ⊆-reflexive : ∀ {p q} → p ≡ q → p ⊆ q
  ⊆-reflexive {p} refl = ⊆-refl {p}

  ∪-idem : ∀ p → p ∪ p ≡ p
  ∪-idem [] = refl
  ∪-idem (false ∷ p) rewrite ∪-idem p = refl
  ∪-idem (true ∷ p) rewrite ∪-idem p = refl

  p-p⊆∅ : ∀ p → p - p ⊆ ∅
  p-p⊆∅ [] ()
  p-p⊆∅ (false ∷ p) {suc x} x∈ = p-p⊆∅ p {x} x∈
  p-p⊆∅ (true ∷ p) {suc x} x∈ = p-p⊆∅ p {x} x∈

  ∅⊆p-p : ∀ p → ∅ ⊆ p - p
  ∅⊆p-p p {x} ()

  p-∅≡p : ∀ p → p - ∅ ≡ p
  p-∅≡p [] = refl
  p-∅≡p (x ∷ p) = refl

  ⁅y⁆-⁅x⁆≡⁅y⁆ : ∀ {x y } → x ≢ y → ⁅ y ⁆ - ⁅ x ⁆ ≡ ⁅ y ⁆
  ⁅y⁆-⁅x⁆≡⁅y⁆ {zero} {zero} xy = ⊥-elim (xy refl)
  ⁅y⁆-⁅x⁆≡⁅y⁆ {suc x} {zero} xy = refl
  ⁅y⁆-⁅x⁆≡⁅y⁆ {zero} {suc y} xy = cong (λ □ → false ∷ □) (p-∅≡p _)
  ⁅y⁆-⁅x⁆≡⁅y⁆ {suc x} {suc y} xy =
      cong (λ □ → false ∷ □) (⁅y⁆-⁅x⁆≡⁅y⁆ λ z → xy (cong suc z))

  ⁅y⁆∩⁅x⁆⊆∅ : ∀ x y → x ≢ y → ⁅ y ⁆ ∩ ⁅ x ⁆ ⊆ ∅
  ⁅y⁆∩⁅x⁆⊆∅ zero zero xy = ⊥-elim (xy refl)
  ⁅y⁆∩⁅x⁆⊆∅ zero (suc y) xy {z}
       with y
  ... | 0
      with z
  ... | 0 = λ z → z
  ... | suc z' = λ z → z
  ⁅y⁆∩⁅x⁆⊆∅ zero (suc y) xy {0} | suc y' = λ z → z
  ⁅y⁆∩⁅x⁆⊆∅ zero (suc y) xy {suc z} | suc y' = λ z → z
  ⁅y⁆∩⁅x⁆⊆∅ (suc x) zero xy {zero} = λ z → z
  ⁅y⁆∩⁅x⁆⊆∅ (suc x) zero xy {suc z} = λ z → z
  ⁅y⁆∩⁅x⁆⊆∅ (suc x) (suc y) xy {zero} = λ z → z
  ⁅y⁆∩⁅x⁆⊆∅ (suc x) (suc y) xy {suc z} =
      (⁅y⁆∩⁅x⁆⊆∅ x y λ z → xy (cong suc z)) {z}
      
  ∪-identityʳ₁ : ∀ p → p ⊆ p ∪ ∅
  ∪-identityʳ₁ [] ()
  ∪-identityʳ₁ (b ∷ p) {x} x∈ = x∈

  p∪∅≡p : ∀ p → p ∪ ∅ ≡ p
  p∪∅≡p [] = refl
  p∪∅≡p (x ∷ p) = refl

  distrib-∨-sub : ∀ a b c → subtract a c ∨ subtract b c ≡ subtract (a ∨ b) c
  distrib-∨-sub false b c = refl
  distrib-∨-sub true false false = refl
  distrib-∨-sub true false true = refl
  distrib-∨-sub true true false = refl
  distrib-∨-sub true true true = refl

  distrib-∪- : ∀ p q r → (p - r) ∪ (q - r) ≡ (p ∪ q) - r
  distrib-∪- [] [] r = refl
  distrib-∪- [] (x ∷ q) r = refl
  distrib-∪- (x ∷ p) [] r = p∪∅≡p _
  distrib-∪- (a ∷ p) (b ∷ q) [] = refl
  distrib-∪- (a ∷ p) (b ∷ q) (c ∷ r)
      rewrite distrib-∪- p q r | distrib-∨-sub a b c = refl

  p∩r⊆∅→p-r≡p : ∀ p r
     → p ∩ r ⊆ ∅
     → p - r ≡ p
  p∩r⊆∅→p-r≡p [] r p∩r = refl
  p∩r⊆∅→p-r≡p (x ∷ p) [] p∩r = refl
  p∩r⊆∅→p-r≡p (false ∷ p) (_ ∷ r) p∩r =
    let IH = p∩r⊆∅→p-r≡p p r (λ {z} z∈ → p∩r {suc z} z∈) in
    cong (λ □ → false ∷ □) IH
  p∩r⊆∅→p-r≡p (true ∷ p) (false ∷ r) p∩r =
    let IH = p∩r⊆∅→p-r≡p p r (λ {z} z∈ → p∩r {suc z} z∈) in
    cong (λ □ → true ∷ □) IH
  p∩r⊆∅→p-r≡p (true ∷ p) (true ∷ r) p∩r = ⊥-elim (p∩r {0} tt)

  distrib-∪-2 : ∀ p q r
     → p ∩ r ⊆ ∅
     → p ∪ (q - r) ≡ (p ∪ q) - r
  distrib-∪-2 [] q r p∩r = refl
  distrib-∪-2 (x ∷ p) [] [] p∩r = refl
  distrib-∪-2 (false ∷ p) [] (b ∷ r) p∩r =
      cong (λ □ → false ∷ □) (sym (p∩r⊆∅→p-r≡p p r (λ {x} z → p∩r {suc x} z)))
  distrib-∪-2 (true ∷ p) [] (false ∷ r) p∩r =
      cong (λ □ → true ∷ □) (sym (p∩r⊆∅→p-r≡p p r (λ {x} z → p∩r {suc x} z)))
  distrib-∪-2 (true ∷ p) [] (true ∷ r) p∩r = ⊥-elim (p∩r {0} tt)
  distrib-∪-2 (a ∷ p) (b ∷ q) [] p∩r = refl
  distrib-∪-2 (false ∷ p) (b ∷ q) (c ∷ r) p∩r =
      let IH = distrib-∪-2 p q r λ {x} x∈ → p∩r {suc x} x∈ in
      cong (λ □ → subtract b c ∷ □) IH
  distrib-∪-2 (true ∷ p) (b ∷ q) (false ∷ r) p∩r =
      let IH = distrib-∪-2 p q r λ {x} x∈ → p∩r {suc x} x∈ in
      cong (λ □ → true ∷ □) IH
  distrib-∪-2 (true ∷ p) (b ∷ q) (true ∷ r) p∩r = ⊥-elim (p∩r {0} tt)

  ∣p-x∣<∣p∪x∣ : ∀ p x → ∣ (p - ⁅ x ⁆) ∣ < ∣ p ∪ ⁅ x ⁆ ∣
  ∣p-x∣<∣p∪x∣ [] x
      rewrite ∣⁅x⁆∣≡1 x = ≤-refl
  ∣p-x∣<∣p∪x∣ (false ∷ p) zero
      rewrite p-∅≡p p = s≤s (p⊆q⇒∣p∣≤∣q∣ {p}{p ∪ ∅} (∪-identityʳ₁ p))
  ∣p-x∣<∣p∪x∣ (true ∷ p) zero
      rewrite p-∅≡p p = s≤s (p⊆q⇒∣p∣≤∣q∣ {p}{p ∪ ∅} (∪-identityʳ₁ p))  
  ∣p-x∣<∣p∪x∣ (false ∷ p) (suc x) = ∣p-x∣<∣p∪x∣ p x
  ∣p-x∣<∣p∪x∣ (true ∷ p) (suc x) = s≤s (∣p-x∣<∣p∪x∣ p x)
