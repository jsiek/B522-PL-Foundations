module ConnectivesNegationLecture where

{-

  Jan. 27, 2020

-}

{-

  propositions as types

  true          unit
  implication   function type
  conjunction   pair (product) type
  disjunction   disjoint union (sum) type
  false         empty

  proposition is proved true  if  type is inhabitable

-}

variable P Q R S : Set

{- True -}
open import Data.Unit using (⊤; tt)

_ : ⊤
_ = tt

{- Implication -}

_ : P → P
_ = λ p → p

{- P isomorphic to (⊤ → P) -}

_ : (⊤ → P) → P
_ = λ f → f tt

{- Conjunction -}

open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

_ : P × Q → Q × P
_ = λ pq → ⟨ (proj₂ pq) , (proj₁ pq) ⟩

{- Disjunction -}

open import Data.Sum using (_⊎_; inj₁; inj₂)

_ : P → Q ⊎ P
_ = λ p → inj₂ p

_ : P ⊎ Q → Q ⊎ P
_ = λ { (inj₁ p) → inj₂ p ; (inj₂ q) → inj₁ q }

f : (P → Q) × (R → Q) → ((P ⊎ R) → Q)
f ⟨ pq , rq ⟩ (inj₁ p) = pq p
f ⟨ pq , rq ⟩ (inj₂ r) = rq r

{-

 False

-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Nat

_ : 0 ≡ 1 → ⊥
_ = λ ()

g : 0 ≡ 1 → ⊥
g ()

open import Data.Empty using (⊥-elim)

h : 0 ≡ 1 → P
h 0≡1 = ⊥-elim (g 0≡1)

h2 : 0 ≡ 1 → Q
h2 0≡1 = ⊥-elim (g 0≡1)

k : 0 ≡ 1 → P
k ()

{- Negation -}

open import Relation.Nullary using (¬_)

_ : (¬ P) ≡ (P → ⊥)
_ = refl

_ : P → (¬ P) → ⊥
_ = λ p ¬p → ¬p p

_ : P → (¬ P) → Q
_ = λ p ¬p → ⊥-elim (¬p p)

_ : P → ¬ ¬ P
_ = λ p ¬p → ¬p p

{-

The other direction, ¬ ¬ P → P, requires Classical logic,
but Agda is Intuitionistic, so it can't be proved in Agda.

-}

{-

  Quantifiers: for all, there exists

-}

postulate Human : Set
postulate Socrates : Human 
postulate Mortal : Human → Set

postulate all-Humans-mortal : (p : Human) → Mortal p
postulate all-Humans-mortal' : ∀ (p : Human) → Mortal p
postulate all-Humans-mortal'' : ∀ p → Mortal p

_ : Mortal Socrates
_ = all-Humans-mortal Socrates

open import Data.Nat.Properties

*-0 : ∀ n → n * 0 ≡ 0
*-0 n rewrite *-comm n 0 = refl

g2 : ∀{P : Set}{Q R : P → Set}
  → (∀ (x : P) → Q x) ⊎ (∀ (x : P) → R x)
  → ∀ (x : P)
  → Q x ⊎ R x
g2 (inj₁ q) x = inj₁ (q x)
g2 (inj₂ r) x = inj₂ (r x)


{- Existentials as Dependent Products -}

{- 
   This first example is about getting use to
   dependent products by encoding logical-or.
-}   

open import Data.Product using (Σ-syntax)

open import Data.Bool using (Bool; true; false)

select : (A : Set) → (B : Set) → Bool → Set
select A B false = A
select A B true = B

_or_ : Set → Set → Set
A or B = Σ[ flag ∈ Bool ] select A B flag

inject₁ : ∀{A B : Set} → A → A or B
inject₁ a = ⟨ false , a ⟩

inject₂ : ∀{A B : Set} → B → A or B
inject₂ b = ⟨ true , b ⟩

case : ∀{A B C : Set} → A or B → (A → C) → (B → C) → C
case ⟨ false , a ⟩ ac bc = ac a
case ⟨ true , b ⟩ ac bc = bc b

{-

  An example proof involving existentials.

-}

∀∃-currying1 : ∀{A : Set}{B : A → Set}{C : Set}
  → (∀ (x : A) → B x → C)
  → (Σ[ x ∈ A ] B x) → C
∀∃-currying1 f ⟨ x , Bx ⟩ = f x Bx

∀∃-currying2 : ∀{A : Set}{B : A → Set}{C : Set}
  → ((Σ[ x ∈ A ] B x) → C)
  → (∀ (x : A) → B x → C)
∀∃-currying2 g x y = g ⟨ x , y ⟩

