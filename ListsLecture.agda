{-

  Jan. 28, 2020

-}

open import Data.Nat
open import Data.List using (List; []; _∷_; map; unzip; reverse; splitAt; _++_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

_ : List ℕ
_ = 1 ∷ 2 ∷ []

{-

  rotate (1 ∷ 2 ∷ 3 ∷ []) 2 = (3 ∷ 1 ∷ 2 ∷ [])

-}

rotate : ∀{A : Set} → List A → ℕ → List A
rotate xs k
    with splitAt k xs
... | ⟨ ls , rs ⟩ =
    let ls' = reverse ls in
    let rs' = reverse rs in
    reverse (ls' ++ rs')

_ : rotate (1 ∷ 2 ∷ 3 ∷ []) 1 ≡ (2 ∷ 3 ∷ 1 ∷ [])
_ = refl

_ : rotate (1 ∷ 2 ∷ 3 ∷ []) 2 ≡ (3 ∷ 1 ∷ 2 ∷ [])
_ = refl

_ : rotate (1 ∷ 2 ∷ 3 ∷ []) 3 ≡ (1 ∷ 2 ∷ 3 ∷ [])
_ = refl

open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Relation.Binary.PropositionalEquality using (sym; cong; cong₂)
open import Data.List.Properties using (reverse-++-commute; reverse-involutive)

rotate-correct : ∀{A : Set}{xs ys zs : List A}{k : ℕ}
  → splitAt k xs ≡ ⟨ ys , zs ⟩
  → rotate xs k ≡ zs ++ ys
rotate-correct {A}{xs}{ys}{zs}{k} refl =
                                       begin
    rotate xs k                        ≡⟨ refl ⟩
    reverse (reverse ys ++ reverse zs) ≡⟨ cong reverse (sym (reverse-++-commute zs ys)) ⟩
    reverse (reverse (zs ++ ys))       ≡⟨ reverse-involutive (zs ++ ys) ⟩
    zs ++ ys                           ∎


open import Function using (_∘_)

map-compose : ∀{A B C : Set}{g : B → C}{f : A → B}
            → (xs : List A)
            → map (g ∘ f) xs ≡ map g (map f xs)
map-compose [] = refl
map-compose {g = g}{f} (x ∷ xs) = cong (λ □ →  g (f x) ∷ □) (map-compose xs)

