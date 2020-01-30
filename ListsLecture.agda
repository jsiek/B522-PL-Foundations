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

map-compose' : ∀{A B C : Set}(g : B → C)(f : A → B)
            → (xs : List A)
            → map (g ∘ f) xs ≡ map g (map f xs)
map-compose' g f [] = refl
map-compose' g f (x ∷ xs) = cong (λ □ →  g (f x) ∷ □) (map-compose' g f xs)

_ : map ((λ x → x) ∘ (λ x → x)) (1 ∷ 2 ∷ []) ≡ map (λ x → x) (map (λ x → x) (1 ∷ 2 ∷ []))
_ = map-compose' (λ x → x) (λ x → x) (1 ∷ 2 ∷ []) 

map-compose'' : ∀{A B C : Set}{g : B → C}{f : A → B}
            → {xs : List A}
            → map (g ∘ f) xs ≡ map g (map f xs)
map-compose'' {xs = []} = refl
map-compose'' {g = g}{f = f}{xs = (x ∷ xs)} = cong (λ □ →  g (f x) ∷ □) (map-compose'')

_ : map ((λ x → x) ∘ (λ x → x)) (1 ∷ 2 ∷ []) ≡ map (λ x → x) (map (λ x → x) (1 ∷ 2 ∷ []))
_ = map-compose'' {ℕ} {ℕ} {ℕ} {(λ x → x)} {(λ x → x)} {(1 ∷ 2 ∷ [])}

{-

  Jan. 29, 2020

-}

_▵_ : ∀{A B C : Set} → (A → B) → (A → C) → A → B × C
(f ▵ g) a = ⟨ (f a) , (g a) ⟩

_⊗_ : ∀{A B C D : Set} → (A → B) → (C → D) → A × C → B × D
(f ⊗ g) ⟨ a , c ⟩ = ⟨ f a , g c ⟩


{-
  unzip [⟨a,b⟩,⟨x,y⟩] ≡ ⟨ [a,x] , [b,y] ⟩
-}

unzip-slow : {A B : Set} → List (A × B) → List A × List B
unzip-slow xs = ((map proj₁) ▵ (map proj₂)) xs

unzip-fast : {A B : Set} → List (A × B) → List A × List B
unzip-fast [] = ⟨ [] , [] ⟩
unzip-fast (⟨ a , b ⟩ ∷ xs) =
   let ⟨ as , bs ⟩ = unzip-fast xs in
   ⟨ (a ∷ as) , (b ∷ bs) ⟩

unzip≡▵map : ∀{A B : Set}
           → (xs : List (A × B))
           → unzip xs ≡ ((map proj₁) ▵ (map proj₂)) xs
unzip≡▵map {A} {B} [] =
  begin
    unzip []       ≡⟨⟩
    ⟨ [] , [] ⟩    ≡⟨⟩
    ((map proj₁) ▵ (map proj₂)) []
  ∎ 
unzip≡▵map {A} {B} (⟨ a , b ⟩ ∷ xs) =
   begin
     unzip (⟨ a , b ⟩ ∷ xs)                           ≡⟨ refl ⟩
     ⟨ a ∷ proj₁ (unzip xs) , b ∷ proj₂ (unzip xs) ⟩  ≡⟨ cong (λ □ → ⟨ a ∷ proj₁ □ , b ∷ proj₂ □ ⟩) (unzip≡▵map xs) ⟩
     ⟨ a ∷ proj₁ (((map proj₁) ▵ (map proj₂)) xs) , b ∷ proj₂ (((map proj₁) ▵ (map proj₂)) xs) ⟩  ≡⟨ refl ⟩
     (map proj₁ ▵ map proj₂) (⟨ a , b ⟩ ∷ xs)
   ∎

⊗-distrib-unzip : ∀{A B C D} {f : A → B} {g : C → D}
    → (xs : List (A × C))
    → (map f ⊗ map g) (unzip xs) ≡ unzip (map (f ⊗ g) xs)
⊗-distrib-unzip {f = f}{g = g} xs =
  begin
     (map f ⊗ map g) (unzip xs)                             ≡⟨ cong (λ □ → (map f ⊗ map g) □) (unzip≡▵map xs) ⟩
     (map f ⊗ map g) (((map proj₁) ▵ (map proj₂)) xs)       ≡⟨ refl ⟩
     (map f ⊗ map g) ⟨ map proj₁ xs , map proj₂ xs ⟩        ≡⟨ refl ⟩
     ⟨ map f (map proj₁ xs) , map g (map proj₂ xs) ⟩        ≡⟨ cong ((λ □ → ⟨ □ , map g (map proj₂ xs) ⟩)) (sym (map-compose xs)) ⟩
     ⟨ map (f ∘ proj₁) xs , map g (map proj₂ xs) ⟩          ≡⟨ cong (λ □ → ⟨ map (f ∘ proj₁) xs , □ ⟩) (sym (map-compose xs)) ⟩
     ⟨ map (f ∘ proj₁) xs , map (g ∘ proj₂) xs ⟩            ≡⟨ refl ⟩
     ⟨ map (proj₁ ∘ (f ⊗ g)) xs , map (proj₂ ∘ (f ⊗ g)) xs ⟩ ≡⟨ cong₂ ⟨_,_⟩ (map-compose xs) (map-compose xs) ⟩
     ⟨ map proj₁ (map (f ⊗ g) xs) , map proj₂ (map (f ⊗ g) xs) ⟩  ≡⟨⟩ 
     ((map proj₁) ▵ (map proj₂)) (map (f ⊗ g) xs)           ≡⟨ sym (unzip≡▵map (map (f ⊗ g) xs)) ⟩
     unzip (map (f ⊗ g) xs)
  ∎
