```
module UnionFind where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
   renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
   using (_≡_; _≢_; refl; sym; trans)
open import Relation.Nullary using (¬_)

_≟_ : (x : ℕ) → (y : ℕ) → Dec (x ≡ y)
zero ≟ zero = yes refl
zero ≟ suc y = no (λ ())
suc x ≟ zero = no (λ ())
suc x ≟ suc y
    with x ≟ y
... | yes refl = yes refl
... | no xy = no λ {refl → xy refl}

abstract

  UnionFind : Set
  init : UnionFind
  union : ℕ → ℕ → UnionFind → UnionFind
  find : UnionFind → ℕ → ℕ
  
  private 
    IdempotentFun : ∀{A : Set} → (A → A) → Set
    IdempotentFun {A} f = ∀{x} → f (f x) ≡ f x

  UnionFind = Σ[ uf ∈ (ℕ → ℕ) ] IdempotentFun uf
  find ⟨ uf , idem ⟩ x = uf x
  init = ⟨ (λ x → x) , refl ⟩

  private
    union-fun : ℕ → ℕ → (ℕ → ℕ) → (ℕ → ℕ)
    union-fun x y uf z
        with uf x ≟ uf z
    ... | yes xz = uf y
    ... | no xz = uf z

    union-idem : ∀{x y uf}
               → IdempotentFun uf
               → IdempotentFun (union-fun x y uf)
    union-idem {x}{y}{uf} idem-uf {z}
        with uf x ≟ uf z
    ... | yes xz
        with uf x ≟ uf (uf y)
    ... | yes xy = refl
    ... | no xy = idem-uf {y}
    union-idem {x}{y}{uf} idem-uf {z} | no xz
        with uf x ≟ uf (uf z)
    ... | yes xz' = ⊥-elim (xz (trans xz' (idem-uf {z})))
    ... | no xz' = idem-uf {z}

  union x y ⟨ uf , idem ⟩ = ⟨ union-fun x y uf , union-idem idem ⟩
```

```
  union-find-left : ∀ {x y : ℕ}{uf : UnionFind}
      → find (union x y uf) x ≡ find uf y
  union-find-left {x}{y}{uf}  
      with (proj₁ uf) x ≟ (proj₁ uf) x
  ... | yes xx = refl
  ... | no xx = ⊥-elim (xx refl)
```

```
  union-find-right : ∀ {x y : ℕ}{uf : UnionFind}
      → find (union x y uf) y ≡ find uf y
  union-find-right {x}{y}{uf} 
      with (proj₁ uf) x ≟ (proj₁ uf) y
  ... | yes xuy = refl
  ... | no xuy = refl
```

```
  union-find-remap : ∀ {x y z : ℕ}{uf : UnionFind}
      → find uf z ≡ find uf x
      → find (union x y uf) z ≡ find uf y
  union-find-remap {x}{y}{z}{uf} zu=xu
      with (proj₁ uf) x ≟ (proj₁ uf) z
  ... | yes xuy = refl
  ... | no xuy = ⊥-elim (xuy (sym zu=xu))
```

```
  union-find-stable : ∀ {x y z : ℕ}{uf : UnionFind}
      → find uf z ≢ find uf x
      → find (union x y uf) z ≡ find uf z
  union-find-stable {x}{y}{z}{uf} ¬zu=xu
      with (proj₁ uf) x ≟ (proj₁ uf) z
  ... | yes xuy = ⊥-elim (¬zu=xu (sym xuy))
  ... | no xuy = refl
```

```
  union-find-idempotent : ∀{uf x}
     → find uf (find uf x) ≡ find uf x
  union-find-idempotent {⟨ f , idem ⟩} {x} = idem
```
