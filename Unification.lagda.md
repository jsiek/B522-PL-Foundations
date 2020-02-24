```
open import Data.Nat

module Unification (Op : Set) (sig : Op → ℕ) where
```

```
open import Relation.Nullary using (Dec; yes; no)
```

{-

  Union-find interface

-}

```
record UnionFind (A : Set) (UF : Set) : Set₁ where
  field
    union : A → A → UF → UF
    find : A → UF → A
    make-set : A → UF → UF
    init : UF
```


A very simple Union-Find data structures.

```
uf : UnionFind ℕ (ℕ → ℕ)
uf = record
    { union = union ;
      find = find ;
      make-set = make-set ;
      init = λ x → x }
    where
    union : ℕ → ℕ → (ℕ → ℕ) → (ℕ → ℕ)
    union x y uf z
        with x ≟ z
    ... | yes xz = uf y
    ... | no xz = uf z

    find : ℕ → (ℕ → ℕ) → ℕ
    find x uf = uf x
    
    make-set : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
    make-set x uf = uf
```
