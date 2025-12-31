open import QIT.Prelude

module QIT.Mobile.Diagram (B : Set) (inhabB : ∥ B ∥) where

open import QIT.Relation.Binary
open import QIT.Mobile.Base B
open import QIT.Mobile.Functor B
open import QIT.Setoid as ≈
open import Data.Product
open import Data.Empty renaming (⊥-elim to absurd)
open import Data.W
open import Data.Unit
open import Data.Sum
open import QIT.Relation.Plump Branch
open import QIT.Relation.Subset
open import QIT.Diagram ≤p hiding (_≤_)

data P₀ : (i : BTree) → Set where
  leaf : ∀ α → P₀ (sup (n , α))
  node : ∀ α (f : (b : B) → P₀ (α b)) → P₀ (sup (n , α))
  weaken : ∀ i j → i ≤ j → P₀ i → P₀ j

n≰l : ∀ {f g} → ¬p (sup (n , f) ≤ sup (l , g))
n≰l {f} {g} (sup≤ f<l) = r inhabB
  where
  r : ∥ B ∥ → ⊥p
  r ∣ b ∣ with f<l b
  ... | <sup () i≤fx

𝟘 : BTree
𝟘 = sup (l , λ())
suc : BTree → BTree
suc x = sup (n , λ _ → x)

<suc : ∀ t → t < suc t
<suc t = f inhabB
  where
  f : ∥ B ∥ → t < suc t
  f ∣ b ∣ = <sup b (≤refl t)

𝟘≤t : ∀ t → 𝟘 ≤ t
𝟘≤t _ = sup≤ λ ()

t≤l→t≡l : ∀ {f} t → (_ : t ≤ sup (l , f)) → t ≡p sup (l , λ())
t≤l→t≡l {f} (sup (l , g)) p = ∣ (leaf≡leaf g λ ()) ∣
t≤l→t≡l {f} (sup (n , g)) p = absurdp (n≰l p)

¬Pl : ∀ {α} → (P₀ (sup (l , α))) → ⊥p
¬Pl (weaken (sup (l , _)) (sup (l , _)) _ t) = ¬Pl t
¬Pl (weaken (sup (n , _)) (sup (l , _)) p _) = n≰l p

⟦_⟧ : ∀ {i} → P₀ i → BTree
⟦ leaf α ⟧ = sup (l , λ ())
⟦ node α f ⟧ = sup (n , λ b → ⟦ f b ⟧)
⟦ weaken i j p s ⟧ = ⟦ s ⟧

_∘ᴾ_ : ∀ {α : B → BTree} (f : (b : B) → P₀ (α b)) (π : B ↔ B)
     → (b : B) → P₀ (α (π .↔.to b))
_∘ᴾ_ {α} f π = λ b → f (π .↔.to b)

data _≈ᴾ_ : ∀ {i j} → P₀ i → P₀ j → Prop where
  ≈pleaf : ∀ α β → leaf α ≈ᴾ leaf β
  ≈pnode : ∀ α β {f g} → (∀ b → f b ≈ᴾ g b) → node α f ≈ᴾ node β g
  ≈pperm : ∀ α {f} → (π : B ↔ B) → node α f ≈ᴾ node (α ∘ᵗ π) (f ∘ᴾ π)
  ≈pweaken : ∀ {i j} (p : i ≤ j) (s : P₀ i) → s ≈ᴾ weaken i j p s
  ≈psym : ∀ {i j} {s : P₀ i} {t : P₀ j} → s ≈ᴾ t → t ≈ᴾ s
  ≈ptrans : ∀ {i j k} {s : P₀ i} {t : P₀ j} {u : P₀ k} → s ≈ᴾ t → t ≈ᴾ u → s ≈ᴾ u

≈pweaken-cong : ∀ i j p → {s t : P₀ i} → s ≈ᴾ t → weaken i j p s ≈ᴾ weaken i j p t
≈pweaken-cong i j p s≈t =
  ≈ptrans (≈psym (≈pweaken p _)) (≈ptrans s≈t (≈pweaken p _))

≈prefl : ∀ {i} (s : P₀ i) → s ≈ᴾ s
≈prefl (leaf α) = ≈pleaf α α
≈prefl (node α f) = ≈pnode α α λ b → ≈prefl (f b)
≈prefl (weaken j i p s) = ≈pweaken-cong j i p (≈prefl s)

import QIT.Setoid.Indexed as Indexed

P : (i : BTree) → Setoid ℓ0 ℓ0
P i = record
  { Carrier = P₀ i
  ; _≈_ = _≈ᴾ_
  ; isEquivalence = record
    { refl = λ {x} → ≈prefl x
    ; sym = λ {x} {y} → ≈psym {i} {i} {x} {y}
    ; trans = λ {x} {y} {z} → ≈ptrans {i} {i} {i} {x} {y} {z} } }

Pᴵ : Indexed.Setoid ℓ0 ℓ0 ℓ0
Pᴵ = record
  { I = BTree
  ; A = P₀
  ; R = λ i j x y → x ≈ᴾ y
  ; isEquivalence = record
    { refl = λ {i} {x} → ≈prefl x
    ; sym = ≈psym
    ; trans = ≈ptrans } }

D : Diagram ℓ0 ℓ0
D = record
  { D-ob = P
  ; D-mor = Hom
  ; D-id = Id
  ; D-comp = Comp }
  where
  Hom : ∀ {i j} → i ≤ j → ≈.Hom (P i) (P j)
  Hom {i} {j} i≤j = record
    { to = weaken i j i≤j
    ; cong = ≈pweaken-cong i j i≤j }
  Id : ∀ {i} → (Hom (≤refl i)) ≈h ≈.idHom
  Id {i} p = ≈ptrans (≈psym (≈pweaken (≤refl i) _)) p
  Comp : ∀ {i j k} (p : i ≤ j) (q : j ≤ k) →
      Hom (≤≤ q p) ≈h (Hom q ≈.∘ Hom p)
  Comp {i} {j} {k} p q {x} {y} x≈y = begin
    weaken i k (≤≤ q p) x
      ≈⟨ ≈psym (≈pweaken (≤≤ q p) x) ⟩
    x
      ≈⟨ x≈y ⟩
    y
      ≈⟨ ≈pweaken p y ⟩
    weaken i j p y
      ≈⟨ ≈pweaken q (weaken i j _ y) ⟩
    weaken j k q (weaken i j p y) ∎
    where open Indexed.≈syntax Pᴵ
