{-# OPTIONS --type-in-type #-}
module QIT.Mobile.Colimit2 (B : Set) (inhabB : B) where

open import QIT.Prelude
open import QIT.Relation.Binary
open import QIT.Mobile.Base B
open import QIT.Mobile.Equivalence B
open import QIT.Setoid as ≈
open import Data.Product
open import Data.Empty renaming (⊥-elim to absurd)
open import Data.W
-- open import Data.Container hiding (_⇒_; identity; refl; sym; trans; ⟦_⟧)
open import Data.Unit
open import Data.Sum
open import QIT.Relation.Plump Branch
import QIT.Colimit as C
open import QIT.Relation.Subset

private
  l0 : Level
  l0 = lzero

data P₀ : (i : BTree) → Set where
  leaf : ∀ α → P₀ (sup (n , α))
  node : ∀ α (f : (b : B) → P₀ (α b)) → P₀ (sup (n , α))
  weaken : ∀ i j → i ≤ j → P₀ i → P₀ j

n≰l : ∀ {f g} → ¬p (sup (n , f) ≤ sup (l , g))
n≰l {f} {g} (sup≤ f<l) with f<l inhabB
... | <sup () i≤fx

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


P : (i : BTree) → Setoid l0 l0
P i = record
  { Carrier = P₀ i
  ; _≈_ = _≈ᴾ_
  ; isEquivalence = record
    { refl = λ {x} → ≈prefl x
    ; sym = λ {x} {y} → ≈psym {i} {i} {x} {y}
    ; trans = λ {x} {y} {z} → ≈ptrans {i} {i} {i} {x} {y} {z} } }


-- -- Sz : BTree → Setoid l0 l0
-- -- Sz t .Setoid.Carrier = P₀ t
-- -- Sz t@(sup (γ , h)) .Setoid._≈_ (sz (sup (α , f)) sf<t@(<sup c d)) (sz (sup (β , g)) sg<t) = _≈ᵗ_ (Sz t) (α , λ b → sz (f b) {!<sup {!!} {!!}!}) ({!!} , {!!})
-- -- Sz t .Setoid.isEquivalence = {!!}


-- -- Sz : BTree → Setoid l0 l0
-- -- Sz t = record
-- --   { Carrier = Sz₀ t
-- --   ; _≈_ = λ (sz u _) (sz s _) → u ≈' s
-- --   ; isEquivalence = {!!} } --record
-- --     -- { refl = ≈refl
-- --     -- ; sym = ≈sym
-- --     -- ; trans = ≈trans } }
-- --   where
-- --     _≈'_ : (a b : BTree) → Prop
-- --     sup (l , _) ≈' sup (l , _) = _≈ᵗ_ (Sz t) (l , λ ()) (l , λ ())
-- --     sup (l , _) ≈' sup (n , g) = _≈ᵗ_ (Sz t) (l , λ ()) (n , λ b → {!sz ? ?!})
-- --     sup (n , f) ≈' sup (l , _) = {!!}
-- --     sup (n , f) ≈' sup (n , g) = {!!}
-- --     -- data _≈'_ (a b : BTree) : Prop where
-- --     --   w : ∀ (a b : F̃-ob₀ (Sz t)) → _≈ᵗ_ (Sz t) a b → {!a ≈' b!}

-- -- P : ∀ {t u} → u ≤ t → ≈.Hom (Sz u) (Sz t)
-- -- P {t} {u} u≤t = record
-- --   { ⟦_⟧ = λ (sz s s<u) → sz s (≤< u≤t s<u)
-- --   ; cong = λ s≈u → s≈u }

-- -- module ≤ = IsPreorder isPreorder-≤

-- -- Id : ∀ {t : BTree}
-- --     → ≈.Hom≈ (P (≤refl t)) ≈.idHom
-- -- Id p = p

-- -- Comp : ∀{s t u} (p : s ≤ t) (q : t ≤ u)
-- --       → ≈.Hom≈ (P (≤.trans p q)) (P q ≈.∘ P p)
-- -- Comp _ _ r = r

-- -- D : Diagram
-- -- D = record
-- --   { D-ob = Sz
-- --   ; D-mor = P
-- --   ; D-id = λ {i} {x} {y} → Id {i} {x} {y}
-- --   ; D-comp = Comp }

-- -- open Colim D
