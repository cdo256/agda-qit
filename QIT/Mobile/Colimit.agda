{-# OPTIONS --type-in-type #-}
module QIT.Mobile.Colimit (B : Set) where

open import QIT.Prelude
open import QIT.Relation.Binary
open import QIT.Mobile.Base B
open import QIT.Mobile.Equivalence B
open import QIT.Setoid as ≈
open import Data.Product
open import Data.Empty renaming (⊥-elim to absurd)
open import Data.W
open import Data.Container hiding (_⇒_; identity; refl; sym; trans)
open import Data.Unit
open import Data.Sum
open import QIT.Relation.Plump Branch
open import QIT.Colimit ≤p
open import QIT.Relation.Subset
open import QIT.Relation.Binary

private
  l0 : Level
  l0 = lzero

P₀ : (i : BTree) → Set l0
P₀ i = ΣP BTree (_< i)

t≮l : ∀ t {f} → t < sup (l , f) → ⊥p
t≮l t (<sup () _)

perm : ∀ i → (f : B → BTree) (p : sup (n , f) < i)
      → (π : B ↔ B)→ P₀ i
perm i f p π = sup (n , g) , g<i
  where
  open _↔_ π renaming (to to π'; from to π⁻¹)
  g : B → BTree
  g b = f (π' b) 
  g≤f : sup (n , g) ≤ sup (n , f)
  g≤f = sup≤ λ b → <sup (π' b) (≤refl (g b))
  g<i : sup (n , g) < i
  g<i = <≤ p g≤f

injP' : ∀ {α} b → P₀ (α b) → P₀ (sup (n , α))
injP' b (x , x<αb) = x , <sup b (<→≤ x<αb)

-- infix 5 _≈ᶻ_
-- data _≈ᶻ_ {i : BTree} : (s t : P₀ i) → Prop where
--   ≈zleaf : ∀ {f} (p q : sup (l , f) < i)
--           → (sup (l , f) , p) ≈ᶻ (sup (l , f) , q)
--   ≈znode : ∀ (f g : B → BTree)
--          → (p : ∀ b → f b < i)
--          → (q : ∀ b → g b < i)
--          → (eq : ∀ b → (f b , p b) ≈ᶻ (g b , q b))
--          → (sup (n , f) , {!!}) ≈ᶻ {!!}
--   ≈zperm : ∀ {f p} → (π : B ↔ B)
--          →  sup (n , f) , p
--          ≈ᶻ perm i f p π
--   ≈ztrans : ∀ {s t u} → s ≈ᶻ t → t ≈ᶻ u → s ≈ᶻ u


infix 5 _⊢_≈ᶻ_
data _⊢_≈ᶻ_ : (i : BTree) (s t : P₀ i) → Prop where
  ≈zleaf : ∀ {i} {f} (p q : sup (l , f) < i)
          → i ⊢ (sup (l , f) , p) ≈ᶻ (sup (l , f) , q)
  -- ≈znode : ∀ {α} b (s t : P₀ (α b))
  --        → (eq : α b ⊢ s ≈ᶻ t)
  --        → sup (n , α) ⊢ injP b s ≈ᶻ injP b t
  ≈zcong : ∀ {α f g p q}
         → (fb<αb : ∀ b → f b < α b)
         → (gb<αb : ∀ b → g b < α b)
         → (_ : ∀ b → α b ⊢ (f b , fb<αb b) ≈ᶻ (g b , gb<αb b))
         → sup (n , α) ⊢  (sup (n , f) , p)
                       ≈ᶻ (sup (n , g) , q)
  ≈zperm : ∀ {i f p} → (π : B ↔ B)
         → i ⊢  sup (n , f) , p
            ≈ᶻ perm i f p π
  ≈ztrans : ∀ {i s t u} → i ⊢ s ≈ᶻ t → i ⊢ t ≈ᶻ u → i ⊢ s ≈ᶻ u


-- ≡→≈ᶻ : ∀ {i} s t
--         → {p : s < i} {q : t < i}
--         → s ≡ t
--         → _≡_ {A = P₀ i} (s , p)  (t , q)
-- ≡→≈ᶻ {i} s t {p = p} {q = q} = ΣP≡ (s , p) (t , q)


injP : ∀ {i j} (s : P₀ i) → i ≤ j → P₀ j
injP (s , s<i) i≤j = s , ≤< i≤j s<i

-- inj≈ᶻ : ∀ {i j} s t (p : s < i) (q : t < i)
--       → i ⊢ (s , p) ≈ᶻ (t , q)


≡→≈ᶻ : ∀ {i} s (p : s < i)
     → i ⊢ (s , p) ≈ᶻ (s , p)
≡→≈ᶻ s p = {!!}

-- ≡→≈ᶻ : ∀ {i} s t
--      → {p : s < i} {q : t < i}
--      → s ≡ t
--      → i ⊢ (s , p) ≈ᶻ (t , q)
-- ≡→≈ᶻ {sup (l , _)} s t {p} = absurdp (t≮l s p)
-- ≡→≈ᶻ {sup (n , α)} (sup (l , f)) (sup (l , f)) {p} {q} ≡.refl =
--   ≈zleaf p q
-- ≡→≈ᶻ {sup (n , α)} (sup (n , f)) (sup (n , f)) {p} {q} ≡.refl =
--   ≈zcong lt lt λ b → {!!}
--   where
--   lt : ∀ b → f b < α b
--   lt b = {!!}

-- -- ≡→≈ᶻ {sup (n , α)} (sup (n , f)) (sup (n , f)) {<sup bp (sup≤ p)} {<sup bq (sup≤ q)} ≡.refl = {!!}
-- --   -- ≈znode α (λ i → {!!} , {!!}) {!!} λ b → {!!}

-- ≈zrefl : ∀ i t → i ⊢ t ≈ᶻ t
-- ≈zrefl i (sup (l , f) , p) = substp (λ ○ → {!!} ) {!!} ≈zleaf
-- ≈zrefl i (sup (n , f) , p) = {!!}

-- P : (i : BTree) → Setoid l0 l0
-- P i = record
--   { Carrier = P₀ i
--   ; _≈_ = i ⊢_≈ᶻ_
--   ; isEquivalence = {!!} }

  
-- -- -- Sz : BTree → Setoid l0 l0
-- -- -- Sz t .Setoid.Carrier = P₀ t
-- -- -- Sz t@(sup (γ , h)) .Setoid._≈_ (sz (sup (α , f)) sf<t@(<sup c d)) (sz (sup (β , g)) sg<t) = _≈ᵗ_ (Sz t) (α , λ b → sz (f b) {!<sup {!!} {!!}!}) ({!!} , {!!})
-- -- -- Sz t .Setoid.isEquivalence = {!!}


-- -- -- Sz : BTree → Setoid l0 l0
-- -- -- Sz t = record
-- -- --   { Carrier = Sz₀ t
-- -- --   ; _≈_ = λ (sz u _) (sz s _) → u ≈' s
-- -- --   ; isEquivalence = {!!} } --record
-- -- --     -- { refl = ≈refl
-- -- --     -- ; sym = ≈sym
-- -- --     -- ; trans = ≈trans } }
-- -- --   where
-- -- --     _≈'_ : (a b : BTree) → Prop
-- -- --     sup (l , _) ≈' sup (l , _) = _≈ᵗ_ (Sz t) (l , λ ()) (l , λ ())
-- -- --     sup (l , _) ≈' sup (n , g) = _≈ᵗ_ (Sz t) (l , λ ()) (n , λ b → {!sz ? ?!})
-- -- --     sup (n , f) ≈' sup (l , _) = {!!}
-- -- --     sup (n , f) ≈' sup (n , g) = {!!}
-- -- --     -- data _≈'_ (a b : BTree) : Prop where
-- -- --     --   w : ∀ (a b : F̃-ob₀ (Sz t)) → _≈ᵗ_ (Sz t) a b → {!a ≈' b!}

-- -- -- P : ∀ {t u} → u ≤ t → ≈.Hom (Sz u) (Sz t)
-- -- -- P {t} {u} u≤t = record
-- -- --   { ⟦_⟧ = λ (sz s s<u) → sz s (≤< u≤t s<u)
-- -- --   ; cong = λ s≈u → s≈u }

-- -- -- module ≤ = IsPreorder isPreorder-≤

-- -- -- Id : ∀ {t : BTree}
-- -- --     → ≈.Hom≈ (P (≤refl t)) ≈.idHom 
-- -- -- Id p = p

-- -- -- Comp : ∀{s t u} (p : s ≤ t) (q : t ≤ u)
-- -- --       → ≈.Hom≈ (P (≤.trans p q)) (P q ≈.∘ P p)   
-- -- -- Comp _ _ r = r

-- -- -- D : Diagram
-- -- -- D = record
-- -- --   { D-ob = Sz
-- -- --   ; D-mor = P
-- -- --   ; D-id = λ {i} {x} {y} → Id {i} {x} {y}
-- -- --   ; D-comp = Comp }

-- -- -- open Colim D
