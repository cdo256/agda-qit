{-# OPTIONS --injective-type-constructors #-}

open import QIT.Prelude
open import QIT.Prop
open import QIT.Container.Base
open import Data.Nat.Base hiding (_⊔_)

module QIT.Container.Properties where

module _ {ℓS ℓP} {S : Set ℓS} {P : S → Set ℓP} where
  getShape : W S P → S
  getShape (sup (s , _)) = s

  getChildren : (x : W S P) → (P (getShape x) → W S P)
  getChildren (sup (_ , f)) = f

  -- Recursor for W-types: fold over the tree structure.
  -- Given a way to combine a shape s with results from P s many subtrees,
  -- produce a result for the entire tree. This implements structural recursion.
  recW : ∀ {ℓX} {X : Set ℓX}
      → (r : ∀ s (f : P s → X) → X)
      → W S P → X
  recW r (sup (s , f)) = r s λ i → recW r (f i)

  data Path : W S P → Set (ℓS ⊔ ℓP) where
    here : ∀ x → Path x
    there : ∀ s f i → Path (f i) → Path (sup (s , f))

  pathLength : ∀ {x} → Path x → ℕ
  pathLength (here _) = 0
  pathLength (there _ _ _ p) = suc (pathLength p)

  pathLookup : ∀ {x} → Path x → W S P
  pathLookup (here x) = x
  pathLookup (there _ _ _ p) = pathLookup p

  recPath : ∀ {ℓA} (A : W S P → Set ℓA)
          → (rh : ∀ x → A x)
          → (rt : ∀ s (f : P s → W S P) i → A (f i) → A (sup (s , f)))
          → ∀ {x} → (p : Path x) → A x
  recPath A rh rt (here x) = rh x
  recPath A rh rt (there s f i p) = rt s f i (recPath A rh rt p)

  elimPath : ∀ {ℓA} (A : ∀ {x} → Path x → Set ℓA)
           → (rh : ∀ x → A (here x))
           → (rt : ∀ s (f : P s → W S P) i → (p : Path (f i)) → A p → A (there s f i p))
           → ∀ {x} → (p : Path x) → A p
  elimPath A rh rt (here x) = rh x
  elimPath A rh rt (there s f i p) = rt s f i p (elimPath A rh rt p)

  -- Extract child equality from sup equality
  sup-child-eq : ∀ {s s' : S} {f : P s → W S P} {f' : P s' → W S P}
               → (p : sup (s , f) ≡ sup (s' , f'))
               → (i : P s)
               → f i ≡ f' (subst P (≡.cong getShape p) i)
  sup-child-eq ≡.refl i = ≡.refl

-- -- Container morphisms: natural transformations between container functors.
-- -- A morphism (fs, fp) : (S ◁ P) → (S' ◁ P') maps shapes and positions
-- -- contravariantly, inducing a natural transformation ⟦ S ◁ P ⟧ → ⟦ S' ◁ P' ⟧.
-- module _ {ℓS ℓP ℓS' ℓP'} {S : Set ℓS} {S' : Set ℓS'} {P : S → Set ℓP} {P' : S' → Set ℓP'} where
--   -- Map container interpretation: transform shapes forward, positions backward
--   map : ∀ {ℓX} {X : Set ℓX} (fs : S → S') (fp : ∀ {s} → P' (fs s) → P s) → ⟦ S ◁ P ⟧ X → ⟦ S' ◁ P' ⟧ X
--   map fs fp (s , f) = fs s , λ i → f (fp i)

--   -- Induced map on W-types: container morphisms extend to W-type morphisms
--   mapW : (fs : S → S') (fp : ∀ {s} → P' (fs s) → P s) → W S P → W S' P'
--   mapW fs fp (sup (s , f)) = sup (fs s , λ i → mapW fs fp (f (fp i)))
