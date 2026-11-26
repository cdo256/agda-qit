open import QIT.Prelude hiding (ℓD)
open import QIT.Prop
open import QIT.Relation.SetQuotient
open import QIT.Relation.Binary

-- Diagrams over a transitive relation, without identity edges.
module QIT.SimpleDiagram
  ⦃ a!c* : A!C ⦄ 
  ⦃ pathElim* : PathElim ⦄
  ⦃ funExt* : FunExt ⦄
  ⦃ propExt* : PropExt ⦄
  ⦃ sq* : SetQuotients ⦄
  {ℓA ℓ<} {A : Set ℓA} (<p : WeakPreorder A ℓ<)
  where

private
  _<_ = <p .proj₁
module <p = IsWeakPreorder (<p .proj₂)

open FunExt funExt*

open import QIT.Setoid
open import QIT.Setoid.Quotient
open import QIT.Setoid.Hom 

open SQ

record Diagram≈ ℓD ℓD' : Set (ℓA ⊔ ℓ< ⊔ lsuc ℓD ⊔ lsuc ℓD') where
  open ≈
  field
    ob : A → Setoid ℓD ℓD'
    edge : ∀ {x y} → x < y → Hom (ob x) (ob y)
    nat : ∀ {x y z} → (p : x < y) → (q : y < z)
      → edge (<p.trans p q) ≈h (edge q ∘ edge p)


record Diagram ℓD : Set (ℓA ⊔ ℓ< ⊔ lsuc ℓD) where
  open ≈
  field
    ob : A → Set ℓD
    edge : ∀ {x y} → x < y → ob x → ob y
    nat : ∀ {x y z} → (p : x < y) → (q : y < z)
      → ∀ a → edge (<p.trans p q) a ≡ edge q (edge p a)

_/≈ᴰ : ∀ {ℓD ℓD'}
     → Diagram≈ ℓD ℓD'
     → Diagram (ℓD ⊔ ℓD')
D /≈ᴰ = record
  { ob = λ x → D.ob x /≈
  ; edge = edge
  ; nat = nat }
  where
  module D = Diagram≈ D
  open ≈.Hom
  edge : {x y : A} (p : x < y)
       → D.ob x /≈ → D.ob y /≈
  edge {x} {y} p =
    mapHom (D.ob x) (D.ob y) (D.edge p) 
  nat : ∀ {x y z} → (p : x < y) → (q : y < z)
    → ∀ a → edge (<p.trans p q) a ≡ edge q (edge p a)
  nat {x} {y} {z} p q =
    elimp (D.ob x)
          (λ a → edge (<p.trans p q) a ≡ edge q (edge p a))
          (λ a₀ → 
      edge (<p.trans p q) ([ D.ob x ] a₀)
        ≡⟨ mapHom-beta (D.ob x) (D.ob z) (D.edge (<p.trans p q)) a₀ ⟩
      D.ob z ⊢[ D.edge (<p.trans p q) .to a₀ ]
        ≡⟨ D.ob z ⊢≈[ D.nat p q ] ⟩
      D.ob z ⊢[ D.edge q .to (D.edge p .to a₀) ]
        ≡⟨ ≡.sym (mapHom-beta (D.ob y) (D.ob z) (D.edge q) (to (D.edge p) a₀)) ⟩
      edge q ([ D.ob y ] (to (D.edge p) a₀))
        ≡⟨ ≡.cong (edge q) (≡.sym (mapHom-beta (D.ob x) (D.ob y) (D.edge p) a₀)) ⟩
      edge q (edge p ([ D.ob x ] a₀)) ∎ )
      where open ≡-Reasoning

PowerSetoid : ∀ {ℓS ℓS' ℓX} → Setoid ℓS ℓS' → Set ℓX → Setoid (ℓS ⊔ ℓX) (ℓS' ⊔ ℓX)
PowerSetoid S X = record
  { Carrier = X → ⟨ S ⟩
  ; _≈_ = λ f g → ∀ x → f x ≈ g x
  ; isEquivalence = record
    { refl = λ _ → refl
    ; sym = λ p _ → sym (p _)
    ; trans = λ p q _ → trans (p _) (q _) } }
  where
  open Setoid S

PowerDiagram≈ : ∀ {ℓX ℓD ℓD'} → Diagram≈ ℓD ℓD' → Set ℓX
  → Diagram≈ (ℓD ⊔ ℓX) (ℓD' ⊔ ℓX)
PowerDiagram≈ D X = record
  { ob = λ i → PowerSetoid (D.ob i) X
  ; edge = λ p → record
    { to = λ f x → D.edge p .Hom.to (f x)
    ; cong = λ q x → D.edge p .Hom.cong (q x) }
  ; nat = λ p q x → D.nat p q }
  where module D = Diagram≈ D

PowerDiagram : ∀ {ℓX ℓD} → Diagram ℓD → Set ℓX → Diagram (ℓD ⊔ ℓX)
PowerDiagram D X = record
  { ob = λ i → X → D.ob i
  ; edge = λ p f x → D.edge p (f x)
  ; nat = λ p q f → funExt λ x → D.nat p q (f x) }
  where module D = Diagram D
