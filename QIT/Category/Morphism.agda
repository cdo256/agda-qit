open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Subset
open import QIT.Setoid hiding (_≅_)
open import QIT.Relation.Binary
open import QIT.Relation.Base
open import QIT.Category.Base

module QIT.Category.Morphism
       {ℓCo} {ℓCh} {ℓCe}
       (C : Category ℓCo ℓCh ℓCe)
       where
open Category C

record IsIso {x y} (f : C [ x , y ]) : Set (ℓCh ⊔ ℓCe) where
  field
    f⁻¹ : C [ y , x ]
    linv : f⁻¹ ∘ f ≈ id
    rinv : f ∘ f⁻¹ ≈ id

record Iso (x y : Obj) : Set (ℓCh ⊔ ℓCe) where
  field
    f : C [ x , y ]
    f⁻¹ : C [ y , x ]
    linv : f⁻¹ ∘ f ≈ id
    rinv : f ∘ f⁻¹ ≈ id

_≅_ : ∀ x y → Prop (ℓCh ⊔ ℓCe)
x ≅ y = ∥ Iso x y ∥

IsIso→Iso : ∀ {x y} {f : C [ x , y ]} → IsIso f → Iso x y
IsIso→Iso {x} {y} {f} isIso = record
  { f = f
  ; f⁻¹ = f⁻¹
  ; linv = linv
  ; rinv = rinv }
  where
  open IsIso isIso

isEquivalenceIso : IsEquivalence _≅_
isEquivalenceIso = record
  { refl = isReflexive
  ; sym = isSymmetric
  ; trans = isTransitive
  }
  where
  -- Every setoid is isomorphic to itself via identity functions
  isReflexive : Reflexive _≅_
  isReflexive {S} = ∣ p ∣
    where
    p : Iso S S
    p = record { f = id ; f⁻¹ = id ; linv = identityˡ ; rinv = identity² }

  -- If S ≅ T then T ≅ S by flipping the isomorphism
  isSymmetric : Symmetric _≅_
  isSymmetric {S} {T} ∣ p ∣ = ∣ q ∣
    where
    module p = Iso p
    q : Iso T S
    q = record { f = p.f⁻¹ ; f⁻¹ = p.f ; linv = p.rinv ; rinv = p.linv }

  -- Composition of isomorphisms: if S ≅ T and T ≅ U then S ≅ U
  isTransitive : Transitive _≅_
  isTransitive {S} {T} {U} ∣ p ∣ ∣ q ∣ = ∣ r ∣
    where
    module p = Iso p
    module q = Iso q
    open ≈.≈syntax {S = hom-setoid}
    linv : (p.f⁻¹ ∘ q.f⁻¹) ∘ q.f ∘ p.f ≈ id
    linv =
      (p.f⁻¹ ∘ q.f⁻¹) ∘ (q.f ∘ p.f)
        ≈⟨ assoc ⟩
      p.f⁻¹ ∘ (q.f⁻¹ ∘ (q.f ∘ p.f))
        ≈⟨ ∘-resp-≈ʳ sym-assoc ⟩
      p.f⁻¹ ∘ ((q.f⁻¹ ∘ q.f) ∘ p.f)
        ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ q.linv) ⟩
      p.f⁻¹ ∘ (id ∘ p.f)
        ≈⟨ ∘-resp-≈ʳ identityˡ ⟩
      p.f⁻¹ ∘ p.f
        ≈⟨ p.linv ⟩
      id ∎
    rinv : (q.f ∘ p.f) ∘ p.f⁻¹ ∘ q.f⁻¹ ≈ id
    ring = {!!}
    r : Iso S U
    r = record { f = q.f ∘ p.f ; f⁻¹ = p.f⁻¹ ∘ q.f⁻¹ ; linv = linv ; rinv = rinv }


--   -- The setoid of setoids: setoids form a setoid under isomorphism
--   IsoSetoid : Setoid (lsuc ℓ ⊔ lsuc ℓ') (ℓ ⊔ ℓ')
--   IsoSetoid = record
--     { Carrier = Setoid ℓ ℓ'
--     ; _≈_ = _≅_
--     ; isEquivalence = isEquivalenceIso
--     }


-- IsMonic : ∀ {x y} (f : C [ x , y ]) → Prop (ℓCo ⊔ ℓCh ⊔ ℓCe) 
-- IsMonic {x} {y} f = ∀ z (g h : C [ z , x ]) → (f ∘ g) ≈ (f ∘ h) → g ≈ h 

-- IsEpic : ∀ {x y} (f : C [ x , y ]) → Prop (ℓCo ⊔ ℓCh ⊔ ℓCe) 
-- IsEpic {x} {y} f = ∀ z (g h : C [ y , z ]) → (g ∘ f) ≈ (h ∘ f) → g ≈ h 
