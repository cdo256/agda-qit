open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Subset
open import QIT.Setoid.Base 
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

IsoFlip : ∀ {x y} → Iso x y → Iso y x
IsoFlip iso = record { f = f⁻¹ ; f⁻¹ = f ; linv = rinv ; rinv = linv }
  where
  open Iso iso

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
  -- Every object is isomorphic to itself via the identity morphism
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
    linv : (p.f⁻¹ ∘ q.f⁻¹) ∘ (q.f ∘ p.f) ≈ id
    linv =
      begin
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
      where open ≈syntax {S = hom-setoid}
    rinv : (q.f ∘ p.f) ∘ (p.f⁻¹ ∘ q.f⁻¹) ≈ id
    rinv =
      begin
      (q.f ∘ p.f) ∘ (p.f⁻¹ ∘ q.f⁻¹)
        ≈⟨ assoc ⟩
      q.f ∘ (p.f ∘ (p.f⁻¹ ∘ q.f⁻¹))
        ≈⟨ ∘-resp-≈ʳ sym-assoc ⟩
      q.f ∘ ((p.f ∘ p.f⁻¹) ∘ q.f⁻¹)
        ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ p.rinv) ⟩
      q.f ∘ (id ∘ q.f⁻¹)
        ≈⟨ ∘-resp-≈ʳ identityˡ ⟩
      q.f ∘ q.f⁻¹
        ≈⟨ q.rinv ⟩
      id ∎
      where open ≈syntax {S = hom-setoid}
    r : Iso S U
    r = record { f = q.f ∘ p.f ; f⁻¹ = p.f⁻¹ ∘ q.f⁻¹ ; linv = linv ; rinv = rinv }

IsoSetoid : Setoid _ _
IsoSetoid = record
  { Carrier = Obj
  ; _≈_ = _≅_
  ; isEquivalence = isEquivalenceIso
  }
