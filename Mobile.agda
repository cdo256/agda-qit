module Mobile where

open import Prelude
open import Data.Product
open import Function.Bundles
open import Function.Definitions
open import Relation.Binary.PropositionalEquality as ≡
open import Axiom
open import Setoid as S
open import Function.Properties.Inverse 
open import Data.Empty renaming (⊥-elim to absurd)
open import Data.W
open import Data.Container hiding (_⇒_; identity)
-- open import Relation.Binary.Structures


private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level


module Mobile (B : Set ℓ) where
  open Box
  
  data NodeType : Set where
    l : NodeType
    n : NodeType

  open import Data.Unit
  open import Data.Sum

  Branch : Container lzero ℓ
  Branch .Shape = NodeType
  Branch .Position l = Lift ℓ ⊥
  Branch .Position n = B

  BTree = W Branch
  
  pattern leaf {f} = sup (l , f)
  pattern node f = sup (n , f)

  Bˢ : Setoid ℓ ℓ
  Bˢ = ≡.setoid B
  open Inverse renaming (inverse to inverse')
  data _≈ᵗ_ : BTree → BTree → Set ℓ where
    ≈leaf : ∀ {f g} → leaf {f} ≈ᵗ leaf {g}
    ≈node : ∀ {f g} → (c : ∀ b → f b ≈ᵗ g b)
          → node f ≈ᵗ node g
    ≈perm : ∀ {f} → (π : B ↔ B)
          → node f ≈ᵗ node λ b → f (π .to b)
    ≈trans : ∀ {s t u} → s ≈ᵗ t → t ≈ᵗ u → s ≈ᵗ u

  ≈refl : ∀ {t} → t ≈ᵗ t
  ≈refl {leaf} = ≈leaf
  ≈refl {node f} = ≈node λ b → ≈refl {f b}

  ≈sym : ∀ {s t} → s ≈ᵗ t → t ≈ᵗ s
  ≈sym ≈leaf = ≈leaf
  ≈sym (≈node c) = ≈node λ b → ≈sym (c b)
  ≈sym (≈perm {f} π) =
    subst
      (λ h → node (λ b → f (π .to b)) ≈ᵗ node λ b → f (h b))
      (funExt λ b → π .inverse' .proj₁ ≡.refl)
      (≈perm {f = λ b → f (π .to b)} (↔-sym π))
  ≈sym (≈trans s≈t t≈u) = ≈trans (≈sym t≈u) (≈sym s≈t)

  isEquiv-≈ᵗ : IsEquivalence _≈ᵗ_
  isEquiv-≈ᵗ = record
    { refl = ≈refl
    ; sym = ≈sym
    ; trans = ≈trans }

  MobileSetoid : Setoid ℓ ℓ
  MobileSetoid = record
    { Carrier = BTree
    ; _≈_ = _≈ᵗ_
    ; isEquivalence = isEquiv-≈ᵗ }

  open import Plump Branch
    renaming (_≺_ to _<_; ≺sup to <sup)
  _≤ᴮ_ : BTree → BTree → Set ℓ
  _≤ᴮ_ s t = Box (s ≤ t)

  leaf≉node : ∀ {f g} → leaf {g} ≈ᵗ node f → ⊥
  leaf≉node (≈trans {t = leaf} p q) = leaf≉node q
  leaf≉node (≈trans {t = node _} p q) = leaf≉node p

  open import Relation.Binary.Core
  leaf≤leaf : ∀ {f g} → leaf {f} ≤ leaf {g}
  leaf≤leaf = sup≤ (λ ())
  ≤-resp-≈ᵗ : _≈ᵗ_ ⇒ _≤ᴮ_
  ≤-resp-≈ᵗ {leaf {f}} {leaf {g}} p = box leaf≤leaf 
  ≤-resp-≈ᵗ {leaf} {node f} p = absurd (leaf≉node p)
  ≤-resp-≈ᵗ {node f} {leaf} p = absurd (leaf≉node (≈sym p))
  ≤-resp-≈ᵗ {node f} {node g} (≈node c) .unbox =
    sup≤ λ b → <sup b (unbox (≤-resp-≈ᵗ (c b)))
  ≤-resp-≈ᵗ {node f} {node g} (≈perm π) .unbox =
    sup≤ (λ b → <sup (π .from b) (u b))
    where
    u : ∀ b → (f b) ≤ (f (π .to (π .from b))) 
    u b = substp (λ x → f b ≤ f x) p (≤refl (f b))
      where
      p = ≡.sym (inverseˡ π {x = b} {y = π .from b} ≡.refl)
  ≤-resp-≈ᵗ {node f} {node g} (≈trans {t = t} p q) .unbox =
    ≤≤ {i = node f} {j = t} {k = node g}
       (≤-resp-≈ᵗ q .unbox) (≤-resp-≈ᵗ p .unbox)

  isPreorder-≤ : IsPreorder _≈ᵗ_ _≤ᴮ_
  isPreorder-≤ = record
    { isEquivalence = isEquiv-≈ᵗ
    ; reflexive = ≤-resp-≈ᵗ
    ; trans = λ p q → box (≤≤ (q .unbox) (p .unbox)) }

  record Sz₀ (t : BTree) : Set ℓ where
    constructor sz
    field
      u : BTree
      u<t : u < t

  Sz : BTree → Setoid ℓ ℓ
  Sz t = record
    { Carrier = Sz₀ t
    ; _≈_ = λ (sz u _) (sz s _) → u ≈ᵗ s
    ; isEquivalence = record
      { refl = ≈refl
      ; sym = ≈sym
      ; trans = ≈trans } }

  P : ∀ {t u} → u ≤ t → Func (Sz u) (Sz t)
  P {t} {u} u≤t = record
    { to = λ (sz s s<u) → sz s (≤< u≤t s<u)
    ; cong = λ s≈u → s≈u }

  P' : ∀ {t u} → u ≤ᴮ t → Func (Sz u) (Sz t)
  P' {t} {u} p = P {t} {u} (p .unbox)

  open import Colimit
  open import Function.Construct.Identity using () renaming (function to identity)

  module ≤ = IsPreorder isPreorder-≤

  Id : ∀ {t : BTree}
     → _≈⃗_ (Sz t) (Sz t)
            (P' (box (≤refl t))) 
            (identity (Sz t))
  Id (sz u u<t) = ≈refl

  Comp : ∀{s t u} (p : s ≤ᴮ t) (q : t ≤ᴮ u) → _≈⃗_ (Sz s) (Sz u)
         (P' (≤.trans p q)) (P' q ∘ P' p)   
  Comp (box w) (box v) (sz u u<t) = {!!}

  D : Diagram isPreorder-≤ B
  D = record
    { D-ob = Sz
    ; D-mor = P'
    ; D-id = Id
    ; D-comp = Comp }

