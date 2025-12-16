module Mobile where

open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
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
open import Relation.Binary.Structures


private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level


-- A wrapper to lift Prop into Set
record Box {ℓ} (P : Prop ℓ) : Set ℓ where
  constructor box
  field unbox : P

open Box


substp : ∀ {A : Set ℓ} (B : A → Prop ℓ') {a1 a2 : A} (p : a1 ≡ a2) → B a1 → B a2
substp B p x = subst (λ x → Box (B x)) p (box x) .unbox



module Mobile (B : Set ℓ) where
  data BTree (B : Set ℓ) : Set ℓ where
    leaf : BTree B
    node : (f : B → BTree B) → BTree B

  open import Data.Unit
  open import Data.Sum

  BTreeCont : Container lzero ℓ
  BTreeCont .Shape = ⊤ ⊎ ⊤
  BTreeCont .Position (inj₁ tt) = Lift ℓ ⊥
  BTreeCont .Position (inj₂ tt) = B

  tree→w : BTree B → W BTreeCont
  tree→w leaf = sup (inj₁ tt , λ())
  tree→w (node f) = sup (inj₂ tt , (λ b → tree→w (f b)))

  w→tree : W BTreeCont → BTree B
  w→tree (sup (inj₁ tt , _)) = leaf
  w→tree (sup (inj₂ tt , f)) = node λ b → w→tree (f b)



  Bˢ : Setoid ℓ ℓ
  Bˢ = ≡.setoid B
  open Inverse renaming (inverse to inverse')
  data _≈ᵗ_ : BTree B → BTree B → Set ℓ where
    ≈leaf : leaf ≈ᵗ leaf
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
    { Carrier = BTree B
    ; _≈_ = _≈ᵗ_
    ; isEquivalence = isEquiv-≈ᵗ }

  open import Plump BTreeCont
    renaming (_≺_ to _<ᵖ_; _≤_ to _≤ᵖ_; <≤ to <≤ᵖ; ≤< to ≤<ᵖ; ≤≤ to ≤≤ᵖ;
              ≤refl to ≤reflᵖ; ≺sup to <supᵖ; sup≤ to sup≤ᵖ)
  _<_ : BTree B → BTree B → Prop ℓ
  s < t = tree→w s <ᵖ tree→w t
  _≤_ : BTree B → BTree B → Prop ℓ
  s ≤ t = tree→w s ≤ᵖ tree→w t
  <→<ᵖ : ∀ {s t} → s < t → tree→w s <ᵖ tree→w t
  <→<ᵖ p = p
  ≤→≤ᵖ : ∀ {s t} → s ≤ t → tree→w s ≤ᵖ tree→w t
  ≤→≤ᵖ p = p
  ≤≤ : {s t u : BTree B} → t ≤ u → s ≤ t → s ≤ u
  ≤≤ p q = ≤≤ᵖ p q
  <≤ : {s t u : BTree B} → t < u → s ≤ t → s < u
  <≤ p q = <≤ᵖ p q
  ≤< : {s t u : BTree B} → t ≤ u → s < t → s < u
  ≤< p q = ≤<ᵖ p q
  ≤refl : ∀ {s} → s ≤ s
  ≤refl {s} = ≤reflᵖ (tree→w s)
  _≤ᴮ_ : BTree B → BTree B → Set ℓ
  _≤ᴮ_ s t = Box (s ≤ t)

  leaf≉node : ∀ {f} → leaf ≈ᵗ node f → ⊥
  leaf≉node (≈trans {t = leaf} p q) = leaf≉node q
  leaf≉node (≈trans {t = node _} p q) = leaf≉node p


  open import Relation.Binary.Core
  ≤-resp-≈ᵗ : _≈ᵗ_ ⇒ _≤ᴮ_
  ≤-resp-≈ᵗ {leaf} {leaf} p = box (≤refl {leaf})
  ≤-resp-≈ᵗ {leaf} {node f} p = absurd (leaf≉node p)
  ≤-resp-≈ᵗ {node f} {leaf} p = absurd (leaf≉node (≈sym p))
  ≤-resp-≈ᵗ {node f} {node g} (≈node c) .unbox =
    sup≤ᵖ λ b → <supᵖ b (unbox (≤-resp-≈ᵗ (c b)))
  ≤-resp-≈ᵗ {node f} {node g} (≈perm π) .unbox =
    sup≤ᵖ (λ b → <supᵖ (π .from b) (u b))
    where
    u : ∀ b → (f b) ≤ (f (π .to (π .from b))) 
    u b = substp (λ x → f b ≤ f x) p ≤refl
      where
      p = ≡.sym (inverseˡ π {x = b} {y = π .from b} ≡.refl)
  ≤-resp-≈ᵗ {node f} {node g} (≈trans {t = t} p q) .unbox =
    ≤≤ {s = node f} {t = t} {u = node g}
       (≤-resp-≈ᵗ q .unbox) (≤-resp-≈ᵗ p .unbox)

  isPreorder-≤ : IsPreorder _≈ᵗ_ _≤ᴮ_
  isPreorder-≤ = record
    { isEquivalence = isEquiv-≈ᵗ
    ; reflexive = ≤-resp-≈ᵗ
    ; trans = λ p q → box (≤≤ (q .unbox) (p .unbox)) }

  record Sz₀ (t : BTree B) : Set ℓ where
    constructor sz
    field
      u : BTree B
      u<t : u < t

  Sz : BTree B → Setoid ℓ ℓ
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

  Id : ∀ {t : BTree B}
     → _≈⃗_ (Sz t) (Sz t)
            (P' (box ≤refl)) 
            (identity (Sz t))
  Id {leaf} (sz u u<t) = {!!}
  Id {node f} (sz u u<t) = {!!}

  D : Diagram isPreorder-≤ B
  D = record
    { D-ob = Sz
    ; D-mor = P'
    ; D-id = Id
    ; D-comp = {!!} }

