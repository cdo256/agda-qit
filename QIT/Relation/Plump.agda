open import QIT.Prelude
open import QIT.Relation.Binary
open import QIT.Container.Base

-- Define plump ordinals Z of a given shape. They are used as size
-- bounds on trees for constructing diagrams, and then colimits.
-- This definition was copied from Fiore et al. 2022, and their earlier work (Pitts et al. 2021).
-- Start with an shape and position. This represents the 'shape' of
-- the underlying W-type being constructed.
module QIT.Relation.Plump {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) where

private
  T = W S P

-- We extend it to have 'enough' points:
--  - ⊥ˢ is the shape for a global minimum (P ⊥ˢ ≅ ⊥).
--  - ∨ˢ is the shape for a join operation (P ∨ˢ ≅ 𝟚).
--  - ιˢ s is the shape inlcusion for any shape S.

-- ⊥ˢ is required because we need to know that the tree isn't empty,
-- and we can't determine that for an arbitrary W type. It is an
-- algebraic convenience, and not strictly necessary.
-- ∨ˢ is required for congruence on ψ in cocontinuity, since we need
-- to be able to join two ordinals to a greater ordinal.

-- It is not required that the set of ordinals exactly follow the
-- shape of the W type, they just have to have 'enough' brancing
-- structure to have a natural injection from T to allow for
-- bounding and construction of stage sets.
data Sᶻ : Set ℓS where
  ⊥ˢ : Sᶻ
  ∨ˢ : Sᶻ
  ιˢ : S → Sᶻ

-- Lifting is required, since we want all positions to be at the same
-- level.
Pᶻ : Sᶻ → Set ℓP
Pᶻ ⊥ˢ = Lift _ ⊥
Pᶻ ∨ˢ = Lift _ (⊤ ⊎ ⊤)
Pᶻ (ιˢ s) = P s

Z : Set (ℓS ⊔ ℓP)
Z = W Sᶻ Pᶻ

⊥ᶻ : Z
⊥ᶻ = sup (⊥ˢ , λ ())

sucᶻ : Z → Z
sucᶻ α = sup (∨ˢ , λ _ → α)

-- Define branching.
-- Note that both α and β are strictly less than α ∨ᶻ β, not less or
-- equal, so this is not strictly a least upper bound.
_∨ᶻ_ : Z → Z → Z
_∨ᶻ_ α β = sup (∨ˢ , f)
  where
  f : Pᶻ ∨ˢ → W Sᶻ Pᶻ
  f (lift (inj₁ tt)) = α
  f (lift (inj₂ tt)) = β

-- Inclusion from the base W type, T, to plump ordinals Z
-- We just recurse over the tree and map each shape s to ιˢ s.
ιᶻ : T → Z
ιᶻ (sup (s , f)) = sup (ιˢ s , λ α → ιᶻ (f α))

-- Define a well-founded order (≤, <) on Z to be 'quasi-extensional'
-- (defined later in this file). We defile ≤ and < mutually
-- inductively using two rules defined below:
mutual
  infix 4 _≤_ _<_
  -- sup≤ states that whenever ∀ α. f α < β, then sup f ≤ β
  -- This gives us 'one-step quasi-extensionality'.
  data _≤_ : Z → Z → Prop (ℓS ⊔ ℓP) where
    sup≤ : {s : Sᶻ} {f : Pᶻ s → Z}
         → {α : Z} (f<α : ∀ β → f β < α)
         → sup (s , f) ≤ α
  -- <sup states that if ∃ α. β ≤ f α, then β < sup f
  -- This means that if any child is at least as large as some ordinal
  -- then the supremum is strictly larger.
  data _<_ : Z → Z → Prop (ℓS ⊔ ℓP) where
    <sup : {s : Sᶻ} {f : Pᶻ s → Z}
         → (β : Pᶻ s) {α : Z}
         → (α≤fi : α ≤ f β)
         → α < sup (s , f)

-- Reflexivity is obtained recursively using <sup followed by sup≤, a
-- common pattern reused several times.
≤refl : ∀ α → α ≤ α
≤refl (sup (_ , f)) = sup≤ (λ i → <sup i (≤refl (f i)))

-- Mutually define three notions of transitivity.
-- These must be mutual as each transitivity statement must either
-- expand a branch...
mutual
  ≤≤ : {α β γ : Z} → β ≤ γ → α ≤ β → α ≤ γ
  ≤≤ β≤γ (sup≤ f<α) = sup≤ λ i → ≤< β≤γ (f<α i)

  ≤< : {α β γ : Z} → β ≤ γ → α < β → α < γ
  ≤< (sup≤ f<α) (<sup i α≤fi) = <≤ (f<α i) α≤fi

  <≤ : {α β γ : Z} → β < γ → α ≤ β → α < γ
  <≤ (<sup i α≤fi) α≤β = <sup i (≤≤ α≤fi α≤β)

<→≤ : ∀{α β} → α < β → α ≤ β
<→≤ (<sup i (sup≤ f<β)) = sup≤ (λ j → <sup i (<→≤ (f<β j)))

<supᶻ : ∀ {s} x → ∥ P s ∥ → x < sup (ιˢ s , λ _ → x)
<supᶻ x ∣ α ∣ = <sup α (≤refl x)

<sucᶻ : ∀ α → α < sucᶻ α
<sucᶻ = λ α → <sup (lift (inj₁ tt)) (≤refl α)

_<ᵀ_ : (W S P) → Z → Prop (ℓS ⊔ ℓP)
t <ᵀ α = ιᶻ t < α

_≤ᵀ_ : (W S P) → Z → Prop (ℓS ⊔ ℓP)
t ≤ᵀ α = ιᶻ t ≤ α

<< : ∀{α β γ} → β < γ → α < β → α < γ
<< (<sup i β≤fi) β<γ = <sup i (<→≤ (≤< β≤fi β<γ))

fi≤sup : ∀ s f i → f i ≤ sup (s , f)
fi≤sup s f i = <→≤ (<sup i (≤refl (f i)))

iswf< : WellFounded _<_
iswf< α = acc λ β β<α → p α β (<→≤ β<α)
  where
  p : ∀ α β → β ≤ α → Acc _<_ β
  p (sup (_ , f)) β β≤α = acc q
    where
    q : WfRec _<_ (Acc _<_) β
    q γ γ<β with ≤< β≤α γ<β
    ... | <sup i γ≤fi = p (f i) γ γ≤fi

isPreorder-≤ : IsPreorder _≤_
isPreorder-≤ = record
  { refl = λ {x} → ≤refl x
  ; trans = λ p q → ≤≤ q p }

≤p : Preorder (W Sᶻ Pᶻ) _
≤p = _≤_ , isPreorder-≤

_⊆_ : Z → Z → Prop (ℓS ⊔ ℓP)
α ⊆ β = ∀ γ → γ < α → γ < β

_⊇_ : Z → Z → Prop (ℓS ⊔ ℓP)
α ⊇ β = ∀ γ → α < γ → β < γ

⊆→≤ : ∀ {α β} → α ⊆ β → α ≤ β
⊆→≤ {sup (s , f)} {sup (t , g)} p =
  sup≤ (λ x → p (f x) (<sup x (≤refl (f x))))

≤→⊆ : ∀ {α β} → α ≤ β → α ⊆ β
≤→⊆ {sup (s , f)} {sup (t , g)} sf≤tg =
  λ γ γ<sf → ≤< sf≤tg γ<sf

≤→⊇ : ∀ {α β} → α ≤ β → β ⊇ α
≤→⊇ α≤β _ β<γ = <≤ β<γ α≤β

_≤≥_ : ∀ (x y : W Sᶻ Pᶻ) → Prop (ℓS ⊔ ℓP)
x ≤≥ y = (x ≤ y) ∧ (y ≤ x)
_⊆⊇_ : ∀ (x y : W Sᶻ Pᶻ) → Prop (ℓS ⊔ ℓP)
x ⊆⊇ y = (x ⊆ y) ∧ (y ⊆ x)

isQuasiExtensionalZ : ∀ {x y} → (x ≤≥ y) ⇔ (x ⊆⊇ y)
isQuasiExtensionalZ = (λ (α≤β , β≤α) → ≤→⊆ α≤β , ≤→⊆ β≤α) , λ (α⊆β , β⊆α) → ⊆→≤ α⊆β , ⊆→≤ β⊆α

≤cong : ∀ s (μ τ : Pᶻ s → Z) → (r : ∀ i → μ i ≤ τ i)
      → sup (s , μ) ≤ sup (s , τ)
≤cong s μ τ r = sup≤ λ i → <sup i (r i)

∨ᶻ-l< : {α β : Z} → α < α ∨ᶻ β
∨ᶻ-l< {α} {β} = <sup (lift (inj₁ tt)) (≤refl α)

∨ᶻ-r< : {α β : Z} → β < α ∨ᶻ β
∨ᶻ-r< {α} {β} = <sup (lift (inj₂ tt)) (≤refl β)

∨ᶻ-l : {α β : Z} → α ≤ α ∨ᶻ β
∨ᶻ-l = fi≤sup ∨ˢ _ (lift (inj₁ tt))

∨ᶻ-r : {α β : Z} → β ≤ α ∨ᶻ β
∨ᶻ-r = fi≤sup ∨ˢ _ (lift (inj₂ tt))

∨ᶻ-flip : {α β : Z} → β ∨ᶻ α ≤ α ∨ᶻ β
∨ᶻ-flip {α} {β} = sup≤ g
  where
  g : (i : Pᶻ ∨ˢ) → _ < (α ∨ᶻ β)
  g (lift (inj₁ tt)) = <sup (lift (inj₂ tt)) (≤refl β)
  g (lift (inj₂ tt)) = <sup (lift (inj₁ tt)) (≤refl α)
