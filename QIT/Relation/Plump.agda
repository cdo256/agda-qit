open import QIT.Prelude
open import QIT.Relation.Binary
open import QIT.Container.Base

module QIT.Relation.Plump {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) where

data Sᶻ : Set ℓS where
  ⊥ˢ : Sᶻ
  ∨ˢ : Sᶻ
  ιˢ : S → Sᶻ

Pᶻ : Sᶻ → Set ℓP
Pᶻ ⊥ˢ = ⊥*
Pᶻ ∨ˢ = Lift ℓP (⊤ ⊎ ⊤)
Pᶻ (ιˢ s) = P s

-- From Fiore et al. 2022
Z : Set (ℓS ⊔ ℓP)
Z = W Sᶻ Pᶻ

⊥ᶻ : Z
⊥ᶻ = sup (⊥ˢ , λ ())

sucᶻ : Z → Z
sucᶻ α = sup (∨ˢ , λ _ → α)

_∨ᶻ_ : Z → Z → Z
_∨ᶻ_ α β = sup (∨ˢ , f)
  where
  f : Pᶻ ∨ˢ → W Sᶻ Pᶻ
  f (lift (inj₁ tt)) = α
  f (lift (inj₂ tt)) = β

ιᶻ : W S P → Z
ιᶻ (sup (s , f)) = sup (ιˢ s , λ i → ιᶻ (f i))

-- The well-founded order (<) on Z
mutual
  infix 4 _≤_ _<_
  data _≤_ : Z → Z → Prop (ℓS ⊔ ℓP) where
    sup≤ :
      {s   : Sᶻ}
      {f   : Pᶻ s → Z}
      {i   : Z}
      (f<i : ∀ x → f x < i)
      → ---------------------
      sup (s , f) ≤ i
  data _<_ : Z → Z → Prop (ℓS ⊔ ℓP) where
    <sup :
      {a    : Sᶻ}
      {f    : Pᶻ a → Z}
      (x    : Pᶻ a)
      {i    : Z}
      (i≤fx : i ≤ f x)
      → ----------------------
      i < sup (a , f)

≤refl : ∀ i → i ≤ i
≤refl (sup (_ , f)) = sup≤ (λ x → <sup x (≤refl (f x)))

mutual
  ≤≤ : {i j k : Z} → j ≤ k → i ≤ j → i ≤ k
  ≤≤ j≤k (sup≤ f<i) = sup≤ λ x → ≤< j≤k (f<i x)

  ≤< : {i j k : Z} → j ≤ k → i < j → i < k
  ≤< (sup≤ f<i) (<sup x i≤fx) = <≤ (f<i x) i≤fx

  <≤ : {i j k : Z} → j < k → i ≤ j → i < k
  <≤ (<sup x i≤fx) i≤j = <sup x (≤≤ i≤fx i≤j)

<→≤ : ∀{i j} → i < j → i ≤ j
<→≤ (<sup x (sup≤ f<i)) = sup≤ (λ y → <sup x (<→≤ (f<i y)))

<supᶻ : ∀ {s} x → ∥ P s ∥ → x < sup (ιˢ s , λ _ → x)
<supᶻ x ∣ i ∣ = <sup i (≤refl x)

<sucᶻ : ∀ α → α < sucᶻ α
<sucᶻ = λ α → <sup (lift (inj₁ tt)) (≤refl α)

_<ᵀ_ : (W S P) → Z → Prop (ℓS ⊔ ℓP)
t <ᵀ α = ιᶻ t < α

_≤ᵀ_ : (W S P) → Z → Prop (ℓS ⊔ ℓP)
t ≤ᵀ α = ιᶻ t ≤ α

<< : ∀{i j k} → j < k → i < j → i < k
<< (<sup x i≤fx) i<j = <sup x (<→≤ (≤< i≤fx i<j))

fi≤sup : ∀ s f i → f i ≤ sup (s , f)
fi≤sup s f i = <→≤ (<sup i (≤refl (f i)))

iswf< : WellFounded _<_
iswf< i = acc λ j j<i → α i j (<→≤ j<i)
  where
  α : ∀ i j → j ≤ i → Acc _<_ j
  α (sup (_ , f)) j j≤i = acc α'
    where
    α' : WfRec _<_ (Acc _<_) j
    α' k k<j with ≤< j≤i k<j
    ... | <sup x k≤fx = α (f x) k k≤fx

isPreorder-≤ : IsPreorder _≤_
isPreorder-≤ = record
  { refl = λ {x} → ≤refl x
  ; trans = λ p q → ≤≤ q p }

≤p : Preorder (W Sᶻ Pᶻ) _
≤p = _≤_ , isPreorder-≤

_⊆_ : Z → Z → Prop (ℓS ⊔ ℓP)
i ⊆ j = ∀ k → k < i → k < j

_⊇_ : Z → Z → Prop (ℓS ⊔ ℓP)
i ⊇ j = ∀ k → i < k → j < k

⊆→≤ : ∀ {i j} → i ⊆ j → i ≤ j
⊆→≤ {sup (s , f)} {sup (t , g)} p =
  sup≤ (λ x → p (f x) (<sup x (≤refl (f x))))

≤→⊆ : ∀ {i j} → i ≤ j → i ⊆ j
≤→⊆ {sup (s , f)} {sup (t , g)} sf≤tg =
  λ k k<sf → ≤< sf≤tg k<sf

≤→⊇ : ∀ {i j} → i ≤ j → j ⊇ i
≤→⊇ i≤j _ j<k = <≤ j<k i≤j

_≤≥_ : ∀ (x y : W Sᶻ Pᶻ) → Prop (ℓS ⊔ ℓP)
x ≤≥ y = (x ≤ y) ∧ (y ≤ x)
_⊆⊇_ : ∀ (x y : W Sᶻ Pᶻ) → Prop (ℓS ⊔ ℓP)
x ⊆⊇ y = (x ⊆ y) ∧ (y ⊆ x)

isQuasiExtensionalZ : ∀ {x y} → (x ≤≥ y) ⇔ (x ⊆⊇ y)
isQuasiExtensionalZ = (λ (i≤j , j≤i) → ≤→⊆ i≤j , ≤→⊆ j≤i) , λ (i⊆j , j⊆i) → ⊆→≤ i⊆j , ⊆→≤ j⊆i

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

⊥≤t : ∀ α → ⊥ᶻ ≤ α
⊥≤t _ = sup≤ λ ()
