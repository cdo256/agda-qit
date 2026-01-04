open import QIT.Prelude
open import QIT.Relation.Binary
open import QIT.Container

open import Data.Product
open import Data.Sum
open import Data.Unit

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
sucᶻ α = sup (⊥ˢ , λ _ → α)

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

_<ᵀ_ : (W S P) → Z → Prop (ℓS ⊔ ℓP)
t <ᵀ α = ιᶻ t < α

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
