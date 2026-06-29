open import QIT.Prelude

module QIT.Relation.Ordinal ⦃ a!c* : A!C ⦄ where

open import QIT.Prelude
open import QIT.Relation.Subset
open import QIT.Relation.Base
open import QIT.Relation.Binary
-- open import QIT.Relation.Properties
-- open import QIT.Prop
-- -- open import QIT.Function.Base
-- -- open import QIT.Set.Base

-- -- -- record IsOrdinalStr {ℓA ℓ<} (A : Set ℓA) (_<_ : A → A → Prop ℓ<) : Prop (ℓA ⊔ ℓ<) where
-- -- --   field
-- -- --     trans : Transitive _<_
-- -- --     wf : WellFounded _<_
-- -- --     ext : ∀ {α β} → (∀ γ → γ < α ⇔ γ < β) → α ≡ β
-- -- --     total : ∀ {α β} → α < β ∨ α ≡ β ∨ β < α

-- -- -- record IsOrdinal {ℓA} ℓ< (A : Set ℓA) : Set (ℓA ⊔ lsuc ℓ<) where
-- -- --   constructor _,_
-- -- --   field
-- -- --     _<_ : A → A → Prop ℓ< 
-- -- --     isOrd : IsOrdinalStr A _<_
-- -- --   open IsOrdinalStr isOrd

-- -- -- Ordinal : ∀ ℓA ℓ< → Set (lsuc ℓA ⊔ lsuc ℓ<)
-- -- -- Ordinal ℓA ℓ< = Σ (Set ℓA) (IsOrdinal ℓ<)


-- -- -- zeroOrd : Ordinal ℓ0 ℓ0
-- -- -- zeroOrd = ⊥ , (λ ()) , isOrdZero
-- -- --   where
-- -- --   isOrdZero : IsOrdinalStr ⊥ (λ ())
-- -- --   isOrdZero = record
-- -- --     { trans = λ {}
-- -- --     ; wf = λ ()
-- -- --     ; ext = λ {}
-- -- --     ; total = λ {} }

-- -- -- sucOrd : ∀ {ℓA ℓ<} → Ordinal ℓA ℓ< → Ordinal ℓA ℓ<
-- -- -- sucOrd (A , _<_ , isOrd-A) = (A ⊎ ⊤) , _<'_ , isOrdSuc
-- -- --   where
-- -- --   _<'_ :  (A ⊎ ⊤) → (A ⊎ ⊤) → Prop _
-- -- --   inj₁ γ <' inj₁ δ = γ < δ
-- -- --   inj₁ γ <' inj₂ tt = ⊤p*
-- -- --   inj₂ tt <' inj₁ δ = ⊥p*
-- -- --   inj₂ tt <' inj₂ tt = ⊥p*
-- -- --   isOrdSuc : IsOrdinalStr (A ⊎ ⊤) _<'_
-- -- --   isOrdSuc = record
-- -- --     { trans = λ {γ δ ε} → <trans {γ} {δ} {ε} 
-- -- --     ; wf = <wf
-- -- --     ; ext = <ext
-- -- --     ; total = <total }
-- -- --     where
-- -- --     open IsOrdinalStr isOrd-A
-- -- --     <trans : Transitive _<'_
-- -- --     <trans {inj₁ γ} {inj₁ δ} {inj₁ ε} p q = trans p q
-- -- --     <trans {inj₁ γ} {inj₁ δ} {inj₂ tt} p q = q
-- -- --     liftAcc : ∀ {γ} → Acc _<_ γ → Acc _<'_ (inj₁ γ)
-- -- --     liftAcc {γ} (acc rs) =
-- -- --       acc λ where
-- -- --         (inj₁ δ) δ<γ → liftAcc (rs δ δ<γ)
-- -- --         (inj₂ tt) → λ ()
-- -- --     <wf : WellFounded _<'_
-- -- --     <wf (inj₁ γ) = liftAcc (wf γ)
-- -- --     <wf (inj₂ tt) = acc λ {(inj₁ δ) δ<γ → liftAcc (wf δ)}
-- -- --     <ext : ∀ {α β} → (∀ γ → γ <' α ⇔ γ <' β) → α ≡ β
-- -- --     <ext {inj₁ α} {inj₁ β} r = ≡.cong inj₁ (ext (λ γ → r (inj₁ γ))) --ext {!r!}
-- -- --       where
-- -- --       inj₁-injective : ∀ {α β : A} → inj₁ {B = ⊤} α ≡ inj₁ β → α ≡ β
-- -- --       inj₁-injective ≡.refl = ≡.refl
-- -- --       r' : (∀ γ → γ <' inj₁ α ⇔ γ <' inj₁ β)
-- -- --       r' (inj₁ x) = r (inj₁ x)
-- -- --       r' (inj₂ tt) = (λ ()) , (λ ())
-- -- --     <ext {inj₁ α} {inj₂ tt} r = absurdp' (Acc-irrefl A _<_ (wf α) (r (inj₁ α) .∧.snd tt*))
-- -- --     <ext {inj₂ tt} {inj₁ β} r = absurdp' (Acc-irrefl A _<_ (wf β) (r (inj₁ β) .∧.fst tt*))
-- -- --     <ext {inj₂ tt} {inj₂ tt} r = ≡.refl
-- -- --     <total : ∀ {α β} → α <' β ∨ α ≡ β ∨ β <' α
-- -- --     <total {inj₁ α} {inj₁ β} with total {α} {β}
-- -- --     ... | ∨.inl α<β = ∨.inl α<β
-- -- --     ... | ∨.inr (∨.inl α≡β) = ∨.inr (∨.inl (≡.cong inj₁ α≡β))
-- -- --     ... | ∨.inr (∨.inr α>β) = ∨.inr (∨.inr α>β)
-- -- --     <total {inj₁ α} {inj₂ tt} = ∨.inl (liftp tt)
-- -- --     <total {inj₂ tt} {inj₁ β} = ∨.inr (∨.inr (liftp tt))
-- -- --     <total {inj₂ tt} {inj₂ tt} = ∨.inr (∨.inl ≡.refl)

-- -- -- module _ where
-- -- --   -- van den Berg ordinals
-- -- --   open import Data.List
-- -- --   record CumulativeOrd : Set₂ where
-- -- --     field
-- -- --       Ord : Set₁
-- -- --       s : Ord → Ord
-- -- --     open Subset (lsuc ℓ0) Ord
-- -- --     private 𝓟Ord = 𝓟 (lsuc ℓ0) Ord
-- -- --     field
-- -- --       ⨆ : 𝓟Ord → Ord
-- -- --       ⇓ : Ord → 𝓟Ord
-- -- --     z : Ord
-- -- --     z = ⨆ [ [] ]ᴾ
-- -- --     field
-- -- --       ⇓s : ∀ α β → ⇓ (s α) β ≡ ([ α ∷ [] ]ᴾ ∪ ⇓ α) β
-- -- --       ⇓⨆ : ∀ (A : 𝓟Ord) β → ⇓ (⨆ A) β ≡ (⋃ (ΣP Ord A) λ (α , α∈A) → ⇓ α) β
-- -- --       ind : ∀ (P : Ord → Prop₁)
-- -- --           → (sr : ∀ α → P α → P (s α))
-- -- --           → (⋃r : ∀ (A : 𝓟Ord) → (∀ α → A α → P α) → P (⨆ A))
-- -- --           → ∀ α → P α
-- -- --       ext : ∀ {α β} → (∀ γ → ⇓ α γ ⇔ ⇓ β γ) → α ≡ β

-- -- --     _<_ : ∀ α β → Prop _
-- -- --     α < β = ⇓ β α

-- -- --     <s : ∀ β α → β < s α ⇔ (β ≡ α ∨ β < α)
-- -- --     <s β α = p , q
-- -- --       where
-- -- --       p : β < s α → (β ≡ α ∨ β < α)
-- -- --       p β<sα with ≡.substp (λ ● → ●) (⇓s α β) β<sα
-- -- --       ... | ∨.inl (∨.inl α≡β) = ∨.inl (≡.sym α≡β)
-- -- --       ... | ∨.inr β<α = ∨.inr β<α
-- -- --         where
-- -- --         u : ⇓ (s α) β ≡ ([ α ∷ [] ]ᴾ ∪ ⇓ α) β
-- -- --         u = ⇓s α β
-- -- --       q : (β ≡ α ∨ β < α) → β < s α
-- -- --       q (∨.inl β≡α) = ≡.substp (λ ● → ●) (≡.sym u) v
-- -- --         where
-- -- --         u : ⇓ (s α) β ≡ ([ α ∷ [] ]ᴾ ∪ ⇓ α) β
-- -- --         u = ⇓s α β
-- -- --         v : β ∈ [ α ∷ [] ]ᴾ ∨ β < α
-- -- --         v = ∨.inl (∨.inl (≡.sym β≡α))
-- -- --       q (∨.inr β<α) = ≡.substp (λ ● → ●) (≡.sym u) v
-- -- --         where
-- -- --         u : ⇓ (s α) β ≡ ([ α ∷ [] ]ᴾ ∪ ⇓ α) β
-- -- --         u = ⇓s α β
-- -- --         v : β ∈ [ α ∷ [] ]ᴾ ∨ β < α
-- -- --         v = ∨.inr β<α

-- -- --     <⨆ : ∀ (A : 𝓟Ord) β → β < ⨆ A ⇔ (∃ λ ((α , α∈A) : ΣP Ord A) → β < α)
-- -- --     <⨆ A β = ≡.≡→⇔ (⇓⨆ A β)

-- -- --     isTransitive-< : Transitive _<_
-- -- --     isTransitive-< {α} {β} {γ} =
-- -- --       ind (λ γ → ∀ β α → α < β → β < γ → α < γ) rs r⨆ γ β α
-- -- --       where
-- -- --       rs : ∀ γ → (∀ β α → α < β → β < γ → α < γ) →
-- -- --             ∀ β α → α < β → β < s γ → α < s γ
-- -- --       rs γ r β α p q with <s β γ .∧.fst q
-- -- --       ... | ∨.inl β≡γ = <s α γ .∧.snd (∨.inr (≡.substp (α <_) β≡γ p))
-- -- --       ... | ∨.inr β<γ = <s α γ .∧.snd (∨.inr (r β α p β<γ))
-- -- --       r⨆ : (A : 𝓟Ord)
-- -- --          → (∀ γ → γ ∈ A → ∀ β α → α < β → β < γ → α < γ)
-- -- --          → ∀ β α → α < β → β < ⨆ A → α < ⨆ A
-- -- --       r⨆ A r β α p q with <⨆ A β .∧.fst q
-- -- --       ... | ∣ (γ , γ∈A) , β<γ ∣ = <⨆ A α .∧.snd ∣ (γ , γ∈A) , r γ γ∈A β α p β<γ ∣


-- -- --     ind' : ∀ (P : Ord → Prop₁)
-- -- --          → (r : ∀ α → (∀ β → β < α → P β) → P α)
-- -- --          → ∀ α → P α
-- -- --     ind' P r α = let qα' = ind Q rs r⨆ (s α) in qα' α (<s α α .∧.snd (∨.inl ≡.refl))
-- -- --       where
-- -- --       Q : ∀ α → Prop₁
-- -- --       Q α = ∀ β → β < α → P β 

-- -- --       rs : ∀ γ → Q γ → Q (s γ)
-- -- --       rs γ qγ β β<sγ with <s β γ .∧.fst β<sγ
-- -- --       ... | ∨.inl ≡.refl = r γ qγ
-- -- --       ... | ∨.inr β<γ = qγ β β<γ
-- -- --       r⨆ : (A : 𝓟Ord) → (∀ α → A α → Q α) → Q (⨆ A)
-- -- --       r⨆ A t β β<⨆A with <⨆ A β .∧.fst β<⨆A
-- -- --       ... | ∣ (γ , γ∈A) , β<γ ∣ = t γ γ∈A β β<γ

-- -- --     _⊆_ : (α β : Ord) → Prop _
-- -- --     α ⊆ β = ∀ γ → γ < α → γ < β

-- -- --     isReflexive-⊆ : Reflexive _⊆_
-- -- --     isReflexive-⊆ γ p = p

-- -- --     isTransitive-⊆ : Transitive _⊆_
-- -- --     isTransitive-⊆ {α} {β} {γ} p q δ δ<α = q δ (p δ δ<α)

-- -- --     isAntiSymmetric-⊆ : AntiSymmetric _⊆_
-- -- --     isAntiSymmetric-⊆ {α} {β} α⊆β β⊆α = ext λ γ → (α⊆β γ , β⊆α γ)

-- -- --     isPartialOrder-⊆ : IsPartialOrder _⊆_
-- -- --     isPartialOrder-⊆ = record
-- -- --       { refl = isReflexive-⊆
-- -- --       ; antisym = isAntiSymmetric-⊆ 
-- -- --       ; trans = isTransitive-⊆ }

-- -- --     -- ⊆< : ∀ {α β γ} → α ⊆ β → β < γ → α < γ
-- -- --     -- <⊆ : ∀ {α β γ} → α < β → β ⊆ γ → α < γ
-- -- --     -- << : ∀ {α β γ} → α < β → β < γ → α < γ
-- -- --     -- ⊆⊆ : ∀ {α β γ} → α ⊆ β → β ⊆ γ → α ⊆ γ
-- -- --     -- ⊆< {α} {β} {γ} = ind' (λ β → α ⊆ β → β < γ → α < γ) r β
-- -- --     --   where
-- -- --     --   r : ∀ β →
-- -- --     --        (∀ δ → δ < β → α ⊆ δ → δ < γ → α < γ) →
-- -- --     --        α ⊆ β → β < γ → α < γ
-- -- --     --   r β p α⊆β β<γ = p {!!} {!!} {!!} {!!}
-- -- --     -- ⊆⊆ = isTransitive-⊆

-- -- --     -- <⇔s⊆ : ∀ α β → α < β ⇔ s α ⊆ β
-- -- --     -- <⇔s⊆ α β = <→s⊆ , s⊆→<
-- -- --     --   where
-- -- --     --   <→s⊆ : α < β → s α ⊆ β
-- -- --     --   <→s⊆ p γ γ<sα = {!!}
-- -- --     --   s⊆→< : s α ⊆ β → α < β
