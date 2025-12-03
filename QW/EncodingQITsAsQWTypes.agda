module QW.EncodingQITsAsQWTypes where

open import QW.IndexedPolynomialFunctorsAndEquationalSystems public

-- Set-valued identity types
data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

----------------------------------------------------------------------
-- Finite multisets with swap (Example 7.5)
----------------------------------------------------------------------
module Bag (X : Set) where
  Σ : Sig
  Op Σ = 𝟙 + X
  Ar Σ (ι₁ _) = 𝟘
  Ar Σ (ι₂ _) = 𝟙

  ε : Syseq Σ
  ε = mkSig
    (X × X)
    (λ _ → 𝟙)
    , (λ { (x , y) → σ ((ι₂ x) , (λ _ → σ (ι₂ y , (λ _ → η _))))})
    , (λ { (x , y) → σ ((ι₂ y) , (λ _ → σ (ι₂ x , (λ _ → η _))))})

----------------------------------------------------------------------
-- Length-indexed multisets (Example 7.6)
----------------------------------------------------------------------
{-
See QWI.EncodingQITsAsQWITypes
-}

module SimpleTree where
  Σ : Sig
  Op Σ       = 𝔹
  Ar Σ false = 𝟘
  Ar Σ true  = 𝔹

  ε : Syseq Σ
  ε = mkSig 𝟘 (λ ()) , (λ ()) , λ ()

  open import QW.FixedPointsAreQWTypes 

  claim = FxSzAlg→QWType Σ ε


----------------------------------------------------------------------
-- Unordered countably-branching trees (Example 7.7)
----------------------------------------------------------------------
module ωTree (X : Set) where
  Σ : Sig
  Op Σ        = 𝟙 + X
  Ar Σ (ι₁ _) = 𝟘
  Ar Σ (ι₂ _) = ℕ

  ε : Syseq Σ
  ε = mkSig
    (X × ∑ (ℕ → ℕ) (LiftProp ∘ isIso))
    (λ _ → ℕ)
    , (λ { (x , _ , _) → σ (ι₂ x , η)})
    , (λ { (x , b , _) → σ (ι₂ x , η ∘ b)})

  open import QW.FixedPointsAreQWTypes 

  claim = FxSzAlg→QWType Σ ε

module 2^ωTree (X : Set) where
  Σ : Sig
  Op Σ        = 𝟙 + X
  Ar Σ (ι₁ _) = 𝟘
  Ar Σ (ι₂ _) = ℕ → 𝔹


  ε : Syseq Σ
  ε = mkSig
    (X × ∑ ((ℕ → 𝔹) → (ℕ → 𝔹)) (LiftProp ∘ isIso))
    (λ _ → (ℕ → 𝔹))
    , (λ { (x , u , v) → σ (ι₂ x , η)})
    , (λ { (x , u , v) → σ (ι₂ x , η ∘ u)})


----------------------------------------------------------------------
-- W-suspensions
----------------------------------------------------------------------
module W-suspension
  (A : Set)
  (B : A → Set)
  (C : Set)
  (l r : C → A)
  where
  Σ : Sig
  Op Σ = A
  Ar Σ = B

  ε : Syseq Σ
  ε = mkSig
    C
    (λ c → B (l c) + B (r c))
    , (λ c → sup (l c , η ∘ ι₁))
    , (λ c → sup (r c , η ∘ ι₂))

----------------------------------------------------------------------
-- W-types with reductions
----------------------------------------------------------------------
{-
See QWI.EncodingQITsAsQWITypes
-}

----------------------------------------------------------------------
-- Blass infinitary equational theory – Lumsdaine and Shulman HIT
----------------------------------------------------------------------
module F where
  data JointlySurjective (f g : ℕ → ℕ) : Set where
    jointly-surjective : (n : ℕ) → ∑ ℕ (λ x → ((f x ≡ n) + (g x ≡ n))) → JointlySurjective f g

  evenodd : ℕ → ℕ + ℕ
  evenodd zero = ι₁ zero
  evenodd (n +1) with (evenodd n)
  evenodd (n +1) | ι₁ x = ι₂ x
  evenodd (n +1) | ι₂ y = ι₁ (y +1)

  _∪_ : ∀ {ℓ} {A : Set ℓ} (f g : ℕ → A) → ℕ → A
  (f ∪ g) = [ f , g ] ∘ evenodd

  -- assuming some bijection ℕ × ℕ ↔ ℕ
  postulate
    ℕpair : ℕ × ℕ → ℕ
    ℕunpair : ℕ → ℕ × ℕ
    unpair-id-1 : (ℕpair ∘ ℕunpair) ≡ id {A = ℕ}
    unpair-id-2 : (ℕunpair ∘ ℕpair) ≡ id {A = ℕ × ℕ}

  data FOp₀ : Set where
    Zdat : FOp₀
    Sdat : FOp₀
    supdat : FOp₀

  FAr₀ : FOp₀ → Set
  FAr₀ Zdat = 𝟘
  FAr₀ Sdat = 𝟙
  FAr₀ supdat = ℕ

  FΣ : Sig
  Op FΣ = FOp₀
  Ar FΣ = FAr₀

  h-sub : {L : ℕ → ℕ → ℕ} → ℕ → ℕ → T{Σ = FΣ} ℕ
  h-sub zero x = η x -- h₀ = h. h(x) is var x.
  h-sub {L} (n +1) x = σ (supdat , ((h-sub {L} n) ∘ (L n)))

  data FOp₁ : Set where
    F-rule-1 : (f g : ℕ → ℕ) → FOp₁
    F-rule-2 : FOp₁
    F-rule-3 : FOp₁
    F-rule-4 : (b c : ℕ → ℕ)
      (js : JointlySurjective b c)
      (L : ℕ → ℕ → ℕ)
      (st1 : (n : ℕ) → ∑ ℕ (λ m → ∑ ℕ (λ l → L (b m) l ≡ b n)))
      (st2 : (n : ℕ) → ∑ ℕ (λ m → ∑ ℕ (λ l → L (c m) l ≡ c n)))
      → FOp₁
    F-rule-5 : FOp₁

  FAr₁ : FOp₁ → Set
  FAr₁ (F-rule-1 f g) = ℕ
  FAr₁ F-rule-2 = ℕ + ℕ
  FAr₁ F-rule-3 = ℕ + ℕ
  FAr₁ (F-rule-4 b c js L st1 st2) = ℕ
  FAr₁ F-rule-5 = 𝟘

  FΓ : Sig
  Op FΓ = FOp₁
  Ar FΓ = FAr₁

  Feq : (p : FOp₁) → T{Σ = FΣ} (FAr₁ p) × T{Σ = FΣ} (FAr₁ p)

  -- rule 1: sup(h ∘ f) = sup(h ∘ g)
  Feq (F-rule-1 f g) = σ (supdat , (η ∘ f))
                    , σ (supdat , (η ∘ g))

  -- rule 2: sup(f ∪ {sup(f ∪ g)}) = sup(f ∪ g)
  Feq F-rule-2 = σ (supdat , ((η ∘ ι₁) ∪ (λ _ → σ (supdat , ((η ∘ ι₁) ∪ (η ∘ ι₂))))))
              , σ (supdat , ((η ∘ ι₁) ∪ (η ∘ ι₂)))

  -- rule 3: sup(f ∪ {S(sup(f ∪ g))}) = S(sup(f ∪ g))
  Feq F-rule-3 = σ (supdat , ((η ∘ ι₁)
                      ∪ (λ _ → σ (Sdat , (λ _ → σ (supdat , ((η ∘ ι₁) ∪ (η ∘ ι₂)))) )) ))
              , σ (Sdat , (λ _ → σ (supdat , ((η ∘ ι₁) ∪ (η ∘ ι₂)))))

  -- rule 4: ∀ {b, c, L, h} → sup(bar-f) = sup(bar-g),
  -- where bar-h(n) = h_{fst (unpair n)}(snd (unpair n))
  Feq (F-rule-4 b c js L st1 st2) = σ (supdat , (λ x → let k , n = ℕunpair x in (h-sub {L} k (b n))))
                                  , σ (supdat , (λ x → let k , n = ℕunpair x in (h-sub {L} k (c n))))

  -- rule 5: sup({0}) = 0
  Feq F-rule-5 = σ (supdat , (λ _ → σ (Zdat , λ())))
              , σ (Zdat , λ())
