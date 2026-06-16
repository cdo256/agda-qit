open import QIT.Prelude
open import QIT.Prop
open import QIT.Category.Base
open import QIT.Relation.Binary using (IsEquivalence)


module QIT.Category.Family
  {ℓCo ℓCh ℓCe} (ℓI : Level)
  (C : Category ℓCo ℓCh ℓCe)
  where

module C = Category C

record Fam : Set (lsuc ℓI ⊔ ℓCo) where
  constructor _,_
  field
    I : Set ℓI
    A : I → C.Obj

record Hom (F₁ F₂ : Fam) : Set (lsuc ℓI ⊔ ℓCo ⊔ ℓCh) where
  constructor _,_
  open Fam F₁ 
  open Fam F₂ renaming (I to J; A to B) 
  field
    u : I → J
    f : ∀ i → A i C.⇒ B (u i)

record _≈h_ {F₁ F₂ : Fam} (f₁ f₂ : Hom F₁ F₂) : Prop (lsuc ℓI ⊔ ℓCo ⊔ ℓCh ⊔ ℓCe) where
  constructor mk≈
  open Fam F₁ 
  open Fam F₂ renaming (I to J; A to B) 
  field
    idx≡ : ∀ i → Hom.u f₁ i ≡ˢ Hom.u f₂ i
    hom≈ : ∀ i → substˢ (λ ○ → A i C.⇒ B ○) (idx≡ i) (Hom.f f₁ i)
         C.≈ Hom.f f₂ i

id : ∀ {F} → Hom F F
id {I , X} = _ , (λ _ → C.id)

_∘_ : {U V W : Fam} → Hom V W → Hom U V → Hom U W
h ∘ g = (λ z → Hom.u h (Hom.u g z)) , (λ i → Hom.f h (Hom.u g i) C.∘ Hom.f g i)

u-∘ : ∀ {U V W : Fam} (h : Hom V W) (g : Hom U V) (i : Fam.I U)
    → Hom.u (h ∘ g) i ≡ˢ Hom.u h (Hom.u g i)
u-∘ h g i = ≡.reflˢ


module _ where
  open import Data.Nat
  postulate
    s : ℕ → ℕ
    u : ∀ n → s n ≡ n
  {-# REWRITE u #-}

--   module _ (s : ℕ → ℕ) (u : ∀ n → s n ≡ˢ n) where
--     {-# REWRITE u #-}

-- -- f-∘ : ∀ {U V W : Fam} (h : Hom V W) (g : Hom U V) (i : Fam.I U)
-- --     → Hom.f (h ∘ g) i ≡ˢ Hom.f h (Hom.u g i) C.∘ Hom.f g i
-- -- f-∘ h g i = ≡.reflˢ

-- -- FamCat : Category (ℓCo ⊔ lsuc ℓI) (ℓCo ⊔ ℓCh ⊔ lsuc ℓI) (ℓCo ⊔ ℓCh ⊔ ℓCe ⊔ lsuc ℓI)
-- -- FamCat = record
-- --   { Obj = Fam
-- --   ; _⇒_ = Hom
-- --   ; _≈_ = _≈h_
-- --   ; id = id
-- --   ; _∘_ = _∘_
-- --   ; assoc = assoc
-- --   ; sym-assoc = sym-assoc
-- --   ; identityˡ = identityˡ
-- --   ; identityʳ = identityʳ
-- --   ; identity² = identity²
-- --   ; equiv = equiv
-- --   ; ∘-resp-≈ = ∘-resp-≈h
-- --   }
-- --   where
-- --   assoc : ∀ {A₀ B₀ C₀ D₀ : Fam}
-- --         → {f : Hom A₀ B₀} → {g : Hom B₀ C₀} → {h : Hom C₀ D₀}
-- --         → ((h ∘ g) ∘ f) ≈h (h ∘ (g ∘ f))
-- --   assoc {A₀ = I , A} {B₀ = J , B} {C₀ = K , D} {D₀ = L , E}
-- --         {f = f} {g = g} {h = h} = record
-- --     { idx≡ = idx-assoc
-- --     ; hom≈ = hom-assoc
-- --     }
-- --     where
-- --     idx-assoc : ∀ i → Hom.u ((h ∘ g) ∘ f) i ≡ˢ Hom.u (h ∘ (g ∘ f)) i
-- --     idx-assoc i =
-- --       transˢ (u-∘ (h ∘ g) f i)
-- --         (transˢ (u-∘ h g (Hom.u f i))
-- --           (transˢ (congˢ (Hom.u h) (symˢ (u-∘ g f i)))
-- --             (symˢ (u-∘ h (g ∘ f) i))))

-- --     hom-assoc : ∀ i
-- --       → subst (λ ○ → A i C.⇒ E ○) (idx-assoc i) (Hom.f ((h ∘ g) ∘ f) i)
-- --       C.≈ Hom.f (h ∘ (g ∘ f)) i
-- --     -- hom-assoc i
-- --     --   rewrite u-∘ (h ∘ g) f i
-- --     --         | u-∘ h g (Hom.u f i)
-- --     --         | u-∘ g f i
-- --     --         | u-∘ h (g ∘ f) i
-- --     --         | f-∘ (h ∘ g) f i
-- --     --         | f-∘ h g (Hom.u f i)
-- --     --         | f-∘ g f i
-- --     --         | f-∘ h (g ∘ f) i
-- --     --   = C.assoc {f = Hom.f f i} {g = Hom.f g (Hom.u f i)} {h = Hom.f h (Hom.u g (Hom.u f i))}

-- --   sym-assoc : ∀ {A₀ B₀ C₀ D₀ : Fam}
-- --             → {f : Hom A₀ B₀} → {g : Hom B₀ C₀} → {h : Hom C₀ D₀}
-- --             → (h ∘ (g ∘ f)) ≈h ((h ∘ g) ∘ f)
-- --   sym-assoc {A₀ = I , A} {B₀ = J , B} {C₀ = K , D} {D₀ = L , E}
-- --             {f = f} {g = g} {h = h} = record
-- --     { idx≡ = λ i → ≡.sym (idx-assoc i)
-- --     ; hom≈ = hom-sym-assoc
-- --     }
-- --     where
-- --     idx-assoc : ∀ i → Hom.u ((h ∘ g) ∘ f) i ≡ Hom.u (h ∘ (g ∘ f)) i
-- --     idx-assoc i =
-- --       ≡.trans (u-∘ (h ∘ g) f i)
-- --         (≡.trans (u-∘ h g (Hom.u f i))
-- --           (≡.trans (≡.cong (Hom.u h) (≡.sym (u-∘ g f i)))
-- --             (≡.sym (u-∘ h (g ∘ f) i))))

-- --     hom-sym-assoc : ∀ i
-- --       → subst (λ ○ → A i C.⇒ E ○) (≡.sym (idx-assoc i)) (Hom.f (h ∘ (g ∘ f)) i)
-- --       C.≈ Hom.f ((h ∘ g) ∘ f) i
-- --     -- hom-sym-assoc i
-- --     --   rewrite u-∘ (h ∘ g) f i
-- --     --         | u-∘ h g (Hom.u f i)
-- --     --         | u-∘ g f i
-- --     --         | u-∘ h (g ∘ f) i
-- --     --         | f-∘ (h ∘ g) f i
-- --     --         | f-∘ h g (Hom.u f i)
-- --     --         | f-∘ g f i
-- --     --         | f-∘ h (g ∘ f) i
-- --     --   = C.sym-assoc {f = Hom.f f i} {g = Hom.f g (Hom.u f i)} {h = Hom.f h (Hom.u g (Hom.u f i))}

-- --   identityˡ : ∀ {F G : Fam} {h : Hom F G} → (id ∘ h) ≈h h
-- --   identityˡ {h = u , f} =
-- --     mk≈ (λ _ → ≡.refl) (λ _ → C.identityˡ)

-- --   identityʳ : ∀ {F G : Fam} {h : Hom F G} → (h ∘ id) ≈h h
-- --   identityʳ {h = u , f} =
-- --     mk≈ (λ _ → ≡.refl) (λ _ → C.identityʳ)

-- --   identity² : ∀ {F : Fam} → (id ∘ id {F}) ≈h id {F}
-- --   identity² =
-- --     mk≈ (λ _ → ≡.refl) (λ _ → C.identity²)

-- --   ≈h-refl : ∀ {F G : Fam} {h : Hom F G} → h ≈h h
-- --   ≈h-refl =
-- --     mk≈ (λ _ → ≡.refl) (λ _ → C.refl)

-- --   ≈h-sym : ∀ {F G : Fam} {h k : Hom F G} → h ≈h k → k ≈h h
-- --   ≈h-sym {F = I , A} {G = J , B} {h = u , f} {v , g} (mk≈ p q) =
-- --     mk≈ (λ i → ≡.sym (p i)) hom≈-sym
-- --     where
-- --     sym-hom : ∀ {X : C.Obj} {j k : J} {a : X C.⇒ B j} {b : X C.⇒ B k}
-- --             → (pi : j ≡ k)
-- --             → subst (λ ○ → X C.⇒ B ○) pi a C.≈ b
-- --             → subst (λ ○ → X C.⇒ B ○) (≡.sym pi) b C.≈ a
-- --     sym-hom ≡.refl qi = C.sym qi

-- --     hom≈-sym : ∀ i → subst (λ ○ → A i C.⇒ B ○) (≡.sym (p i)) (g i) C.≈ f i
-- --     hom≈-sym i = sym-hom (p i) (q i)

-- --   ≈h-trans : ∀ {F G : Fam} {h k l : Hom F G} → h ≈h k → k ≈h l → h ≈h l
-- --   ≈h-trans {F = I , A} {G = J , B} {h = u , f} {v , g} {w , h} (mk≈ p q) (mk≈ r s) =
-- --     mk≈ (λ i → ≡.trans (p i) (r i)) hom≈-trans
-- --     where
-- --     trans-hom : ∀ {X : C.Obj} {j k l : J}
-- --               → {a : X C.⇒ B j} {b : X C.⇒ B k} {c : X C.⇒ B l}
-- --               → (pi : j ≡ k) → (ri : k ≡ l)
-- --               → subst (λ ○ → X C.⇒ B ○) pi a C.≈ b
-- --               → subst (λ ○ → X C.⇒ B ○) ri b C.≈ c
-- --               → subst (λ ○ → X C.⇒ B ○) (≡.trans pi ri) a C.≈ c
-- --     trans-hom ≡.refl ≡.refl qi ri = C.trans qi ri

-- --     hom≈-trans : ∀ i → subst (λ ○ → A i C.⇒ B ○) (≡.trans (p i) (r i)) (f i) C.≈ h i
-- --     hom≈-trans i = trans-hom (p i) (r i) (q i) (s i)

-- --   equiv : ∀ {F G : Fam} → IsEquivalence (_≈h_ {F} {G})
-- --   equiv = record
-- --     { refl = ≈h-refl
-- --     ; sym = ≈h-sym
-- --     ; trans = ≈h-trans
-- --     }

-- --   ∘-resp-≈h : ∀ {T U V : Fam} {f h : Hom U V} {g i : Hom T U}
-- --             → f ≈h h → g ≈h i → (f ∘ g) ≈h (h ∘ i)
-- --   ∘-resp-≈h {T = I , A} {U = J , B} {V = K , D}
-- --              {f = u , f} {v , g} {u' , f'} {v' , g'} (mk≈ p q) (mk≈ r s) =
-- --     mk≈ (λ i → ≡.trans (≡.cong u (r i)) (p (v' i))) hom≈-resp
-- --     where
-- --     subst-comp : ∀ {X : C.Obj} {j k : J} (h : ∀ j → B j C.⇒ D (u j))
-- --                → (pi : j ≡ k) (a : X C.⇒ B j)
-- --                → subst (λ ○ → X C.⇒ D (u ○)) pi (h j C.∘ a)
-- --                ≡ h k C.∘ subst (λ ○ → X C.⇒ B ○) pi a
-- --     subst-comp h ≡.refl a = ≡.refl

-- --     subst-compˡ : ∀ {X Y : C.Obj} {j k : K}
-- --                 → (pi : j ≡ k) (h : Y C.⇒ D j) (a : X C.⇒ Y)
-- --                 → subst (λ ○ → X C.⇒ D ○) pi (h C.∘ a)
-- --                 ≡ subst (λ ○ → Y C.⇒ D ○) pi h C.∘ a
-- --     subst-compˡ ≡.refl h a = ≡.refl

-- --     hom≈-resp : ∀ i
-- --       → subst (λ ○ → A i C.⇒ D ○) (≡.trans (≡.cong u (r i)) (p (v' i))) (f (u' i) C.∘ f' i)
-- --       C.≈ (g (v' i) C.∘ g' i)
-- --     hom≈-resp i =
-- --       ≡.substp
-- --         (λ lhs → lhs C.≈ (g (v' i) C.∘ g' i))
-- --         (≡.sym eq)
-- --         (C.∘-resp-≈ (q (v' i)) (s i))
-- --       where
-- --       P : K → Set ℓCh
-- --       P ○ = A i C.⇒ D ○

-- --       Q : J → Set ℓCh
-- --       Q ○ = A i C.⇒ B ○

-- --       z : A i C.⇒ D (u (u' i))
-- --       z = f (u' i) C.∘ f' i

-- --       eq : subst P (≡.trans (≡.cong u (r i)) (p (v' i))) z
-- --          ≡ subst (λ ○ → B (v' i) C.⇒ D ○) (p (v' i)) (f (v' i))
-- --            C.∘ subst Q (r i) (f' i)
-- --       eq = ≡.trans
-- --         (≡.sym (≡.subst-subst {P = P} (≡.cong u (r i)) {y≡z = p (v' i)} {p = z}))
-- --         (≡.trans
-- --           (≡.cong (subst P (p (v' i))) (≡.subst-∘ {C = P} u (r i) z))
-- --           (≡.trans
-- --             (≡.cong (subst P (p (v' i))) (subst-comp f (r i) (f' i)))
-- --             (subst-compˡ (p (v' i)) (f (v' i)) (subst Q (r i) (f' i)))))
