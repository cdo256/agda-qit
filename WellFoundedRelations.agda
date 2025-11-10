module WellFoundedRelations where

open import TypeTheory public

----------------------------------------------------------------------
-- Well-founded relations
----------------------------------------------------------------------
module wf {l m : Level}{A : Set l}(R : A → A → Prop m) where
  --------------------------------------------------------------------
  -- Accessibility predicate
  --------------------------------------------------------------------
  data Acc (x : A) : Prop (l ⊔ m) where
    acc : (∀ y → R y x → Acc y) → Acc x

  --------------------------------------------------------------------
  -- Well-foundedness
  --------------------------------------------------------------------
  iswf : Prop  (l ⊔ m)
  iswf = ∀ x → Acc x

  --------------------------------------------------------------------
  -- Well-founded induction
  --------------------------------------------------------------------
  ind :
    (_ : iswf)
    {n : Level}
    (B : A → Prop n)
    (b : ∀ x → (∀ y → R y x → B y) → B x)
    → -----------------------------------
    ∀ x → B x
  ind w B b x = Acc→B x (w x)
    where
    Acc→B : ∀ x → Acc x → B x
    Acc→B x (acc α) = b x (λ y r → Acc→B  y (α y r))

  --------------------------------------------------------------------
  -- Well-founded recursion (Proposition 5.3)
  --------------------------------------------------------------------
  module _
    (w : iswf)
    {n : Level}
    (B : A → Set n)
    (b : ∀ x → (∀ x' → R x' x → B x') → B x)
    {- We reduce well-founded recursion to well-founded induction
       using unique choice, by considering the graph Rec : (x : A)(y :
       B x) → Prop l of the recursive function rec : (x : A) → B x to
       be constructed (satisfying ∀ x → rec x == b x (λ x' _ → rec x'))
     -}
    where
    private
      data Rec (x : A) : B x → Prop (l ⊔ m ⊔ n)
        where
        mkRec :
          (f : ∀ x' → R x' x → B x')
          (_ : (x' : A)(r : R x' x) → Rec x' (f x' r))
          → ------------------------------------------
          Rec x (b x f)

      hyp :
        (x : A)
        (_ : (∀ x' → R x' x → ∃! (B x') (Rec x')))
        → ----------------------------------------
        ∃! (B x) (Rec x)
      hyp x h = ∃i (b x f₀) (∧i (mkRec f₀ g₀) v)
        where
        f₀ : ∀ x' → R x' x → B x'
        f₀ x' r = let instance _ = h x' r in the y ∶ B x' , Rec x' y

        g₀ : (x' : A)(r : R x' x) → Rec x' (f₀ x' r)
        g₀ x' r = let instance _ = h x' r in the-pf (B x') (Rec x')

        v : (y : B x) → Rec x y → b x f₀ == y
        v _ (mkRec f g) =
          ap (b x) (quot.funext λ x' → funexp λ r →
            let instance _ = h x' r in
            the-uniq (B x') (Rec x') (f x' r) (g x' r))

      instance
        gr : ∀{x} → ∃! (B x) (Rec x)
        gr {x} = ind w (λ x → ∃! (B x) (Rec x)) hyp x

    -- the recursively defined function
    rec : ∀ x → B x
    rec x = the (B x) (Rec x)

    -- and it's recursion property
    comp :
      (x : A)
      → -----------------------------
      rec x == b x (λ x' _ →  rec x')
    comp x = c (rec x) (the-pf (B x) (Rec x))
      where
      c : ∀ y → Rec x y → y == b x (λ x' _ →  rec x')
      c _ (mkRec f g) =
        ap (b x) (quot.funext λ x' → funexp λ r →
        symm (the-uniq (B x') (Rec x') (f x' r) (g x' r)))

    -- uniqueness of the recursive function
    uniq :
      (r : (x : A) → B x)
      (_ : ∀ x → r x == b x (λ x' _ → r x'))
      → ------------------------------------
      rec == r
    uniq r e = quot.funext (ind w (λ x →  rec x == r x) ih)
      where
      ih : ∀ x → (∀ x' → R x' x → rec x' == r x') → rec x == r x
      ih x h =
        proof
          rec x
        =[ comp x ]
          b x (λ x' _ →  rec x')
        =[ ap (b x) (quot.funext λ x' → funexp (h x')) ]
          b x (λ x' _ → r x')
        =[ symm (e x) ]
          r x
        qed
-- end module wf -----------------------------------------------------
