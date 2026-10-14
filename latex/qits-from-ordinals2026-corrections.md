# Proposed corrections: qits-from-ordinals2026

1. **Anonymise repository link in abstract** (`qits-from-ordinals2026.tex:85`)
   - Current: `\url{https://github.com/cdo256/agda-qit/tree/fossacs}` — reveals the
     author's GitHub account, violating double-blind review.
   - Proposed: replace with an anonymised mirror, e.g. via
     <https://anonymous.4open.science>, giving
     `\url{https://anonymous.4open.science/r/<id>}`.
   - Note: there is no `fossacs` branch on `origin` (the closest is
     `wip/fossacs2027`), so the current link is also broken.

2. **Explain the theory of signatures** (`qits-from-ordinals2026.tex:106–111`, Introduction)
   - Current: "The theory of signatures gives one such route via a CwF-like
     universal QIIT, but its full construction is substantial; …" The term is
     used without explanation, so a reader who doesn't know it can't follow.
   - Proposed replacement (about one line longer than the current text, as
     space is tight):

     > One such route is the *theory of signatures*
     > \citep{kaposi2019-constructing-qiit}, where a QIIT is specified by a
     > context in a small type theory whose types describe its sorts and
     > constructors, and initial algebras arise from a universal QIIT of
     > signatures; this extends to infinitary QIITs
     > \citep{kovacs2020-infinitary-qiit}. The construction is substantial,
     > however, and it remains unclear whether simpler combinators suffice
     > for a large class of infinitary QITs.

   - Citations already in `master.bib`: `kaposi2019-constructing-qiit` (main
     reference), `kovacs2020-infinitary-qiit` (infinitary extension).

## Further issues (review pass, 2026-10-14)

### Substantive

3. **The stagewise constructor μ is not justified for this diagram**
   (`.tex:337–341`, `1148–1166`)
   - Here the stages are `Q_α = T_{≤α}/≈`, which are quotients of raw terms.
     To define `μ : colim_α S(Q_α) → Q`, you have to apply `sup^T` to a
     family `B(a) → Q_α`. Doing that needs representatives for the whole
     family, which is exactly the choice problem the paper is avoiding.
     In FPS the stages are built as quotients of `S(colim_{β<α} D_β)`, so
     μ comes for free there. That isn't true of this diagram.
   - The Agda (`QIT/QW/Diagram.agda`, `Cocontinuity/FromDepthPreservation.agda`)
     proves `FD*/ ≅ F(D*/)`, but I found no definition of μ or `intro` on
     `D*/`. The existing `ssup₀` (`QIT/QW/Stage.agda:46`) works on raw bounded
     terms, not on quotient classes.
   - Cocontinuity alone doesn't give initiality: FPS define
     `intro = μ ∘ κ⁻¹`, so μ has to exist first. For this diagram,
     `colim_α Q_α ≅ T/≈`, because every term lives at its own rank. Composing
     μ with `σ_D` would therefore give `S(T/≈) → T/≈` directly. For mobiles,
     that is `node` on `T/perm`, which is the original choice problem. So
     defining μ is equivalent to the problem being solved, not a routine
     step.
   - **Authors' position:** μ exists, using the successor ordinal. Action:
     make it explicit in the Agda, i.e. define
     `μ : FD*/ → D*/` (or `μ_α : F(D̃/ α) → D̃/ (α +1)`, natural in α) and
     state the hypotheses of FPS Thm 6.4 for it.
   - Open concern: the successor fixes the *bound* (`sup(a, f)` has rank
     `≤ α+1`), but not the *lift*. `F(D̃/ α)` contains families
     `B(a) → T_{≤α}/≈`, and `ssup₀` needs `B(a) → T_{≤α}`. Check whether the
     definition goes through without choosing representatives (for
     infinitary `B(a)`, `S(X/≈) ≠ S(X)/≈ₚ` constructively).
   - Fix: either show that this diagram satisfies the hypotheses of FPS
     Thm 6.4 (including how μ is defined), or explain how μ is obtained.
     A reviewer will ask about this. "The general plump ordering … supply
     the corresponding size hypotheses" (`1139–1142`) isn't enough.

4. **The ordinal basis is itself a QIIT, and the paper never says so**
   (`.tex:472–488`, abstract, Thm 5.4)
   - `Z` is defined inductive-inductively together with `<` and `≤`, and has
     a path constructor `antisym`. The main theorem assumes that an initial
     algebra of this kind exists. A reader will immediately ask whether this
     is circular, and whether the assumption is weaker than WISC.
   - Fix: say this explicitly in the introduction and in the theorem, and
     move the "relationship to collection principles is open" remark
     (`1262`) forward.

5. **The `V` listing is a conditional QIT, and doesn't match the QW
   encoding used in the text** (`.tex:139–150` vs `763–768`)
   - The listing guards the equation with `EqImage` on values (`iy j ≡ ix i`).
     That is a conditional equation, which the conclusion (`1262`) lists as
     future work. The text (`763`) uses the FPS encoding instead, where
     `f : A→X` and `g : B→X` have the same image on *variables*.
   - Fix: give the QW-style presentation, or say that the listing is
     informal and is encoded as in FPS.
   - `V` has arities `I : Type` for every small type, so the basis must be
     closed under every small type. This contradicts `461–466` ("we do not
     require closure under every small type"), which needs a caveat.

6. **The hypotheses on Z are stated inconsistently**
   - `461–466`: arities must include `B(a)` *and* `V(e)`.
   - Thm 5.3 (`1112`): only "supporting the arities `B(a)`".
   - Thm 5.4 (`1189`): "initial extensional plump ordinal algebra for Σ".
   - Intro (`247`): "initial … closed under the arities of Σ".
   - `1194–1197`: "Equivalently … supported by an extensional plump ordinal
     basis", which drops initiality, so it isn't equivalent.
   - `906–910` says the `V(e)` contexts aren't needed, which makes `461–466`
     out of date. Pick one formulation and use it everywhere.

7. **The ambient type theory is described in four different ways**
   - "extensional dependent type theory with … path elimination" (`1185`)
     vs. "type theory with propositions, funext, propext, unique choice, set
     quotients" (`791`) vs. the Agda module parameters (`PathElim`, `A!C`,
     `FunExt`, `PropExt`, `SetQuotients`). "Extensional type theory" suggests
     equality reflection, which isn't what's meant.

8. **The explanation of the roles of the hypotheses is wrong**
   (`.tex:1122–1126`)
   - "Extensionality ensures that these rank equalities descend through the
     stage quotients": descent is quotient recursion, which only needs depth
     preservation. Extensionality is what makes permutation and image
     equations depth-preserving (Lemma 3.3).
   - "Plumpness places all arguments … below the common supremum": any
     supremum with `<sup` does this. Plumpness is needed for `≤`/`<`
     transitivity and weakening.

9. **There are two descriptions of the diagram**
   (`.tex:747–754` vs Section 4.1)
   - `747–754` refers to "unit and multiplication relations" of the FPS
     stages, which are never introduced. Section 4.1 uses a single uniform
     relation. Delete `747–754`, which also saves space.

### Notation and presentation

10. **Notation clashes**
    - The canonical map is `κ_D` in Sections 1–2 and `φ` in Section 4.
    - `μ` is both the stagewise constructor (`340`, `1151`) and the rank
      family (`1036`).
    - The basis uses `S', P'` "freely extending S and P" (`490`), but the
      signature is `(A,B)` everywhere else, and `S` is the functor.
    - Mobile: the listing has a parameter `I` and `leaf : Mobile`, which
      should be `Mobile I`. The text uses `ℕ`.

11. **Cross-references**
    - The theorem and lemma labels sit inside `quote`, so `\ref` gives the
      *subsection* number (they happen to match now). Use llncs
      `theorem`/`lemma` environments. The "extensionality of the plump
      order" lemma (`420`) has no number.
    - `275`, `923`: "Section 4 proves/establishes …" is referenced from
      inside Section 4. Point to `cocontinuity-from-depth-preservation`
      instead.
    - `246–249`: the informal theorem refers to "the assumptions of
      Theorem 5.4", which is itself.
    - `1092`: "exact-rank lifting theorem" is Lemma 5.2.
    - `202`: "defined in the mobile listing. % Add tag reference"

12. **Typos and leftovers**
    - `149`: `sett` → `mkset`.
    - `400`: `\mathsf{sup}\,a\,f)` has a stray `)`.
    - `104`: `types.\citep{…}` → `types~\citep{…}.`
    - `113`: "the Mobile: A permutation-invariant …" → lower-case.
    - `137`, `202`, `501`: leftover `%` notes.
    - `145`: `Set₁` and `Type` are mixed.
    - `278`: "finite multisets (as lists)" vs the abstract.

### Space (limit 18 pp)

The current build is 19 pp. The body ends on p. 18 and the bibliography
runs pp. 18–19. Check whether the 18-page limit includes references.
Candidate cuts:

- `415–417` repeats `408–413`.
- The "Agda proves the iso; initiality is imported" statement appears four
  times (abstract, `365–367`, `796–798`, `1178`). Keep one in the body.
- Related work appears three times (intro `164–173`, `228–233`; Sec 2
  `365–370`; Discussion `1201–1239`). Merge it into one place.
- Sec 4.1 (`805–904`) displays many one-line definitions as separate
  equations. Run them inline.
- `747–754`: see item 9.
- Fold Sec 3.3 ("too in the weeds" per `501`) into the lemma statement.
- `281–287` and `1257–1261` say the same thing ("coherent factorisation").
