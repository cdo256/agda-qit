# Paper Review TODO

## Submission

- [x] Convert the paper to the Springer LNCS format required by
      FoSSaCS. The current source uses `article` and `plainnat`.
- [ ] Reduce the main text to the FoSSaCS limit of 18 pages excluding
      references, or move genuinely supplementary material to a
      clearly marked appendix.
- [x] Preserve double-blind review: remove authors, affiliation,
      acknowledgements, and identifying self-references from the
      submission version.
- [x] Replace the manually numbered section titles and the nonstandard
      abstract heading with the class-supported forms.

## Main theorem and structure

- [x] State precisely which Fiore--Pitts--Steenkamp 2022 theorem
      supplies initiality. The formal development proves cocontinuity,
      not the full initiality result.
- [x] Apply the general Fiore--Pitts--Steenkamp initiality theorem
      directly to the rank-bounded diagram. Its general-diagram
      hypotheses are supplied by the plump-order properties and
      well-founded recursion; no transfer lemma from Section 4 is needed.
- [x] State the initiality and well-founded-recursion requirements for the
      extensional plump ordinal basis.
- [x] Treat Section 7.4 as an application of the cited initiality result,
      rather than as a self-contained proof of initiality.
- [x] Explain that the Section 4 expository diagram need not be identified
      with the rank-bounded diagram used for the direct cocontinuity proof.
- [x] Make clear in the citation discussion that Fiore--Pitts--Steenkamp's
      general theorem, not a theorem for the Section 7 diagram specifically,
      supplies the imported initiality result.
- [x] Record that the two stage diagrams are intentionally different and
      require no equivalence for the imported general initiality theorem.
      required.
- [x] Add well-foundedness to the ordinal-basis assumptions used for
      recursion and induction.
- [x] Replace sectionability by coherent factorisation through the
      canonical map as the semantic criterion.
- [ ] Either prove the normalisation and finitary variants or clearly
      label the discussion as outlook.

## Code changes
- [ ] Define the category and morphisms for an initial extensional
      plump ordinal basis, or state the basis assumptions directly and
      prove well-foundedness separately.

## Technical corrections

- [x] Add a leaf/nullary constructor to the mobile signature. A
      signature with only `node : (N -> M) -> M` has an empty W-type.
- [x] Justify the claim that antisymmetry gives extensionality from
      equal predecessor segments using the predecessor-inclusion lemma.
- [x] Give universe-level and basis instances for the cumulative
      hierarchy example.
- [ ] Clarify the role of unique choice and avoid suggesting that the
      construction is choice-free in a stronger sense than “without
      WISC”.

## Local cleanup

- [x] Remove the draft footnotes `wording?` and `metaphor basis?` from
      the abstract.
- [x] Fix the typo `generateb` in the introduction.
- [x] Fix the Taylor citation key/year mismatch: the cited paper is
      the 1996 paper, not a 1993 publication.
- [x] Split or otherwise reformat the overfull `DepthPreserving`
      display around lines 1115--1124.
- [x] Audit the bibliography after switching to the LNCS bibliography
      style.

## Formalisation scope

- [x] State clearly that the Agda development proves the cocontinuity
      isomorphism; the initiality step is imported from
      Fiore--Pitts--Steenkamp rather than formalised in this
      repository.
- [x] Mention the stronger two-sided cocontinuity isomorphism present
      in `QIT/QW/Cocontinuity/FromDepthPreservation.agda` if it is
      used to meet the cited theorem's hypotheses.

## Author Notes

- [x] Keep the paper centred on one main theorem.
- [x] Relate this construction to the theory of signatures.
- [ ] Put the formalisation front and centre.
- [ ] Make the plump-ordinal listing consistent with the formalisation.
- [x] Explain the theory-of-signatures route to QIT presentations.
- [x] Relate extensional plump ordinals to the basic ordinal examples.
- [ ] Explain how future work could bridge the remaining reduction gap.
- [x] Identify reusable combinators for deriving QITs.
- [x] Cite Van den Berg's work on ordinals and relate it to these ordinals.
- [ ] Rephrase the semantic criterion as the syntactic criterion is developed.
- [x] Keep the introduction within two pages.
- [x] Compress the background section to roughly two pages.
- [ ] Add a compact diagram or schematic for the motivating examples.
- [ ] Check whether the theory-of-toposes background belongs in the paper.
- [ ] Verify that the container reference is the best reference.
- [ ] Check whether alpha/beta notation is confusing with ordinal stages.
- [ ] Check whether the interpretation-equation parentheses are necessary.
- [ ] State the exact upstream theorem used for initiality.
- [ ] Define or cite the size operations used in the background presentation.
- [ ] Compare the expository stage presentation with the rank-bounded diagram.
- [ ] Put the formalisation assumptions front and centre.
- [ ] Add the formalisation citation.
- [ ] Check theorem and section numbering after compression.
