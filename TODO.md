# Paper Review TODO

## Submission

- [ ] Convert the paper to the Springer LNCS format required by
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

- [ ] State precisely which Fiore--Pitts--Steenkamp 2022 theorem
      supplies initiality. The formal development proves cocontinuity,
      not the full initiality result.
- [ ] Give an explicit instantiation of that theorem, including its
      assumptions on W-types, quotients, extensionality, unique
      choice, sizes, and equation presentations.
- [ ] Decide whether Section 7.4 is an application of the cited
      initiality theorem or a self-contained proof. The current prose
      at lines 1515--1527 is not enough as a proof of initiality.
- [ ] Relate the two stage constructions. Section 4.1 uses quotients
      of terms over earlier approximants with unit and multiplication
      relations; Section 7 uses quotients of rank-bounded raw
      terms. Prove they agree or present only one construction.
- [ ] Resolve the equation-context issue. Section 4.3 includes
      equation-variable contexts in the lifting polynomial, while
      Section 7 drops them. Explain how arbitrary equation
      substitutions are lifted and include closure under `V(e)` where
      required.
- [ ] Define the category and morphisms for an initial extensional
      plump ordinal basis, or state the basis assumptions directly and
      prove well-foundedness separately.
- [ ] Add well-foundedness to the ordinal-basis assumptions used for
      recursion and induction.
- [ ] Make the semantic sectionability criterion precise rather than
      treating a coherent section as an almost tautological
      restatement of common-stage lifting.
- [ ] Either prove the normalisation and finitary variants or clearly
      label Section 8 as outlook.

## Technical corrections

- [ ] Add a leaf/nullary constructor to the mobile signature. A
      signature with only `node : (N -> M) -> M` has an empty W-type.
- [ ] Justify the claim that antisymmetry gives extensionality from
      equal predecessor segments. This requires a proved connection
      between `<=` and predecessor inclusion. (Now formalised)
- [ ] Give universe-level and basis instances for the cumulative
      hierarchy example.
- [ ] Clarify the role of unique choice and avoid suggesting that the
      construction is choice-free in a stronger sense than “without
      WISC”.

## Local cleanup

- [x] Remove the draft footnotes `wording?` and `metaphor basis?` from
      the abstract.
- [x] Fix the typo `generateb` in the introduction.
- [ ] Fix the Taylor citation key/year mismatch: the cited paper is
      the 1996 paper, not a 1993 publication.
- [ ] Split or otherwise reformat the overfull `DepthPreserving`
      display around lines 1115--1124.
- [ ] Audit the bibliography after switching to the LNCS bibliography
      style.

## Formalisation scope

- [ ] State clearly that the Agda development proves the cocontinuity
      isomorphism; the initiality step is imported from
      Fiore--Pitts--Steenkamp rather than formalised in this
      repository.
- [ ] Mention the stronger two-sided cocontinuity isomorphism present
      in `QIT/QW/Cocontinuity/FromDepthPreservation.agda` if it is
      used to meet the cited theorem's hypotheses.
