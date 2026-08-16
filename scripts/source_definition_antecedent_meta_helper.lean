/-!
This source is injected after `import Lean` and the reviewed paper module by
the source-definition antecedent route runner.  It is intentionally not a
standalone module: the helper must execute in the exact environment of the
paper declaration it reviews, rather than becoming an independently compiled
audit dependency.

The declaration names below are coordinates only.  Acceptance comes from
Lean's elaborated expressions and definitional equality under full
transparency.  In particular, neither predicate spelling nor an IFF side's
printed text is evidence that a source theorem antecedent is the intended
paper-facing definition.
-/

open Lean Meta Elab Command

namespace EconCSLibAudit.SourceDefinitionAntecedent

private structure BridgeVerdict where
  schema : String := "3"
  iffIsSyntactic : Bool := false
  matchingIffSides : Array String := #[]
  requestedSideMatches : Bool := false
  rawExpansionMatchesLemmaBinder : Bool := false
  reviewSurfaceIsSyntacticIff : Bool := false
  reviewSurfaceMatchesActualIff : Bool := false
  reviewFormulaIffSide : String := ""
  reviewFormulaSelectionMethod : String := ""
  reviewFormulaSideMatchesActual : Bool := false
  oppositeActualEndpointMatchesLemmaBinder : Bool := false
  lemmaBinderType : String := ""
  requestedEndpointType : String := ""
  definitionIffDisplay : String := ""
  lemmaBinderAlpha : String := ""
  leftIffSideAlpha : String := ""
  rightIffSideAlpha : String := ""
  parsedRawExpansionAlpha : String := ""
  reviewLeftIffSideAlpha : String := ""
  reviewRightIffSideAlpha : String := ""
  actualLeftIffSideAlpha : String := ""
  actualRightIffSideAlpha : String := ""
  parameterCorrespondenceEstablished : Bool := false
  parameterCorrespondenceMethod : String := ""
  /-- Each pair is `(definition outer-binder index, lemma outer-binder index)`.
  These are declaration coordinates, never parser/display names. -/
  parameterCorrespondence : Array (Nat × Nat) := #[]
  failureTag : String := ""

private def failure (tag : String) : BridgeVerdict :=
  { failureTag := tag }

private def binderInfoName : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

private def alphaNameIndex (seen : Array Name) (name : Name) : Array Name × Nat :=
  match seen.findIdx? (fun candidate => candidate == name) with
  | some index => (seen, index)
  | none => (seen.push name, seen.size)

private def alphaLevelMVarIndex
    (seen : Array LMVarId) (id : LMVarId) : Array LMVarId × Nat :=
  match seen.findIdx? (fun candidate => candidate == id) with
  | some index => (seen, index)
  | none => (seen.push id, seen.size)

/--
Encode universe levels without retaining generated level-parameter or level
metavariable identities.  The encounter index preserves equality relations
between repeated occurrences while making the representation stable under
alpha-renaming and fresh metavariable allocation.
-/
private partial def canonicalAlphaLevel
    (seenParams : Array Name) (seenMVars : Array LMVarId) (level : Level) :
    MetaM (Array Name × Array LMVarId × Json) := do
  match level with
  | .zero => pure (seenParams, seenMVars, Json.mkObj [("tag", Json.str "zero")])
  | .succ inner =>
      let (nextParams, nextMVars, canonicalInner) ←
        canonicalAlphaLevel seenParams seenMVars inner
      pure (nextParams, nextMVars, Json.mkObj [
        ("tag", Json.str "succ"), ("of", canonicalInner)])
  | .max left right =>
      let (leftParams, leftMVars, canonicalLeft) ←
        canonicalAlphaLevel seenParams seenMVars left
      let (nextParams, nextMVars, canonicalRight) ←
        canonicalAlphaLevel leftParams leftMVars right
      pure (nextParams, nextMVars, Json.mkObj [
        ("tag", Json.str "max"), ("left", canonicalLeft), ("right", canonicalRight)])
  | .imax left right =>
      let (leftParams, leftMVars, canonicalLeft) ←
        canonicalAlphaLevel seenParams seenMVars left
      let (nextParams, nextMVars, canonicalRight) ←
        canonicalAlphaLevel leftParams leftMVars right
      pure (nextParams, nextMVars, Json.mkObj [
        ("tag", Json.str "imax"), ("left", canonicalLeft), ("right", canonicalRight)])
  | .param name =>
      let (nextParams, index) := alphaNameIndex seenParams name
      pure (nextParams, seenMVars, Json.mkObj [
        ("tag", Json.str "param"), ("index", Json.str (toString index))])
  | .mvar id =>
      let (nextMVars, index) := alphaLevelMVarIndex seenMVars id
      pure (seenParams, nextMVars, Json.mkObj [
        ("tag", Json.str "mvar"), ("index", Json.str (toString index))])

/--
Canonical alpha representation for a closed endpoint.  It deliberately omits
all fvar and binder user names; an unexpected fvar is an error rather than an
opportunity to serialize a process-local fvar id.  Constant names remain the
Lean identity of imported/library declarations, but are not used to decide
whether the antecedent bridge is valid; `closedDefEq` above is the acceptance
test.
-/
private partial def canonicalAlphaExpr
    (seenParams : Array Name) (seenMVars : Array LMVarId) (expr : Expr) :
    MetaM (Array Name × Array LMVarId × Json) := do
  let expr ← instantiateMVars expr
  match expr with
  | .bvar index =>
      pure (seenParams, seenMVars, Json.mkObj [
        ("tag", Json.str "bvar"), ("index", Json.str (toString index))])
  | .fvar _ =>
      throwError "unclosed free variable in source-definition alpha evidence"
  | .mvar _ =>
      throwError "unresolved expression metavariable in source-definition alpha evidence"
  | .sort level =>
      let (nextParams, nextMVars, canonicalLevel) ←
        canonicalAlphaLevel seenParams seenMVars level
      pure (nextParams, nextMVars, Json.mkObj [
        ("tag", Json.str "sort"), ("level", canonicalLevel)])
  | .const name levels =>
      let mut nextParams := seenParams
      let mut nextMVars := seenMVars
      let mut canonicalLevels : Array Json := #[]
      for level in levels do
        let (updatedParams, updatedMVars, canonicalLevel) ←
          canonicalAlphaLevel nextParams nextMVars level
        nextParams := updatedParams
        nextMVars := updatedMVars
        canonicalLevels := canonicalLevels.push canonicalLevel
      pure (nextParams, nextMVars, Json.mkObj [
        ("tag", Json.str "const"),
        ("name", Json.str name.toString),
        ("levels", Json.arr canonicalLevels)])
  | .app fn arg =>
      let (fnParams, fnMVars, canonicalFn) ←
        canonicalAlphaExpr seenParams seenMVars fn
      let (nextParams, nextMVars, canonicalArg) ←
        canonicalAlphaExpr fnParams fnMVars arg
      pure (nextParams, nextMVars, Json.mkObj [
        ("tag", Json.str "app"), ("fn", canonicalFn), ("arg", canonicalArg)])
  | .lam _ domain body binderInfo =>
      let (domainParams, domainMVars, canonicalDomain) ←
        canonicalAlphaExpr seenParams seenMVars domain
      let (nextParams, nextMVars, canonicalBody) ←
        canonicalAlphaExpr domainParams domainMVars body
      pure (nextParams, nextMVars, Json.mkObj [
        ("tag", Json.str "lam"),
        ("binder_info", Json.str (binderInfoName binderInfo)),
        ("domain", canonicalDomain),
        ("body", canonicalBody)])
  | .forallE _ domain body binderInfo =>
      let (domainParams, domainMVars, canonicalDomain) ←
        canonicalAlphaExpr seenParams seenMVars domain
      let (nextParams, nextMVars, canonicalBody) ←
        canonicalAlphaExpr domainParams domainMVars body
      pure (nextParams, nextMVars, Json.mkObj [
        ("tag", Json.str "forall"),
        ("binder_info", Json.str (binderInfoName binderInfo)),
        ("domain", canonicalDomain),
        ("body", canonicalBody)])
  | .letE _ type value body nondep =>
      let (typeParams, typeMVars, canonicalType) ←
        canonicalAlphaExpr seenParams seenMVars type
      let (valueParams, valueMVars, canonicalValue) ←
        canonicalAlphaExpr typeParams typeMVars value
      let (nextParams, nextMVars, canonicalBody) ←
        canonicalAlphaExpr valueParams valueMVars body
      pure (nextParams, nextMVars, Json.mkObj [
        ("tag", Json.str "let"),
        ("type", canonicalType),
        ("value", canonicalValue),
        ("body", canonicalBody),
        ("nondep", Json.bool nondep)])
  | .lit literal =>
      pure (seenParams, seenMVars, Json.mkObj [
        ("tag", Json.str "lit"), ("value", Json.str (reprStr literal))])
  | .mdata _ body =>
      canonicalAlphaExpr seenParams seenMVars body
  | .proj typeName index structExpr =>
      let (nextParams, nextMVars, canonicalStruct) ←
        canonicalAlphaExpr seenParams seenMVars structExpr
      pure (nextParams, nextMVars, Json.mkObj [
        ("tag", Json.str "proj"),
        ("type_name", Json.str typeName.toString),
        ("index", Json.str (toString index)),
        ("structure", canonicalStruct)])

private def closedAlpha (binders : Array Expr) (body : Expr) : MetaM String := do
  let closed ← mkForallFVars binders body (usedOnly := true)
  let (_, _, canonical) ← canonicalAlphaExpr #[] #[] closed
  pure canonical.compress

/--
Close an open proposition over the declaration binders it actually uses, then
compare the resulting closed expressions.  Each declaration receives fresh
local constants while opening its telescope, so comparing the open terms would
make alpha-equivalent expressions appear different merely because their fvars
are distinct.  `usedOnly` also preserves the necessary dependent binders
without imposing irrelevant parameters from either declaration.
-/
private def closedDefEq
    (leftBinders : Array Expr) (left : Expr)
    (rightBinders : Array Expr) (right : Expr) : MetaM Bool :=
  withNewMCtxDepth do
    let closedLeft ← mkForallFVars leftBinders left (usedOnly := true)
    let closedRight ← mkForallFVars rightBinders right (usedOnly := true)
    withTransparency .all do
      isDefEq closedLeft closedRight

/--
Compare the elaborated structure of two open expressions without unfolding
definitions.  This is intentionally stricter than definitional equality: the
source-review formula side must visibly be the parsed raw expansion, even
when a transparent abbreviation makes both IFF sides definitionally equal.
Closing over the actual telescope removes fvar identities and binder spelling
from the comparison.
-/
private def closedAlphaEq
    (leftBinders : Array Expr) (left : Expr)
    (rightBinders : Array Expr) (right : Expr) : MetaM Bool := do
  let leftAlpha ← closedAlpha leftBinders left
  let rightAlpha ← closedAlpha rightBinders right
  pure (leftAlpha == rightAlpha)

private def parsePropositionText (label text : String) : TermElabM Expr := do
  let stx ←
    match Parser.runParserCategory (← getEnv) `term text with
    | .ok parsed => pure parsed
    | .error _ => throwError "could not parse {label} as a Lean proposition"
  let expression ←
    Term.withoutAutoBoundImplicit <|
      Term.withoutErrToSorry <|
        Term.elabTermEnsuringType stx (some (mkSort .zero)) false false
  Term.synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  if expression.hasMVar then
    throwError "{label} left unresolved expression metavariables"
  if expression.hasSorry then
    throwError "{label} contains an explicit sorry"
  if expression.hasSyntheticSorry then
    throwError "{label} elaborated through a synthetic sorry"
  pure expression

private def sideEndpoint? (side : String) (left right : Expr) : Option Expr :=
  if side == "left" then some left
  else if side == "right" then some right
  else none

/-- Collect the free local-variable coordinates occurring in an expression.
The returned order is not used as evidence: callers always project it back to
the declaration telescope's outer-binder order. -/
private partial def collectFVarIds
    (expr : Expr) (seen : Array FVarId := #[]) : Array FVarId :=
  match expr with
  | .bvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ => seen
  | .fvar id => if seen.contains id then seen else seen.push id
  | .app fn arg => collectFVarIds arg (collectFVarIds fn seen)
  | .lam _ domain body _ => collectFVarIds body (collectFVarIds domain seen)
  | .forallE _ domain body _ => collectFVarIds body (collectFVarIds domain seen)
  | .letE _ type value body _ =>
      collectFVarIds body (collectFVarIds value (collectFVarIds type seen))
  | .mdata _ body => collectFVarIds body seen
  | .proj _ _ structExpr => collectFVarIds structExpr seen

private def allFVarsBelongTo (expr : Expr) (binders : Array Expr) : Bool :=
  let permitted := binders.map Expr.fvarId!
  (collectFVarIds expr).all permitted.contains

/--
Take the transitive local-type dependency closure of formula variables, then
return it in declaration-telescope order.  This deliberately rejects a term
whose parser silently resolved one of its free variables in an outer,
unrelated telescope.
-/
private def relevantTelescopeBinders
    (allBinders roots : Array Expr) (label : String) : MetaM (Array Expr) := do
  let allIds := allBinders.map Expr.fvarId!
  let mut needed : Array FVarId := #[]
  for root in roots do
    for id in collectFVarIds root do
      if !allIds.contains id then
        throwError "{label} references a free variable outside its declaration telescope"
      if !needed.contains id then
        needed := needed.push id
  let mut changed := true
  while changed do
    changed := false
    for binder in allBinders do
      if needed.contains binder.fvarId! then
        let binderType ← inferType binder
        for id in collectFVarIds binderType do
          if !allIds.contains id then
            throwError "{label} binder type references a variable outside its declaration telescope"
          if !needed.contains id then
            needed := needed.push id
            changed := true
  pure <| allBinders.filter (fun binder => needed.contains binder.fvarId!)

private def outerBinderIndex? (allBinders : Array Expr) (binder : Expr) : Option Nat :=
  allBinders.findIdx? (fun candidate => candidate.fvarId! == binder.fvarId!)

/-! A deliberately tiny local permutation generator.  The helper is injected
after `import Lean`, not compiled as a Mathlib module, so it must not rely on
an incidental `List.permutations` import from the reviewed paper. -/
private def insertAtEveryPosition {α : Type u} (value : α) : List α → List (List α)
  | [] => [[value]]
  | head :: tail =>
      (value :: head :: tail) ::
        (insertAtEveryPosition value tail).map (fun rest => head :: rest)

private def boundedPermutations {α : Type u} : List α → List (List α)
  | [] => [[]]
  | head :: tail =>
      (boundedPermutations tail).flatMap (insertAtEveryPosition head)

/-- A candidate maps definition-telescope variables into lemma-telescope variables.
The mapping is accepted only when every mapped local type is definitionally
equal after the same simultaneous substitution. -/
private def mappingTypesCompatible
    (definitionRelevant lemmaTargets : Array Expr) : MetaM Bool := do
  if definitionRelevant.size != lemmaTargets.size then
    return false
  for index in List.range definitionRelevant.size do
    let definitionType ← inferType definitionRelevant[index]!
    let lemmaType ← inferType lemmaTargets[index]!
    let transportedDefinitionType :=
      definitionType.replaceFVars definitionRelevant lemmaTargets
    let compatible ← withTransparency .all do
      isDefEq transportedDefinitionType lemmaType
    if !compatible then
      return false
  return true

private structure CoherentParameterBridge where
  formulaSide : String
  reviewSurfaceMatchesActualIff : Bool
  reviewFormulaSideMatchesActual : Bool
  oppositeActualEndpointMatchesLemmaBinder : Bool
  parsedRawExpansionAlpha : String
  reviewLeftIffSideAlpha : String
  reviewRightIffSideAlpha : String
  actualLeftIffSideAlpha : String
  actualRightIffSideAlpha : String
  parameterCorrespondence : Array (Nat × Nat)

/--
Test one complete, type-checked coordinate map.  All formula comparisons now
occur in the *lemma* telescope, so a textual identifier is never rebound in a
different declaration context.
-/
private def coherentBridgeForMapping
    (lemmaBinders : Array Expr) (rawBinderType parsedRaw : Expr)
    (definitionBinders definitionRelevant lemmaTargets : Array Expr)
    (actualIff parsedReviewIff : Expr) : MetaM (Option CoherentParameterBridge) := do
  if !(← mappingTypesCompatible definitionRelevant lemmaTargets) then
    return none
  let transportedActualIff :=
    actualIff.replaceFVars definitionRelevant lemmaTargets
  let transportedReviewIff :=
    parsedReviewIff.replaceFVars definitionRelevant lemmaTargets
  if !allFVarsBelongTo transportedActualIff lemmaBinders
      || !allFVarsBelongTo transportedReviewIff lemmaBinders then
    return none
  if !transportedActualIff.isAppOfArity ``Iff 2
      || !transportedReviewIff.isAppOfArity ``Iff 2 then
    return none
  let actualArgs := transportedActualIff.getAppArgs
  let reviewArgs := transportedReviewIff.getAppArgs
  let actualLeft := actualArgs[0]!
  let actualRight := actualArgs[1]!
  let reviewLeft := reviewArgs[0]!
  let reviewRight := reviewArgs[1]!
  let rawAlpha ← closedAlpha lemmaBinders parsedRaw
  let reviewLeftAlpha ← closedAlpha lemmaBinders reviewLeft
  let reviewRightAlpha ← closedAlpha lemmaBinders reviewRight
  let actualLeftAlpha ← closedAlpha lemmaBinders actualLeft
  let actualRightAlpha ← closedAlpha lemmaBinders actualRight
  let rawCandidates :=
    #[
      ("left", reviewLeftAlpha == rawAlpha),
      ("right", reviewRightAlpha == rawAlpha),
    ].filter (fun (_, isMatch) => isMatch)
  if rawCandidates.size != 1 then
    return none
  let formulaSide := rawCandidates[0]!.1
  let selectedReview := if formulaSide == "left" then reviewLeft else reviewRight
  let selectedActual := if formulaSide == "left" then actualLeft else actualRight
  let oppositeActual := if formulaSide == "left" then actualRight else actualLeft
  let reviewSurfaceMatchesActualIff ←
    closedAlphaEq lemmaBinders transportedReviewIff lemmaBinders transportedActualIff
  let reviewFormulaSideMatchesActual ←
    closedAlphaEq lemmaBinders selectedReview lemmaBinders selectedActual
  let oppositeActualEndpointMatchesLemmaBinder ←
    closedDefEq lemmaBinders oppositeActual lemmaBinders rawBinderType
  if !reviewSurfaceMatchesActualIff
      || !reviewFormulaSideMatchesActual
      || !oppositeActualEndpointMatchesLemmaBinder then
    return none
  let mut coordinates : Array (Nat × Nat) := #[]
  for index in List.range definitionRelevant.size do
    let some definitionIndex := outerBinderIndex? definitionBinders definitionRelevant[index]!
      | return none
    let some lemmaIndex := outerBinderIndex? lemmaBinders lemmaTargets[index]!
      | return none
    coordinates := coordinates.push (definitionIndex, lemmaIndex)
  return some {
    formulaSide := formulaSide
    reviewSurfaceMatchesActualIff := reviewSurfaceMatchesActualIff
    reviewFormulaSideMatchesActual := reviewFormulaSideMatchesActual
    oppositeActualEndpointMatchesLemmaBinder := oppositeActualEndpointMatchesLemmaBinder
    parsedRawExpansionAlpha := rawAlpha
    reviewLeftIffSideAlpha := reviewLeftAlpha
    reviewRightIffSideAlpha := reviewRightAlpha
    actualLeftIffSideAlpha := actualLeftAlpha
    actualRightIffSideAlpha := actualRightAlpha
    parameterCorrespondence := coordinates }

private def inspectBridge
    (lemmaName : Name) (binderIndex : Nat)
    (definitionName : Name) (requestedSide : String) : MetaM BridgeVerdict :=
  withNewMCtxDepth do
    let lemmaConst ← mkConstWithFreshMVarLevels lemmaName
    let lemmaType ← inferType lemmaConst
    forallTelescopeReducing lemmaType fun lemmaBinders _ => do
      if binderIndex >= lemmaBinders.size then
        return failure "lemma_binder_index_out_of_range"
      let rawBinderType ← inferType lemmaBinders[binderIndex]!
      let rawBinderDisplay := (← ppExpr rawBinderType).pretty

      let definitionConst ← mkConstWithFreshMVarLevels definitionName
      let definitionType ← inferType definitionConst
      forallTelescopeReducing definitionType fun definitionBinders definitionResult => do
        let definitionResult ← whnf definitionResult
        if !definitionResult.isAppOfArity ``Iff 2 then
          return {
            iffIsSyntactic := false
            lemmaBinderType := rawBinderDisplay
            failureTag := "definition_result_not_iff" }
        let iffArgs := definitionResult.getAppArgs
        let left := iffArgs[0]!
        let right := iffArgs[1]!
        let some requestedEndpoint := sideEndpoint? requestedSide left right
          | return {
              iffIsSyntactic := true
              lemmaBinderType := rawBinderDisplay
              failureTag := "invalid_requested_iff_side" }

        let definitionIffDisplay := (← ppExpr definitionResult).pretty
        let rawBinderAlpha ← closedAlpha lemmaBinders rawBinderType
        let leftAlpha ← closedAlpha definitionBinders left
        let rightAlpha ← closedAlpha definitionBinders right
        let leftMatches ← closedDefEq lemmaBinders rawBinderType definitionBinders left
        let rightMatches ← closedDefEq lemmaBinders rawBinderType definitionBinders right
        let mut matchingSides : Array String := #[]
        if leftMatches then
          matchingSides := matchingSides.push "left"
        if rightMatches then
          matchingSides := matchingSides.push "right"
        let requestedSideMatches :=
          if requestedSide == "left" then leftMatches else rightMatches
        pure {
          iffIsSyntactic := true
          matchingIffSides := matchingSides
          requestedSideMatches := requestedSideMatches
          lemmaBinderType := rawBinderDisplay
          requestedEndpointType := (← ppExpr requestedEndpoint).pretty
          definitionIffDisplay := definitionIffDisplay
          lemmaBinderAlpha := rawBinderAlpha
          leftIffSideAlpha := leftAlpha
          rightIffSideAlpha := rightAlpha }

/--
Inspect the mathematical formula bridge without allowing Python to select an
IFF orientation.  The raw expansion and reviewed full IFF are parsed and
elaborated in the declaration telescopes that actually govern them.  The
formula side is chosen only by exact alpha-structural equality of elaborated
terms; transparent aliases are deliberately *not* unfolded for that choice.

The subsequent `.all` checks establish the intended mathematical bridge:
the parsed raw expansion is definitionally equal to the source-result
antecedent, and the opposite actual definition endpoint is definitionally
equal to that antecedent.  The full reviewed IFF must also structurally match
the actual definition result, preventing an unrelated hidden side from being
smuggled into the source-review surface.
-/
private def inspectSemanticFormulaBridge
    (lemmaName : Name) (binderIndex : Nat)
    (definitionName : Name) (rawExpansion reviewSurface : String) :
    TermElabM BridgeVerdict :=
  withNewMCtxDepth do
    let lemmaConst ← mkConstWithFreshMVarLevels lemmaName
    let lemmaType ← inferType lemmaConst
    forallTelescopeReducing lemmaType fun lemmaBinders _ => do
      if binderIndex >= lemmaBinders.size then
        return failure "lemma_binder_index_out_of_range"
      let rawBinderType ← inferType lemmaBinders[binderIndex]!
      let parsedRawInLemma ← parsePropositionText "raw expansion" rawExpansion
      let rawExpansionMatchesLemmaBinder ←
        closedDefEq lemmaBinders parsedRawInLemma lemmaBinders rawBinderType
      let lemmaRelevant ← relevantTelescopeBinders
        lemmaBinders #[parsedRawInLemma, rawBinderType] "raw lemma formula"

      let definitionConst ← mkConstWithFreshMVarLevels definitionName
      let definitionType ← inferType definitionConst
      forallTelescopeReducing definitionType fun definitionBinders definitionResult => do
        let definitionResult ← whnf definitionResult
        if !definitionResult.isAppOfArity ``Iff 2 then
          return {
            schema := "2"
            lemmaBinderType := (← ppExpr rawBinderType).pretty
            rawExpansionMatchesLemmaBinder := rawExpansionMatchesLemmaBinder
            failureTag := "definition_result_not_iff" }
        let actualIffArgs := definitionResult.getAppArgs
        let actualLeft := actualIffArgs[0]!
        let actualRight := actualIffArgs[1]!
        let parsedReviewSurface ←
          parsePropositionText "reviewed source-definition IFF surface" reviewSurface
        let parsedReviewSurface ← whnf parsedReviewSurface
        if !parsedReviewSurface.isAppOfArity ``Iff 2 then
          return {
            schema := "3"
            rawExpansionMatchesLemmaBinder := rawExpansionMatchesLemmaBinder
            reviewSurfaceIsSyntacticIff := false
            lemmaBinderType := (← ppExpr rawBinderType).pretty
            definitionIffDisplay := (← ppExpr definitionResult).pretty
            failureTag := "review_surface_not_iff" }
        -- The definition telescope is nested inside the lemma telescope while
        -- this Meta command runs.  Reject any accidental resolution of review
        -- text to a lemma-local variable before attempting a coordinate map.
        if !allFVarsBelongTo parsedReviewSurface definitionBinders
            || !allFVarsBelongTo definitionResult definitionBinders then
          return {
            schema := "3"
            rawExpansionMatchesLemmaBinder := rawExpansionMatchesLemmaBinder
            reviewSurfaceIsSyntacticIff := true
            lemmaBinderType := (← ppExpr rawBinderType).pretty
            definitionIffDisplay := (← ppExpr definitionResult).pretty
            failureTag := "definition_review_uses_non_definition_telescope_variable" }
        let definitionRelevant ← relevantTelescopeBinders
          definitionBinders #[parsedReviewSurface, definitionResult]
            "reviewed definition formula"
        if lemmaRelevant.size != definitionRelevant.size then
          return {
            schema := "3"
            rawExpansionMatchesLemmaBinder := rawExpansionMatchesLemmaBinder
            reviewSurfaceIsSyntacticIff := true
            lemmaBinderType := (← ppExpr rawBinderType).pretty
            definitionIffDisplay := (← ppExpr definitionResult).pretty
            failureTag := "definition_and_lemma_parameter_closures_have_different_sizes" }
        if lemmaRelevant.size > 6 then
          return {
            schema := "3"
            rawExpansionMatchesLemmaBinder := rawExpansionMatchesLemmaBinder
            reviewSurfaceIsSyntacticIff := true
            lemmaBinderType := (← ppExpr rawBinderType).pretty
            definitionIffDisplay := (← ppExpr definitionResult).pretty
            failureTag := "parameter_correspondence_search_too_wide" }
        let mut coherentCandidates : Array CoherentParameterBridge := #[]
        for targetList in boundedPermutations lemmaRelevant.toList do
          let some candidate ← coherentBridgeForMapping
            lemmaBinders rawBinderType parsedRawInLemma
            definitionBinders definitionRelevant targetList.toArray
            definitionResult parsedReviewSurface
            | pure ()
          coherentCandidates := coherentCandidates.push candidate
        if coherentCandidates.size != 1 then
          return {
            schema := "3"
            rawExpansionMatchesLemmaBinder := rawExpansionMatchesLemmaBinder
            reviewSurfaceIsSyntacticIff := true
            lemmaBinderType := (← ppExpr rawBinderType).pretty
            definitionIffDisplay := (← ppExpr definitionResult).pretty
            failureTag :=
              if coherentCandidates.isEmpty then
                "no_coherent_type_checked_parameter_correspondence"
              else
                "ambiguous_coherent_type_checked_parameter_correspondence" }
        let some coherent := coherentCandidates[0]?
          | return failure "coherent_parameter_correspondence_disappeared"
        let rawBinderAlpha ← closedAlpha lemmaBinders rawBinderType
        let failureTag :=
          if !rawExpansionMatchesLemmaBinder then
            "raw_expansion_does_not_match_lemma_binder"
          else ""
        pure {
          schema := "3"
          iffIsSyntactic := true
          matchingIffSides := #[coherent.formulaSide]
          rawExpansionMatchesLemmaBinder := rawExpansionMatchesLemmaBinder
          reviewSurfaceIsSyntacticIff := true
          reviewSurfaceMatchesActualIff := coherent.reviewSurfaceMatchesActualIff
          reviewFormulaIffSide := coherent.formulaSide
          reviewFormulaSelectionMethod := "syntactic_alpha_under_unique_coordinate_bijection"
          reviewFormulaSideMatchesActual := coherent.reviewFormulaSideMatchesActual
          oppositeActualEndpointMatchesLemmaBinder :=
            coherent.oppositeActualEndpointMatchesLemmaBinder
          lemmaBinderType := (← ppExpr rawBinderType).pretty
          requestedEndpointType := "transported-opposite-definition-endpoint"
          definitionIffDisplay := (← ppExpr definitionResult).pretty
          lemmaBinderAlpha := rawBinderAlpha
          leftIffSideAlpha := coherent.actualLeftIffSideAlpha
          rightIffSideAlpha := coherent.actualRightIffSideAlpha
          parsedRawExpansionAlpha := coherent.parsedRawExpansionAlpha
          reviewLeftIffSideAlpha := coherent.reviewLeftIffSideAlpha
          reviewRightIffSideAlpha := coherent.reviewRightIffSideAlpha
          actualLeftIffSideAlpha := coherent.actualLeftIffSideAlpha
          actualRightIffSideAlpha := coherent.actualRightIffSideAlpha
          parameterCorrespondenceEstablished := true
          parameterCorrespondenceMethod := "unique_type_checked_coordinate_bijection"
          parameterCorrespondence := coherent.parameterCorrespondence
          failureTag := failureTag }

private def verdictJson
    (lemmaName definitionName : Name) (binderIndex : String) (requestedSide : String)
    (verdict : BridgeVerdict) : Json :=
  Json.mkObj [
    ("schema", Json.str verdict.schema),
    ("lemma", Json.str lemmaName.toString),
    ("definition", Json.str definitionName.toString),
    ("lemma_binder_index", Json.str binderIndex),
    ("requested_iff_side", Json.str requestedSide),
    ("iff_is_syntactic", Json.bool verdict.iffIsSyntactic),
    ("matching_iff_sides", Json.arr (verdict.matchingIffSides.map Json.str)),
    ("requested_side_matches", Json.bool verdict.requestedSideMatches),
    ("raw_expansion_matches_lemma_binder", Json.bool verdict.rawExpansionMatchesLemmaBinder),
    ("review_surface_is_syntactic_iff", Json.bool verdict.reviewSurfaceIsSyntacticIff),
    ("review_surface_matches_actual_iff", Json.bool verdict.reviewSurfaceMatchesActualIff),
    ("review_formula_iff_side", Json.str verdict.reviewFormulaIffSide),
    ("review_formula_selection_method", Json.str verdict.reviewFormulaSelectionMethod),
    ("review_formula_side_matches_actual", Json.bool verdict.reviewFormulaSideMatchesActual),
    ("opposite_actual_endpoint_matches_lemma_binder", Json.bool verdict.oppositeActualEndpointMatchesLemmaBinder),
    ("lemma_binder_type", Json.str verdict.lemmaBinderType),
    ("requested_endpoint_type", Json.str verdict.requestedEndpointType),
    ("definition_iff_display", Json.str verdict.definitionIffDisplay),
    ("lemma_binder_alpha", Json.str verdict.lemmaBinderAlpha),
    ("left_iff_side_alpha", Json.str verdict.leftIffSideAlpha),
    ("right_iff_side_alpha", Json.str verdict.rightIffSideAlpha),
    ("parsed_raw_expansion_alpha", Json.str verdict.parsedRawExpansionAlpha),
    ("review_left_iff_side_alpha", Json.str verdict.reviewLeftIffSideAlpha),
    ("review_right_iff_side_alpha", Json.str verdict.reviewRightIffSideAlpha),
    ("actual_left_iff_side_alpha", Json.str verdict.actualLeftIffSideAlpha),
    ("actual_right_iff_side_alpha", Json.str verdict.actualRightIffSideAlpha),
    ("parameter_correspondence_established", Json.bool verdict.parameterCorrespondenceEstablished),
    ("parameter_correspondence_method", Json.str verdict.parameterCorrespondenceMethod),
    ("parameter_correspondence", Json.arr (verdict.parameterCorrespondence.map fun (definitionIndex, lemmaIndex) =>
      Json.mkObj [
        ("definition_binder_index", Json.str (toString definitionIndex)),
        ("lemma_binder_index", Json.str (toString lemmaIndex))])),
    ("failure_tag", Json.str verdict.failureTag)]

syntax (name := sourceDefinitionAntecedentBridgeCmd)
  "#source_definition_antecedent_bridge " str str str str : command

elab_rules : command
  | `(#source_definition_antecedent_bridge
      $lemmaToken:str $binderToken:str $iffToken:str $sideToken:str) => do
      let lemmaName := lemmaToken.getString.toName
      let definitionName := iffToken.getString.toName
      let binderIndexString := binderToken.getString
      let requestedSide := sideToken.getString
      let verdict ←
        match binderIndexString.toNat? with
        | none => pure (failure "invalid_lemma_binder_index")
        | some binderIndex =>
            try
              liftTermElabM <|
                inspectBridge lemmaName binderIndex definitionName requestedSide
            catch _ =>
              pure (failure "meta_inspection_failed")
      let result := verdictJson lemmaName definitionName binderIndexString requestedSide verdict
      IO.println s!"SOURCE_DEFINITION_ANTECEDENT_META:{result.compress}"

/--
Formula-bearing bridge command.  Unlike the compatibility command above, it
does not accept a caller-selected IFF side: Lean parses both review sides and
returns the unique structural raw-formula side itself.
-/
syntax (name := sourceDefinitionAntecedentSemanticBridgeCmd)
  "#source_definition_antecedent_semantic_bridge " str str str str str : command

elab_rules : command
  | `(#source_definition_antecedent_semantic_bridge
      $lemmaToken:str $binderToken:str $iffToken:str $rawToken:str $reviewToken:str) => do
      let lemmaName := lemmaToken.getString.toName
      let definitionName := iffToken.getString.toName
      let binderIndexString := binderToken.getString
      let verdict ←
        match binderIndexString.toNat? with
        | none => pure { schema := "2", failureTag := "invalid_lemma_binder_index" }
        | some binderIndex =>
            try
              liftTermElabM <|
                inspectSemanticFormulaBridge lemmaName binderIndex definitionName
                  rawToken.getString reviewToken.getString
            catch _ =>
              pure { schema := "2", failureTag := "semantic_formula_inspection_failed" }
      let result := verdictJson lemmaName definitionName binderIndexString "" verdict
      IO.println s!"SOURCE_DEFINITION_ANTECEDENT_META:{result.compress}"

end EconCSLibAudit.SourceDefinitionAntecedent
