module

public import Mathlib.Order.WithBot
public import Mathlib.Tactic.MetaInterval.Dyadic
public import Mathlib.Tactic.MetaInterval.Expr
public import Lean.Compiler.IR.CompilerM
public import Qq

set_option linter.style.header false

@[expose] public section

open Lean Meta Elab Term Qq

namespace IntervalArithmetic

initialize registerTraceClass `Tactic.interval

structure IntervalCertificate where
  expr : Expr
  intervalExpr : Expr
  proof : Expr
  deriving Inhabited

structure IntervalM.State where
  cache : ExprMap (IntervalCertificate × Interval Dyadic) := {}
  deriving Inhabited

abbrev IntervalM := StateT IntervalM.State MetaM

abbrev IntervalComp := Array ℕ → Array (Interval Dyadic) → Interval Dyadic

structure PureCertificateFunction where
  /-- `intervalExpr` is an expression of the form
  `λ (n₁ : ℕ) ... (nₘ : ℕ) (I₁ : Interval Dyadic) ... (Iᵢ : Interval Dyadic), f n₁ .. nₘ I₁ .. Iᵢ`.
  -/
  intervalExpr : Expr
  /-- `intervalComp` is a compiled version of `intervalExpr`. -/
  intervalComp : IntervalComp
  /-- `proof` is a proof of:
  `∀ (n₁ : ℕ) ... (nₘ : ℕ), (x₁ : ℝ) .. (xᵢ : ℝ),`
    `(I₁ : Interval Dyadic) .. (Iᵢ : Interval Dyadic),`
    `(h₁ : x₁ ∈ (I₁.map Dyadic.toReal).toSet) ...`
    `(hᵢ : xᵢ ∈ (Iᵢ.map Dyadic.toReal).toSet) :`
    `(e x₁ .. xᵢ) ∈ ((f n₁ .. nₘ I₁ .. Iᵢ).map Dyadic.toReal).toSet`. -/
  proof : Expr
  deriving Inhabited

abbrev MetaCertificateFunction :=
  Array Expr → Array Expr → Array Expr → Array Expr →
    Array ℕ → Array (Interval Dyadic) →
    IntervalM (IntervalCertificate × Interval Dyadic)

inductive CertificateFunction
  | pureCert : PureCertificateFunction → CertificateFunction
  | metaCert : MetaCertificateFunction → CertificateFunction
  deriving Inhabited

structure CertificateGenerator where
  params : Array Expr
  iVarExprs : Array Expr
  fn : CertificateFunction
  deriving Inhabited

structure PureCertificateBody where
  intervalExprBody : Expr
  intervalCompBody : Expr
  intervalProofBody : Expr
  deriving Inhabited

structure MetaCertificateBody where
  body : Expr
  deriving Inhabited

inductive CertificateBody where
  | pureBody : PureCertificateBody → CertificateBody
  | metaBody : MetaCertificateBody → CertificateBody
  deriving Inhabited

structure CertificateGeneratorM.Context where
  params : Array FVarId
  localContext : LocalContext
  localInstances : LocalInstances
  deriving Inhabited

structure IVarData where
  exprVar : Expr
  intervalExprVar : Expr
  intervalVar : Expr
  hypVar : Expr
  deriving Inhabited

structure CertificateGeneratorM.State where
  fvars : FVarIdSet
  ivars : ExprMap IVarData
  deriving Inhabited

abbrev CertificateGeneratorM :=
  ReaderT CertificateGeneratorM.Context <| StateT CertificateGeneratorM.State MetaM

def CertificateGeneratorM.run {α : Type} (x : CertificateGeneratorM α)
    (params : Array FVarId := #[]) : MetaM α := do
  let localContext ← getLCtx
  let localInstances ← getLocalInstances
  StateT.run' (ReaderT.run x { params, localContext, localInstances }) default

def mkIVar (e : Expr) : CertificateGeneratorM IVarData := do
  let ctx ← read
  unless ← MetavarContext.isWellFormed ctx.localContext e do
    throwError "Cannot create an interval variable for {e} because it depends on variables \
      introduced while constructing the certificate"
  let eType ← inferType e
  unless ← MetavarContext.isWellFormed ctx.localContext eType do
    throwError "Cannot create an interval variable for {e} because its type depends on variables \
      introduced while constructing the certificate"
  let exprVar ←
    mkFreshExprMVarAt ctx.localContext ctx.localInstances eType .syntheticOpaque
  let intervalExprVar ←
    mkFreshExprMVarAt ctx.localContext ctx.localInstances q(Interval Dyadic) .syntheticOpaque
  let intervalVar ←
    mkFreshExprMVarAt ctx.localContext ctx.localInstances q(Interval Dyadic) .syntheticOpaque
  let hypType ← mkIntervalMem exprVar intervalExprVar (mkConst ``Dyadic.toReal)
  let hypVar ←
    mkFreshExprMVarAt ctx.localContext ctx.localInstances hypType .syntheticOpaque
  let data := ⟨exprVar, intervalExprVar, intervalVar, hypVar⟩
  modify fun state => { state with ivars := state.ivars.insert e data }
  return data

def IVarData.toCertificateBody (data : IVarData) : CertificateBody :=
  .pureBody ⟨data.intervalExprVar, data.intervalVar, data.hypVar⟩

def compileIntervalComp (params intervals : Array Expr) (body : PureCertificateBody) :
    MetaM IntervalComp := do
  withLocalDeclD `params q(Array ℕ) fun params' => do
    withLocalDeclD `intervals q(Array (Interval Dyadic)) fun intervals' => do
      let getParams ← params.mapIdxM fun i _ => do
        mkAppM ``getElem! #[params', mkNatLit i]
      let getIntervals ← intervals.mapIdxM fun i _ => do
        mkAppM ``getElem! #[intervals', mkNatLit i]
      let intervalCompBody ← body.intervalCompBody.replaceFVarsM
        (params ++ intervals) (getParams ++ getIntervals)
      let intervalComp ← mkLambdaFVars #[params', intervals'] intervalCompBody
      unsafe evalExpr IntervalComp q(IntervalComp) intervalComp

def compileMetaCertificateFn (paramExprs iVarIds intervalExprs hyps intervals : Array Expr)
    (body : MetaCertificateBody) : MetaM MetaCertificateFunction := do
  withLocalDeclD `paramExprs q(Array Expr) fun paramExprs' => do
    withLocalDeclD `iVarIds q(Array Expr) fun iVarIds' => do
      withLocalDeclD `intervalExprs q(Array Expr) fun intervalExprs' => do
        withLocalDeclD `hyps q(Array Expr) fun hyps' => do
          withLocalDeclD `params q(Array ℕ) fun params' => do
            withLocalDeclD `intervals q(Array (Interval Dyadic)) fun intervals' => do
              let getParamExprs ← paramExprs.mapIdxM fun i _ => do
                mkAppM ``getElem! #[paramExprs', mkNatLit i]
              let getIVarIds ← iVarIds.mapIdxM fun i _ => do
                mkAppM ``getElem! #[iVarIds', mkNatLit i]
              let getIntervalExprs ← intervalExprs.mapIdxM fun i _ => do
                mkAppM ``getElem! #[intervalExprs', mkNatLit i]
              let getHyps ← hyps.mapIdxM fun i _ => do
                mkAppM ``getElem! #[hyps', mkNatLit i]
              let getIntervals ← intervals.mapIdxM fun i _ => do
                mkAppM ``getElem! #[intervals', mkNatLit i]
              let fnBody ← body.body.replaceFVarsM
                (paramExprs ++ iVarIds ++ intervalExprs ++ hyps ++ intervals)
                (getParamExprs ++ getIVarIds ++ getIntervalExprs ++ getHyps ++ getIntervals)
              let fn ← mkLambdaFVars
                #[paramExprs', iVarIds', intervalExprs', hyps', params', intervals'] fnBody
              unsafe evalExpr MetaCertificateFunction q(MetaCertificateFunction) fn

def mkCertificateGenerator (body : CertificateBody) :
    CertificateGeneratorM CertificateGenerator := do
  let allowedParamIds := (← read).params
  let state ← get
  let fvars := state.fvars
  let allowedParams := allowedParamIds.foldl (init := ({} : FVarIdSet)) fun params param =>
    params.insert param
  for fvar in fvars do
    unless allowedParams.contains fvar do
      throwError "Unaccounted free variable {mkFVar fvar} in interval certificate generator; \
        it was not set as a parameter by the interval tactic"
  let params := (allowedParamIds.filter fvars.contains).map mkFVar
  for param in params do
    unless ← isDefEq (← inferType param) (mkConst ``Nat) do
      throwError "Cannot compile interval parameter {param} of type {← inferType param}; \
        expected type ℕ"
  let (iVarExprs, iVarData) := state.ivars.toArray.unzip
  let iVars := iVarData.map (·.exprVar)
  let intervalExprs := iVarData.map (·.intervalExprVar)
  let intervals := iVarData.map (·.intervalVar)
  let hyps := iVarData.map (·.hypVar)
  let fn ← match body with
  | .pureBody body => do
    let intervalExpr ← mkLambdaFVars (params ++ intervalExprs) body.intervalExprBody
      (binderInfoForMVars := .default)
    let intervalComp ← compileIntervalComp params intervals body
    let intervalProofBody ← mkLambdaFVars (intervalExprs ++ hyps) body.intervalProofBody
      (binderInfoForMVars := .default)
    let intervalProof ← mkLambdaFVars (params ++ iVars) intervalProofBody
      (binderInfoForMVars := .default)
    pure (CertificateFunction.pureCert ⟨intervalExpr, intervalComp, intervalProof⟩)
  | .metaBody body =>
    let metaFn ← compileMetaCertificateFn params iVars intervalExprs hyps intervals body
    pure (CertificateFunction.metaCert metaFn)
  return ⟨params, iVarExprs, fn⟩

instance :
    MonadBacktrack (Meta.SavedState × CertificateGeneratorM.State) CertificateGeneratorM where
  saveState := do return ⟨← Meta.saveState, ← get⟩
  restoreState s := do
    s.1.restore
    set s.2

structure IntervalExt where
  name : Name := by exact decl_name%
  eval (e : Expr) : CertificateGeneratorM CertificateBody
  priority : Nat := eval_prio default

def mkIntervalExt (n : Name) : ImportM IntervalExt := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck IntervalExt opts ``IntervalExt n

abbrev Entry := Array (Array DiscrTree.Key) × Name

structure IntervalExts where
  tree : DiscrTree IntervalExt := {}
  erased : PHashSet Name := {}
  deriving Inhabited

def IntervalExts.eraseCore (exts : IntervalExts) (declName : Name) : IntervalExts :=
  { exts with erased := exts.erased.insert declName }

def IntervalExts.erase {m : Type → Type} [Monad m] [MonadError m]
    (exts : IntervalExts) (declName : Name) : m IntervalExts := do
  unless exts.tree.values.any (·.name == declName) && !exts.erased.contains declName do
    throwError "'{declName}' does not have [intervalExt] attribute"
  return exts.eraseCore declName

initialize intervalExt : ScopedEnvExtension Entry (Entry × IntervalExt) IntervalExts ←
  have : BEq IntervalExt := ⟨fun _ _ ↦ false⟩
  let insert kss v dt := kss.foldl (fun dt ks ↦ dt.insertKeyValue ks v) dt
  registerScopedEnvExtension {
    mkInitial := pure {}
    ofOLeanEntry := fun _ e@(_, n) ↦ return (e, ← mkIntervalExt n)
    toOLeanEntry := (·.1)
    addEntry := fun { tree, erased } ((kss, n), ext) ↦
      { tree := insert kss ext tree, erased := erased.erase n }
  }

syntax (name := intervalExtAttr) "intervalExt" term,+ : attr

/-- The `intervalExt` attribute registers an interval certificate extension. -/
initialize registerBuiltinAttribute {
  name := `intervalExtAttr
  descr := "adds an interval arithmetic extension"
  applicationTime := .afterCompilation
  add := fun declName stx kind => match stx with
    | `(attr| intervalExt $es,*) => do
      let env ← getEnv
      ensureAttrDeclIsMeta `intervalExt declName kind
      unless (env.getModuleIdxFor? declName).isNone do
        throwError "invalid attribute `intervalExt`, declaration is in an imported module"
      if (IR.getSorryDep env declName).isSome then return -- ignore in progress definitions
      let ext ← mkIntervalExt declName
      let keys ← MetaM.run' <| es.getElems.mapM fun stx ↦ do
        let e ← TermElabM.run' <| withSaveInfoContext <| withAutoBoundImplicit <|
          withReader ({ · with ignoreTCFailures := true }) do
            let e ← elabTerm stx none
            let (_, _, e) ← lambdaMetaTelescope (← mkLambdaFVars (← getLCtx).getFVars e)
            return e
        DiscrTree.mkPath e
      intervalExt.add ((keys, declName), ext) kind
    | _ => throwUnsupportedSyntax
  erase := fun declName => do
    let s := intervalExt.getState (← getEnv)
    let s ← s.erase declName
    modifyEnv fun env => intervalExt.modifyState env fun _ => s
}

def mkCertificateBody (e : Expr) : CertificateGeneratorM CertificateBody := do
  if let some data := (← get).ivars[e]? then
    trace[Tactic.interval] "Reusing ivar for {e}"
    return data.toCertificateBody
  if e.isFVar && (← isDefEq (← inferType e) (mkConst ``Real)) then
    let data ← mkIVar e
    trace[Tactic.interval] "Creating ivar for free variable {e}"
    return data.toCertificateBody
  let s ← saveState
  let intervalExts := intervalExt.getState (← getEnv)
  let exts ← intervalExts.tree.getMatch e
  let exts := exts.qsort (fun ext₁ ext₂ ↦ ext₁.priority < ext₂.priority)
  for ext in exts do
    if ! intervalExts.erased.contains ext.name then
      try
        let body ← ext.eval e
        recordExtraModUseFromDecl (isMeta := true) ext.name
        trace[Tactic.interval] "{ext.name} applied to {e}"
        return body
      catch err =>
        trace[Tactic.interval] "Failed to apply {ext.name} to {e} : {err.toMessageData}"
        restoreState s
  if ← isDefEq (← inferType e) (mkConst ``Real) then
    let data ← mkIVar e
    trace[Tactic.interval] "No extension applied to {e}; created an ivar"
    return data.toCertificateBody
  throwError "{e} is not a real expression or depends on bound variables and no interval
    extensions apply"

def toCertificateGenerator (e : Expr) (params : Array FVarId := #[]) :
    MetaM CertificateGenerator :=
  CertificateGeneratorM.run (params := params) do
    let body ← mkCertificateBody e
    mkCertificateGenerator body

end IntervalArithmetic
