module

public import Mathlib.Order.WithBot
public import Mathlib.Tactic.MetaInterval.Interval
public import Lean.Compiler.IR.CompilerM

set_option linter.style.header false

@[expose] public section

open Lean Meta Elab Term

namespace IntervalArithmetic

initialize registerTraceClass `Tactic.interval

/-- Maybe generalize to other interval types -/
structure IntervalCertificate where
  expr : Expr
  intervalExpr : Expr
  proof : Expr
  deriving Inhabited

structure CertificateGenerator where
  params : Array FVarId
  ivarIds : Array Expr
  /-- `intervalExpr` is an expression of the form
  `λ (n₁ : ℕ) ... (nₘ : ℕ) (I₁ : Interval Dyadic) ... (Iᵢ : Interval Dyadic), f n₁ .. nₘ I₁ .. Iᵢ`
  -/
  intervalExpr : Expr
  /-- `intervalComp` is a compiled version of `intervalExpr` -/
  intervalComp : Array ℕ → Array (Interval Dyadic) → Interval Dyadic
  /-- `proof` is a proof of:
  `∀ (n₁ : ℕ) ... (nₘ : ℕ), (x₁ : ℝ) .. (xᵢ : ℝ),`
    `(I₁ : Interval Dyadic) .. (Iᵢ : Interval Dyadic),`
    `(h₁ : x₁ ∈ I₁.toSet φ) ... (hᵢ : xᵢ ∈ Iᵢ.toSet φ) :`
    `(e x₁ .. xᵢ) ∈ (f n₁ .. nₘ I₁ .. Iᵢ).map Dyadic.toReal).toSet`
  -/
  proof : Expr
  deriving Inhabited

structure CertificateGeneratorM.Context where
  numParams : ℕ
  deriving Inhabited

structure CertificateGeneratorM.State where
  fvars : FVarIdSet
  ivars : ExprMap (Expr × Expr)
  intervalExprBody : Expr
  intevalCompBody : Expr
  intervalProofBody : Expr
  deriving Inhabited

abbrev CertificateGeneratorM :=
  ReaderT CertificateGeneratorM.Context <| StateT CertificateGeneratorM.State MetaM

instance :
    MonadBacktrack (Meta.SavedState × CertificateGeneratorM.State) CertificateGeneratorM where
  saveState := do return ⟨← Meta.saveState, ← get⟩
  restoreState s := do
    s.1.restore
    set s.2

structure IntervalExt where
  name : Name := by exact decl_name%
  eval (e : Expr) : CertificateGeneratorM Unit
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
    throwError "'{declName}' does not have [interval] attribute"
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

/-- The `interval` attribute registers an interval certificate extension. -/
initialize registerBuiltinAttribute {
  name := `intervalExtAttr
  descr := "adds an interval arithmetic extension"
  applicationTime := .afterCompilation
  add := fun declName stx kind => match stx with
    | `(attr| intervalExt $es,*) => do
      let env ← getEnv
      ensureAttrDeclIsMeta `interval declName kind
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

def toCertificateGenerator (e : Expr) : MetaM CertificateGenerator :=
    -- define a custom run function if we stick with this...
    ((go e).run default).run' default where
  go (e : Expr) : CertificateGeneratorM CertificateGenerator := do
    let s ← saveState
    let intervalExts := intervalExt.getState (← getEnv)
    let exts ← intervalExts.tree.getMatch e
    let exts := exts.qsort (fun ext₁ ext₂ ↦ ext₁.priority < ext₂.priority)
    for ext in exts do
      if ! intervalExts.erased.contains ext.name then
        try
          ext.eval e
          recordExtraModUseFromDecl (isMeta := true) ext.name
          trace[Tactic.interval] "{ext.name} applied to {e}"
          return ← mkCertificateGenerator
        catch err =>
          trace[Tactic.interval] "Failed to apply {ext.name} to {e} : {err.toMessageData}"
          restoreState s
    throwError "{e}: no interval extensions apply"


structure IntervalM.State where
  cache : ExprMap IntervalCertificate := {}
  deriving Inhabited

abbrev IntervalM := StateT IntervalM.State MetaM

end IntervalArithmetic
