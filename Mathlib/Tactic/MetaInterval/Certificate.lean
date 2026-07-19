module

public import Mathlib.Order.WithBot
public import Mathlib.Tactic.MetaInterval.Interval

set_option linter.style.header false

@[expose] public section

open Lean Meta

namespace IntervalArithmetic

initialize registerTraceClass `Tactic.interval

/-- Maybe generalize to other interval types -/
structure IntervalCertificate where
  interval : Interval Dyadic
  intervalExpr : Expr
  proof : Expr
  deriving Inhabited

structure CertificateGenerator where
  fvarSet : FVarIdSet
  ivarSet : FVarIdSet
  certGen (fvarSet : Array FVarId) (ivarSet : Array FVarId) (hyps : Array IntervalCertificate) :
    MetaM IntervalCertificate
  deriving Inhabited

abbrev CertificateGeneratorM := StateT CertificateGenerator MetaM

instance : MonadBacktrack (SavedState × CertificateGenerator) CertificateGeneratorM where
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

-- Add `intervalExt` extensions

def toCertificateGenerator (e : Expr) : MetaM CertificateGenerator := (go e).run' default where
  go (e : Expr) : CertificateGeneratorM CertificateGenerator := do
    let s ← saveState
    let intervalExts := intervalExt.getState (← getEnv)
    let exts ← intervalExts.tree.getMatch e
    let exts := exts.qsort (fun ext₁ ext₂ ↦ ext₁.priority < ext₂.priority)
    for ext in exts do
      if ! intervalExts.erased.contains ext.name then
        try
          ext.eval e
          trace[Tactic.interval] "{ext.name} applied to {e}"
          return (← get)
        catch err =>
          trace[Tactic.interval] "Failed to apply {ext.name} to {e} : {err.toMessageData}"
          restoreState s
    throwError "{e}: no interval extensions apply"

end IntervalArithmetic
