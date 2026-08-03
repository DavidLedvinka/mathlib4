module

public meta import Mathlib.Tactic.Inclusion.Core.Inclusion
public import Mathlib.Tactic.Inclusion.Core.Splitting

set_option linter.style.header false

@[expose] public meta section

open Lean Meta Elab Tactic

namespace IntervalArithmetic

def mkIVarDataFromContext (e : Expr) (iVarType : IVarType) : MetaM IVarData := do
  for ldecl in ← getLCtx do
    let type ← instantiateMVars ldecl.type
    if let some (expr, set, toSetInst) := toSetHyp? type then
      if expr == e then
        if ← isDefEq (← inferType set) iVarType.setType then
          if ← isDefEq toSetInst iVarType.toSetInst then
            return ⟨iVarType, expr, set, ldecl.toExpr⟩
  throwError "No containment hypothesis using set type {iVarType.setType} found for {e}"

structure SplitIVarData where
  data : IVarData
  splitter : Expr

def mkSplitIVarData (data : IVarData) : MetaM SplitIVarData := do
  let splitterType ← mkAppOptM ``Splitter
    #[data.iVarType.setType, data.iVarType.exprType, data.iVarType.toSetInst]
  try
    return ⟨data, ← synthInstance splitterType⟩
  catch _ =>
    throwError "No splitter is registered for inclusion variables of type \
      {data.iVarType.exprType} represented by {data.iVarType.setType}"

partial def mkSplitInclusionValueAux (inclusion : Expr)
    (splitIVars : Array SplitIVarData) (depth : Expr) (i : Nat) (pieces : Array Expr) :
    MetaM Expr := do
  if h : i < splitIVars.size then
    let { data, splitter } := splitIVars[i]
    withLocalDeclD `splitPiece data.iVarType.setType fun piece => do
      let inner ← mkSplitInclusionValueAux inclusion splitIVars depth (i + 1)
        (pieces.push piece)
      let predicate ← mkLambdaFVars #[piece] inner
      mkAppOptM ``Splitter.check
        #[data.iVarType.setType, data.iVarType.exprType, data.iVarType.toSetInst, splitter,
          depth, data.setVar, predicate]
  else
    return mkAppN inclusion pieces

def mkSplitInclusionValue (fn : ExprInclusionFunction)
    (splitIVars : Array SplitIVarData) (depth : Expr) : MetaM Expr :=
  mkSplitInclusionValueAux fn.inclusion splitIVars depth 0 #[]

def mkInclusionProof (uncurried : UncurriedInclusion) (exprs sets hyps : Array Expr)
    (hcheck : Expr) : MetaM Expr := do
  let expr ← mkProdsExpr exprs
  let sets ← mkProdsExpr sets
  let hyp ← mkProdsHyp hyps
  let proof ← mkAppOptM ``true_of_isInclusionFunction
    #[uncurried.iVarType.setType, uncurried.iVarType.exprType,
      uncurried.iVarType.toSetInst, uncurried.expr, uncurried.inclusion,
      uncurried.proof, expr, sets, hyp]
  return mkApp proof hcheck

partial def mkSplitProofAux (fn : ExprInclusionFunction)
    (uncurried : UncurriedInclusion) (splitIVars : Array SplitIVarData) (depth : Expr) (i : Nat)
    (pieces pieceHyps : Array Expr) (hcheck : Expr) : MetaM Expr := do
  if h : i < splitIVars.size then
    let { data, splitter } := splitIVars[i]
    withLocalDeclD `splitPiece data.iVarType.setType fun piece => do
      let inner ← mkSplitInclusionValueAux fn.inclusion splitIVars depth (i + 1)
        (pieces.push piece)
      let predicate ← mkLambdaFVars #[piece] inner
      let pieceHypType ← mkToSetMem data.iVarType.exprType data.iVarType.setType
        data.exprVar piece data.iVarType.toSetInst
      withLocalDeclD `splitPieceHyp pieceHypType fun pieceHyp => do
        let nextCheck := mkApp predicate piece
        withLocalDeclD `splitCheck (← mkEq nextCheck (mkConst ``IntervalBool.true))
            fun nextCheckTrue => do
          let next ← mkSplitProofAux fn uncurried splitIVars depth (i + 1)
            (pieces.push piece) (pieceHyps.push pieceHyp) nextCheckTrue
          let qType ← inferType next
          let continuation ← mkLambdaFVars #[piece, pieceHyp, nextCheckTrue] next
          let elim ← mkAppM ``Splitter.splitElim
            #[splitter, predicate, depth, data.exprVar, data.setVar, data.hypVar]
          return mkApp3 elim qType hcheck continuation
  else
    mkInclusionProof uncurried fn.ivars pieces pieceHyps hcheck

def mkSplitProof (fn : ExprInclusionFunction) (splitIVars : Array SplitIVarData)
    (depth hcheck : Expr) : MetaM Expr := do
  let uncurried ← fn.uncurry
  mkSplitProofAux fn uncurried splitIVars depth 0 #[] #[] hcheck

def mkGoalInclusionData (g : MVarId) : MetaM (ExprInclusionFunction × Array IVarData) := do
  let target ← instantiateMVars (← g.getType)
  unless ← isProp target do
    throwError "The target is not a proposition"
  let fn ← toExprInclusionFunction target
  unless fn.ivars.size = fn.iVarTypes.size do
    throwError "Internal error: inclusion-variable expressions and types have different lengths"
  let ivars := fn.ivars.zip fn.iVarTypes
  return (fn, ← ivars.mapM fun (e, iVarType) => mkIVarDataFromContext e iVarType)

def mkInclusionTrueProof (inclusionValue : Expr) (split : Bool) : MetaM Expr := do
  let inclusionResult ← unsafe
    (evalExpr IntervalBool (mkConst ``IntervalBool) inclusionValue)
  match inclusionResult with
  | IntervalBool.true =>
      return mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``IntervalBool) inclusionValue
  | IntervalBool.false =>
      if split then
        throwError "The compiled split inclusion check returned false"
      else
        throwError "The compiled inclusion check returned false"
  | IntervalBool.undetermined =>
      if split then
        throwError "The compiled split inclusion check was undetermined"
      else
        throwError "The compiled inclusion check was undetermined"

def inclusionCore (g : MVarId) : MetaM Expr := do
  let (fn, iVarData) ← mkGoalInclusionData g
  let inclusionValue := mkAppN fn.inclusion (iVarData.map (·.setVar))
  let inclusionTrue ← mkInclusionTrueProof inclusionValue false
  let uncurried ← fn.uncurry
  mkInclusionProof uncurried fn.ivars (iVarData.map (·.setVar))
    (iVarData.map (·.hypVar)) inclusionTrue

def inclusionCoreSplit (g : MVarId) (depth : Nat) : MetaM Expr := do
  let (fn, iVarData) ← mkGoalInclusionData g
  let splitIVars ← iVarData.mapM mkSplitIVarData
  let depthExpr := mkNatLit depth
  let inclusionValue ← mkSplitInclusionValue fn splitIVars depthExpr
  let inclusionTrue ← mkInclusionTrueProof inclusionValue true
  mkSplitProof fn splitIVars depthExpr inclusionTrue

def inclusionTactic : TacticM Unit := withMainContext do
  let g ← getMainGoal
  g.assign (← inclusionCore g)
  replaceMainGoal []

elab "inclusion" : tactic => inclusionTactic

elab "inclusion" "[" "split" " := " depth:num "]" : tactic => withMainContext do
  let g ← getMainGoal
  g.assign (← inclusionCoreSplit g depth.getNat)
  replaceMainGoal []

end IntervalArithmetic
