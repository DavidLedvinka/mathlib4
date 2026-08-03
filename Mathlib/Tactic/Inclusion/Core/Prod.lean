module

public import Mathlib.Tactic.Inclusion.Core.Expr

set_option linter.style.header false

@[expose] public section

open Lean Meta

namespace IntervalArithmetic

structure IVarType where
  exprType : Expr
  setType : Expr
  toSetInst : Expr

structure IVarData where
  iVarType : IVarType
  exprVar : Expr
  setVar : Expr
  hypVar : Expr

structure UncurriedInclusion where
  iVarType : IVarType
  expr : Expr
  inclusion : Expr
  proof : Expr

def mkProdsIVarType (types : Array IVarType) : MetaM IVarType := do
  let result ← types.foldrM (init := none) fun type result => do
    let some prods := result | return some type
    let exprType ← mkAppM ``Prod #[type.exprType, prods.exprType]
    let setType ← mkAppM ``Prod #[type.setType, prods.setType]
    let toSetInst ← mkAppOptM ``instToSetProd
      #[type.setType, type.exprType, prods.setType, prods.exprType, type.toSetInst, prods.toSetInst]
    return some ⟨exprType, setType, toSetInst⟩
  return result.getD ⟨mkConst ``PUnit [1], mkConst ``PUnit [1], mkConst ``instToSetPUnit [0, 0]⟩

def getProdComponents (n : Nat) (e : Expr) : MetaM (Array Expr) := do
  if n = 0 then
    return #[]
  let mut components := Array.mkEmpty n
  let mut tail := e
  for _ in [:(n - 1)] do
    components := components.push (← mkAppM ``Prod.fst #[tail])
    tail ← mkAppM ``Prod.snd #[tail]
  return components.push tail

def getProdHyps (n : Nat) (h : Expr) : MetaM (Array Expr) := do
  if n = 0 then
    return #[]
  let mut hyps := Array.mkEmpty n
  let mut tail := h
  for _ in [:(n - 1)] do
    hyps := hyps.push (← mkAppM ``And.left #[tail])
    tail ← mkAppM ``And.right #[tail]
  return hyps.push tail

def uncurryInclusion
    (iVarTypes : Array IVarType) (expr inclusion proof : Expr) : MetaM UncurriedInclusion := do
  let prodType ← mkProdsIVarType iVarTypes
  withLocalDeclD `args prodType.exprType fun args => do
    let exprComponents ← getProdComponents iVarTypes.size args
    let expr ← mkLambdaFVars #[args] (mkAppN expr exprComponents)
    withLocalDeclD `sets prodType.setType fun sets => do
      let setComponents ← getProdComponents iVarTypes.size sets
      let inclusion ← mkLambdaFVars #[sets] (mkAppN inclusion setComponents)
      let hypType ← mkToSetMem prodType.exprType prodType.setType args sets prodType.toSetInst
      withLocalDeclD `h hypType fun h => do
        let hyps ← getProdHyps iVarTypes.size h
        let proof ← mkLambdaFVars #[args, sets, h]
          (mkAppN proof (exprComponents ++ setComponents ++ hyps))
        return ⟨prodType, expr, inclusion, proof⟩

end IntervalArithmetic
