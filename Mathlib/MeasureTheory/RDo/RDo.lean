module

public import Mathlib.MeasureTheory.RDo.MeasurableSpaceMonad
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Distributions.Bernoulli
public meta import Lean.Meta.ProdN

set_option linter.style.header false

open Lean Lean.Parser Lean.Parser.Term Lean.Meta Lean.Elab Lean.Elab.Do Lean.Elab.Term Std

open MeasureTheory ProbabilityTheory Measure MeasurableSpacePure MeasurableSpaceBind

public meta section

def randOps : DoOps := { DoOps.default with
  mkPureApp α e := do
    let ⟨m, u, v, _, _⟩ := (← read).monadInfo
    let α ← Term.ensureHasType (mkSort (mkLevelSucc u)) α
    let e ← Term.ensureHasType α e
    let instPure ← mkInstMVar (.app (mkConst ``MeasurableSpacePure [u,v]) m)
    let instPure ← instantiateMVars instPure
    let σ ← mkInstMVar (.app (mkConst ``MeasurableSpace [u]) α)
    let σ ← instantiateMVars σ
    return mkAppN (mkConst ``mPure [u, v]) #[m, instPure, α, σ, e]
  mkBindApp α β e k := do
    let ⟨m, u, v, _, _⟩ := (← read).monadInfo
    let α ← Term.ensureHasType (mkSort (mkLevelSucc u)) α
    let σα ← mkInstMVar (.app (mkConst ``MeasurableSpace [u]) α)
    let σβ ← mkInstMVar (.app (mkConst ``MeasurableSpace [u]) β)
    let mα := mkApp2 m α σα
    let mβ := mkApp2 m β σβ
    let e ← Term.ensureHasType mα e
    let k ← Term.ensureHasType (← mkArrow α mβ) k
    let σα ← instantiateMVars σα
    let σβ ← instantiateMVars σβ
    let instBind ← mkInstMVar (.app (mkConst ``MeasurableSpaceBind [u, v]) m)
    let instBind ← instantiateMVars instBind
    return mkAppN (mkConst ``mBind [u, v]) #[m, instBind, α, β, σα, σβ, e, k]
  isPureApp? e :=
    if e.isAppOfArity ``mPure 5 then some (e.getArg! 4) else none
  splitMonadApp? type := do
    let type := type.consumeMData
    let args := type.getAppArgs
    unless args.size == 2 do return none
    let resultType := args[0]!
    let u ← getDecLevel resultType
    let v ← getDecLevel type
    return some ({ m := type.getAppFn, u := u.normalize, v := v.normalize }, resultType)
  mkMonadApp α := do
    let ⟨m, u, _, _, _⟩ := (← read).monadInfo
    let σ ← mkInstMVar (mkApp (mkConst ``MeasurableSpace [u]) α)
    return mkApp2 m α σ
  }

section LoopElab

@[doElem_elab Lean.Parser.Term.doFor] def elabDoFor : DoElab := fun stx dec => do
  let `(doFor| for%$tk $[$h? : ]? $x:ident in $xs do $body) := stx | throwUnsupportedSyntax
  let dec ← dec.ensureUnitAt tk
  checkMutVarsForShadowing #[x]
  let uα ← mkFreshLevelMVar
  let uρ ← mkFreshLevelMVar
  let α ← mkFreshExprMVar (mkSort (uα.succ)) (userName := `α)
  let ρ ← mkFreshExprMVar (mkSort (uρ.succ)) (userName := `ρ)
  let xs ← Term.elabTermEnsuringType xs ρ
  let mi := (← read).monadInfo
  let mutVars := (← read).mutVars

  let info ← inferControlInfoSeq body
  let oldReturnCont ← getReturnCont
  let returnVarName ← mkFreshUserName `__r
  let loopMutVars := mutVars.filter fun x => info.reassigns.contains x.getId
  let loopMutVarNames :=
    if info.returnsEarly then
      returnVarName :: (loopMutVars.map (·.getId)).toList
    else
      (loopMutVars.map (·.getId)).toList
  let useLoopMutVars (e : Option Expr) : TermElabM (Array Expr) := do
    let mut defs := #[]
    unless e.isNone || info.returnsEarly do
      throwError "Early returning {e} but the info said there is no early return"
    if info.returnsEarly then
      let returnVar ←
        match e with
        | none => mkNone oldReturnCont.resultType
        | some e => mkSome oldReturnCont.resultType e
      defs := defs.push returnVar
    for x in loopMutVars do
      let defn ← getLocalDeclFromUserName x.getId
      Term.addTermInfo' x defn.toExpr
      let u ← getDecLevel defn.type
      discard <| isLevelDefEq u mi.u
      defs := defs.push defn.toExpr
    if info.returnsEarly && loopMutVars.isEmpty then
      defs := defs.push (mkConst ``Unit.unit)
    return defs

  let (preS, σ) ← mkProdMkN (← useLoopMutVars none) mi.u
  let mσ ← Term.mkInstMVar <| mkApp (mkConst ``MeasurableSpace [mi.u]) σ
  let (app, p?) ← match h? with
    | none =>
      let instForIn ← Term.mkInstMVar <|
          mkApp3 (mkConst ``MeasurableSpaceForIn [uρ, uα, mi.u, mi.v]) mi.m ρ α
      let app := Lean.mkConst ``MeasurableSpaceForIn.forIn [uρ, uα, mi.u, mi.v]
      let app := mkApp8 app mi.m ρ α instForIn σ mσ xs preS
      pure (app, none)
    | some _ =>
      let d ← mkFreshExprMVar (mkApp2 (mkConst ``Membership [uα, uρ]) α ρ) (userName := `d)
      let instForIn ← Term.mkInstMVar <|
          mkApp4 (mkConst ``MeasurableSpaceForIn' [uρ, uα, mi.u, mi.v]) mi.m ρ α d
      let app := Lean.mkConst ``MeasurableSpaceForIn'.forIn' [uρ, uα, mi.u, mi.v]
      let app := mkApp9 app mi.m ρ α d instForIn σ mσ xs preS
      pure (app, some d)
  let s ← mkFreshUserName `__s
  let xh : Array (Name × (Array Expr → DoElabM Expr)) := match h?, p? with
    | some h, some d =>
      #[(x.getId, fun _ => pure α),
        (h.getId, fun x => pure (mkApp5 (mkConst ``Membership.mem [uα, uρ]) α ρ d xs x[0]!))]
    | _, _ =>
      #[(x.getId, fun _ => pure α)]

  let body ←
    withLocalDeclsD xh fun xh => do
    Term.addLocalVarInfo x xh[0]!
    if let some h := h? then
      Term.addLocalVarInfo h xh[1]!
    withLocalDecl s .default σ (kind := .implDetail) fun loopS => do
    mkLambdaFVars (xh.push loopS) <| ← do
    bindMutVarsFromTuple loopMutVarNames loopS.fvarId! do
    let newDoBlockResultType := mkApp (mkConst ``ForInStep [mi.u]) σ
    withDoBlockResultType newDoBlockResultType do
    let continueCont := do
      let (tuple, _tupleTy) ← mkProdMkN (← useLoopMutVars none) mi.u
      let yield := mkApp2 (mkConst ``ForInStep.yield [mi.u]) σ tuple
      mkPureApp newDoBlockResultType yield
    let breakCont := do
      let (tuple, _tupleTy) ← mkProdMkN (← useLoopMutVars none) mi.u
      let done := mkApp2 (mkConst ``ForInStep.done [mi.u]) σ tuple
      mkPureApp newDoBlockResultType done
    let returnCont := { oldReturnCont with k := fun e => do
        let (tuple, _tupleTy) ← mkProdMkN (← useLoopMutVars (some e)) mi.u
        let done := mkApp2 (mkConst ``ForInStep.done [mi.u]) σ tuple
        mkPureApp newDoBlockResultType done
      }
    enterLoopBody breakCont continueCont returnCont do
    -- Elaborate the loop body, which must have result type `PUnit`, just like the whole `for` loop.
    elabDoSeq body { dec with k := continueCont, kind := .duplicable }

  let forIn := mkApp app body

  let γ := (← read).doBlockResultType
  let rest ←
    withLocalDeclD s σ fun postS => do mkLambdaFVars #[postS] <| ← do
      bindMutVarsFromTuple loopMutVarNames postS.fvarId! do
        if info.returnsEarly then
          let ret ← getFVarFromUserName returnVarName
          let ret ← if loopMutVars.isEmpty then mkAppM ``Prod.fst #[ret] else pure ret
          let motive := mkLambda `_ .default (← inferType ret) (← mkMonadApp γ)
          let app := mkApp3 (mkConst ``Break.runK.match_1 [mi.u, mi.v.succ])
            oldReturnCont.resultType motive ret
          let none := mkSimpleThunk (← dec.continueWithUnit)
          let some ← withLocalDeclD (← mkFreshUserName `r) oldReturnCont.resultType fun r => do
            mkLambdaFVars #[r] (← oldReturnCont.k r)
          return mkApp2 app some none
        else
          dec.continueWithUnit

  mkBindApp σ γ forIn rest

end LoopElab

syntax (name := randKind) "rdo" doSeq : term

@[term_elab randKind] def elabRand : Term.TermElab := fun stx et? => do
  let `(rdo $doSeq) := stx | throwUnsupportedSyntax
  elabDoWith randOps doSeq et?

end

public section

section LoopInstances

universe u v

variable {α : Type u} [mα : MeasurableSpace α] {m : (α : Type u) → [MeasurableSpace α] → Type v}

section Array

/-- Compiler implementation for `forIn` -/
@[inline] unsafe def Array.measurableSpaceForIn'Unsafe [MeasurableSpaceMonad m]
  {β : Type u} [mβ : MeasurableSpace β]
  (as : Array α) (b : β) (f : (a : α) → a ∈ as → β → m (ForInStep β)) : m β :=
  let sz := as.usize
  let rec @[specialize] loop (i : USize) (b : β) : m β := rdo
    if i < sz then
      let a := as.uget i lcProof
      match (← f a lcProof b) with
      | ForInStep.done  b => mPure b
      | ForInStep.yield b => loop (i+1) b
    else
      mPure b
  loop 0 b

/-- Reference implementation for `forIn'` -/
@[implemented_by Array.measurableSpaceForIn'Unsafe]
protected def Array.measurableSpaceForIn' [MeasurableSpaceMonad m]
  {β : Type u} [mβ : MeasurableSpace β]
  (as : Array α) (b : β) (f : (a : α) → a ∈ as → β → m (ForInStep β)) : m β :=
  let rec loop (i : Nat) (h : i ≤ as.size) (b : β) : m β := rdo
    match i, h with
    | 0,   _ => mPure b
    | i+1, h =>
      have h' : i < as.size            := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) h
      have : as.size - 1 < as.size     := Nat.sub_lt (Nat.zero_lt_of_lt h') (by decide)
      have : as.size - 1 - i < as.size := Nat.lt_of_le_of_lt (Nat.sub_le (as.size - 1) i) this
      match (← f as[as.size - 1 - i] (getElem_mem this) b) with
      | ForInStep.done b  => mPure b
      | ForInStep.yield b => loop i (Nat.le_of_lt h') b
  loop as.size (Nat.le_refl _) b

instance [MeasurableSpaceMonad m] : MeasurableSpaceForIn' m (Array α) α inferInstance where
  forIn' := Array.measurableSpaceForIn'

instance {n : ℕ} [MeasurableSpaceMonad m] :
    MeasurableSpaceForIn' m (Vector α n) α inferInstance where
  forIn' xs b f := Array.measurableSpaceForIn' xs.toArray b (fun a h b => f a (by simpa using h) b)

end Array

section List

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [Ring α]

@[inline]
protected def List.measurableSpaceForIn' [MeasurableSpaceMonad m]
    {β : Type u} [mβ : MeasurableSpace β] (as : @& List α) (init : β)
    (f : (a : α) → a ∈ as → β → m (ForInStep β)) : m β :=
  let rec @[specialize]
    loop : (as' : @& List α) → (b : β) → Exists (fun bs => bs ++ as' = as) → m β
      | [], b, _    => mPure b
      | a::as', b, h => rdo
        have : a ∈ as := by
          clear f
          have ⟨bs, h⟩ := h
          subst h
          exact mem_append_right _ (Mem.head ..)
        match (← f a this b) with
        | ForInStep.done b  => mPure b
        | ForInStep.yield b =>
          have : Exists (fun bs => bs ++ as' = as) :=
            have ⟨bs, h⟩ := h
            ⟨bs ++ [a], by rw [← h, append_cons (bs := as')]⟩
          loop as' b this
  loop as init ⟨[], rfl⟩

instance [MeasurableSpaceMonad m] : MeasurableSpaceForIn' m (List α) α inferInstance where
  forIn' := List.measurableSpaceForIn'

end List

section Iter

universe w z


end Iter

end LoopInstances

end
