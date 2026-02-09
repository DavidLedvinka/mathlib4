import Mathlib

/- FunProp File Notes -/

/- # Mathlib.Tactic.Funprop.Elab -/

namespace Mathlib
open Lean Meta Elab Tactic

namespace Meta.FunProp
open Lean.Parser.Tactic

/-
`declare_config_elab elabName TypeName` declares a function `elabName : Syntax → TacticM TypeName`
that elaborates a tactic configuration.

-/


/-- `fun_prop` config elaborator -/
declare_config_elab elabFunPropConfig' FunProp.Config

/- We get a function

`elabFunPropConfig : Syntax → TacticM FunProp.Config`

-/

/- This declares the syntax used to run the tactic -/
syntax (name := funPropTacStx')
  "fun_prop" optConfig (discharger)? (" [" withoutPosition(ident,*,?) "]")? : tactic

/-
`p,*,?` is shorthand for sepBy(p, ",", allowTrailingSep).
It parses 0 or more occurrences of p separated by ,,
possibly including a trailing ,, that is:
empty | p | p, | p,p | p,p, | p,p,p | ....

It produces a nullNode containing a SepArray with the interleaved parser results.
It has arity 1, and auto-groups its component parser if needed.
-/

-- `withReducible x` executes `x` with the reducible transparencey setting. In this setting
--  only definitions tagged as `[reducible]` are unfolded.

-- `forAllTelescope` given `type` of the form `forall xs, A`, execute `k xs A`.
-- This combinator will declare local declarations, create free variables for them,
-- execute `k` with updated local context, and make sure the cache is restored after
-- executing `k`.

-- `forallTelescopeReducing` is similar to `forallTelescope` but given `type` of the form
-- `for all xs, A` it reduces `A` and continues building the telescope if it is a `forall`.

structure FunPropDecl' where
  /-- function transformation name -/
  funPropName : Name
  /-- path for discrimination tree -/
  path : Array DiscrTree.Key
  /-- argument index of a function this function property talks about.
  For example this would be 4 for `@Continuous α β _ _ f` -/
  funArgId : Nat
  deriving Inhabited, BEq

/-- Discrimination tree for function properties -/
structure FunPropDecls' where
  decls : DiscrTree FunPropDecl' := {}
  deriving Inhabited

/-- Extension storing function properties tracked and used by the `fun_prop` attribute and
tactic, including, for example, `Continuous`, `Measurable`, `Differentiable`, etc. -/
initialize funPropDeclsExt' : FunPropDeclsExt ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun d e =>
      {d with decls := d.decls.insertKeyValue e.path e}
  }

/-- Result fo `funProp`, it is a proof fo function property `P f` -/
structure Result' where
  proof : Expr

/- Is `e` a function property statement? If yes return the function property declaration
and the function it talks about. -/
def getFunProp?' (e : Expr) : MetaM (Option (FunPropDecl × Expr)) := do
  let ext := funPropDeclsExt.getState (← getEnv) -- get the declaration
  let decls ← ext.decls.getMatch e (← read) -- tries to find all matches using discrimination tree
  if h : decls.size = 0 then
    return none
  else
    if decls.size > 1 then
      throwError "fun_prop bug: expression {← ppExpr e} matches multiple function properties\n\
        {decls.map (fun d => d.funPropName)}"
    let decl := decls[0]
    unless decl.funArgId < e.getAppNumArgs do return none
    let f := e.getArg! decl.funArgId
    return (decl, f)

private def emptyDischarge : Expr → MetaM (Option Expr) :=
  fun e =>
    withTraceNode `Meta.Tactic.fun_prop
      (fun r => do pure s!"{ExceptToEmoji.toEmoji r} discharging: {← ppExpr e}") do
        pure none

@[tactic funPropTacStx]
def funPropTac' : Tactic
  | `(tactic| fun_prop $cfg:optConfig $[$d]? $[[$names,*]]?) => do
    -- We are in the TacticM monad
    let goal ← getMainGoal -- get the goal (goal : MVarId)
    goal.withContext do
      let goalType ← goal.getType -- get the type of the goal
      -- this part of the code checks if its actually a fun_prop goal!
      withReducible <| forallTelescopeReducing (← whnfR goalType) fun _ type => do
        unless (← getFunProp? type).isSome do
          let hint :=
            if let some n := type.getAppFn.constName?
            then s!" Maybe you forgot marking `{n}` with `@[fun_prop]`."
            else ""
          throwError "{← ppExpr type} is not a `fun_prop` goal!{hint}"
      -- turn the config syntax into actual configuration (where is this actually "done")
      let cfg ← elabFunPropConfig cfg
      -- set the discharger
      let disch ← show MetaM (Expr → MetaM (Option Expr)) from do
        match d with
        | none => pure emptyDischarge
        | some d =>
          match d with
          -- **TODO** come back to `tacticToDischarge` to understand how it works!
          | `(discharger| (discharger:=$tac)) => pure <| tacticToDischarge (← `(tactic| ($tac)))
          | _ => pure emptyDischarge
      -- unfold names, not used very much...
      let namesToUnfold : Array Name :=
        match names with
        | none => #[]
        | some ns => ns.getElems.map (fun n => n.getId)
      -- by default fun_prop unfolds
      -- #[`id, `Function.comp, `Function.const, `Function.HasUncurry.uncurry, `Function.uncurry]
      let namesToUnfold := namesToUnfold ++ defaultNamesToUnfold
      -- Set up context
      let ctx : Context :=
        { config := cfg
          disch := disch
          constToUnfold := .ofArray namesToUnfold _}
      let env ← getEnv -- whats the point of this?
      -- set morphism and transition theorems?
      -- **TODO** Understand the below code which cannot be written for now...
      -- let s := {
      --   morTheorems        := morTheoremsExt.getState env
      --   transitionTheorems := transitionTheoremsExt.getState env }
      -- `funProp (e : Expr) : FunPropM (Option Result)` is the main function!
      -- let (r?, s) ← funProp goalType ctx |>.run s
      -- (the `ctx |>.run s` part probably somehow uses "FunPropM")
      let r? : Option Result ← sorry
      let s : State ← sorry -- used to record trace I think?
      if let some r := r? then
        goal.assign r.proof -- we assign the proof if sucess!
      else
        let mut msg := s!"`fun_prop` was unable to prove `{← Meta.ppExpr goalType}\n\n"
        msg := msg ++ "Issues:"
        msg := s.msgLog.foldl (init := msg) (fun msg m => msg ++ "\n " ++ m)
        throwError msg
  | _ => throwUnsupportedSyntax

/- **TODO**: Understand `funPropM` and `Result` -/

/-  `Elab` also contains a command that prints all function properties attached to a function. -/

/- **NEXT"** `funProp` (THE MEAT!) -/
