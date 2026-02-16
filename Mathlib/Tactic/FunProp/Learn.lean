import Mathlib

/- FunProp File Notes -/

/- # Mathlib.Tactic.Funprop.Elab -/

namespace Mathlib
open Lean Meta Elab Tactic

namespace Meta.FunProp
open Lean.Parser.Tactic Qq

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

/- # Lean.Expr programs for working with bundled morphisms

Function applications in normal lean expressions look like `.app f x` but when we work with
bundled morphisms `f` it looks like `.app (.app coe f) x`. In mathlib `coe` is usually
`DFunLike.coe` but it can be any coercian that is registered with the `coe` attribute.

The main difference when working with expressions involving morphisms is that the notion
the head of the expression changes. For example in
```
  coe (f a) b
```
the head of the expression is considered to be `f` and not `coe` (why?).

-/

/- An abbreviation of `∀ x, p x`. It is used by `fun_prop` to represent Pi types as function
applications and should not occur in any place other than the implimentation of `fun_prop`-/
abbrev Forall' {α : Sort*} (p : α → Sort*) := ∀ x, p x

namespace Mor

/- Is `name` a corecian from some function space to functions? -/
def isCoeFunName' (name : Name) : CoreM Bool := do
  let some info ← getCoeFnInfo? name | return false
  return info.type == .coeFun

/- Is `e` a coercian from some function space to functions? -/
def isCoeFun' (e : Expr) : MetaM Bool := do
  let some (name, _) := e.getAppFn.const? | return false
  let some info ← getCoeFnInfo? name | return false
  return e.getAppNumArgs' + 1 == info.numArgs

/-- Morphism application -/
structure App' where
  /-- morphism coercian -/
  coe : Expr
  /-- bundled morphism -/
  fn : Expr
  /-- morphism argument -/
  arg : Expr

/-- Is `e` morphism application? -/
def isMorApp?' (e : Expr) : MetaM (Option App) := do
  let .app (.app coe f) x := e | return none
  if ← isCoeFun coe then
    return some { coe := coe, fn := f, arg := x }
  else
    return none

/-
Weak head normal head form of an expression involving morphism application.
Additionally, `pred` can specify when to unfold definitions.

For example calling this on `coe (f a) b` will put `f` in weak normal form instead
of `coe`.
-/

partial def whnfPred' (e : Expr) (pred : Expr → MetaM Bool) :
    MetaM Expr := do
  whnfEasyCases e fun e => do
    let e ← whnfCore e
    if let some ⟨coe,f,x⟩ ← isMorApp? e then
      let f ← whnfPred' f pred
      if (← getConfig).zeta then
        return (coe.app f).app x
      else
        return ← mapLetTelescope f fun _ f' => pure ((coe.app f').app x)
    if (← pred e) then
      match (← unfoldDefinition? e) with
      | some e => whnfPred e pred
      | none => return e
    else
      return e

def whnf' (e : Expr) : MetaM Expr :=
  whnfPred e (fun _ => return false)

/- Argument of morphism application that stores corresponding coercian if necessary -/
structure Arg' where
/-- argument of type `α` -/
expr : Expr
/-- coercian `F → α → β` -/
coe : Option Expr := none
deriving Inhabited

/-- Morphism application -/
def app' (f : Expr) (arg : Arg) : Expr :=
  match arg.coe with
  | none => f.app arg.expr
  | some coe => (coe.app f).app arg.expr

/- Given `e = f a₁ a₂ … aₙ`, returns `k f #[a₁, ..., aₙ]` where `f` can be bundled morphism. -/

partial def withApp' {α} (e : Expr) (k : Expr → Array Arg → MetaM α) : MetaM α :=
  go e #[]
where
  go : Expr → Array Arg → MetaM α
    | .mdata _ b, as => go b as -- skip data
    | .app (.app c f) x, as => do
      if ← isCoeFun c then
        go f (as.push {coe := c, expr := x})
      else
        go (.app c f) (as.push {expr := x})
    | .app (.proj n i f) x, as => do
      -- convert proj back to function application
      let env ← getEnv
      let info := getStructureInfo? env n |>.get!
      let projFn := getProjFnForField? env n (info.fieldNames[i]!) |>.get!
      let .app c f ← mkAppM projFn #[f] | panic! "bug in Mor.withApp"
      go (.app (.app c f) x) as
    | .app f a, as => go f (as.push {expr := a})
    | .forallE x t b bi, _ => do
      go (← mkAppM ``Forall #[.lam x t b bi]) #[]
    | f, as => k f as.reverse

/-
If the given expression is a sequence of morphism applications `f a₁ .. aₙ`, return `f`.
Otherwise return the input expression.
-/
def getAppFn' (e : Expr) : MetaM Expr :=
  match e with
  | .mdata _ b => getAppFn b
  | .app (.app c f) _ => do
    if ← isCoeFun c then
      getAppFn f
    else
      getAppFn (.app c f)
  | .app f _ =>
    getAppFn f
  | e => return e

/- Given `f a₁ ... aₙ`, returns `#[a₁, ..., aₙ]` where `f` can be bundled morphism. -/
def getAppArgs' (e : Expr) : MetaM (Array Arg) := withApp e fun _ xs => return xs

/-- `mkAppN f #[a₀, ..., aₙ]` ==> `f a₀ a₁ .. aₙ` where `f` can be bundled morphism. -/
def mkAppN'' (f : Expr) (xs : Array Arg) : Expr :=
  xs.foldl (init := f) (fun f x =>
    match x with
    | ⟨x, .none⟩ => (f.app x)
    | ⟨x, some coe⟩ => (coe.app f).app x)

/-- `mkAppN f #[a₀, ..., a]` ==> `f a₀ a₁ .. aₙ` where `f` can be a bundled morphism. -/
def mkAppN' (f : Expr) (xs : Array Arg) : Expr :=
  xs.foldl (init := f) (fun f x =>
    match x with
    | ⟨x, .none⟩ => (f.app x)
    | ⟨x, some coe⟩ => (coe.app f).app x)

end Mor

/- # Function Data -/

/- Structure storing parts of a function in funProp-normal form. -/
structure FunctionData' where
  /- local context where `mainVar` exists. -/
  lctx : LocalContext
  /- local instances -/
  insts : LocalInstances
  /- main function -/
  fn : Expr
  /- applied function arguments -/
  args : Array Mor.Arg
  /- main variable -/
  mainVar : Expr
  /- indices of `args` that contain `mainVars` -/
  mainArgs : Array Nat

/- Turn function data back to expression. -/
def FunctionData.toExpr' (f : FunctionData) : MetaM Expr := do
  withLCtx f.lctx f.insts do
    let body := Mor.mkAppN f.fn f.args
    mkLambdaFVars #[f.mainVar] body

/- Is `f` an indentity function? -/
def FunctionData.isIdentityFun' (f : FunctionData) : Bool :=
  (f.args.size = 0 && f.fn == f.mainVar)

/- Is `f` a constant function? -/
def FunctionData.isConstantFun' (f : FunctionData) : Bool :=
  ((f.mainArgs.size = 0) && !(f.fn.containsFVar f.mainVar.fvarId!))

/- Is head function of `f` a constant?

If the head of `f` is a projection return the name of the corresponding projection function. -/
def FunctionData.getFnConstName?' (f : FunctionData) : MetaM (Option Name) := do
  match f.fn with
  | .const n _ => return n
  | .proj typeName idx _ =>
    let some info := getStructureInfo? (← getEnv) typeName | return none
    let some projName := info.getProjFn? idx | return none
    return projName
  | _ => return none

/- Get `FunctionData` for `f`. Throws if `f` can't be put into funProp-normal form. -/
def getFunctionData' (f : Expr) : MetaM FunctionData := do
  lambdaTelescope f fun xs b => do
    let xId := xs[0]!.fvarId!
    Mor.withApp b fun fn args => do
      let mut fn := fn
      let mut args := args
      -- revert projection in fn
      if let .proj n i x := fn then
        let some info := getStructureInfo? (← getEnv) n | unreachable!
        let some projName := info.getProjFn? i | unreachable!
        let p ← mkAppM projName #[x]
        fn := p.getAppFn
        args := p.getAppArgs.map (fun a => {expr := a}) ++ args
      let mainArgs := args
        |>.mapIdx (fun i ⟨arg,_⟩ => if arg.containsFVar xId then some i else none)
        |>.filterMap id
      return {
        lctx := ← getLCtx
        insts := ← getLocalInstances
        fn := fn
        args := args
        mainVar := xs[0]!
        mainArgs := mainArgs
      }

/- Result of `getFunctionData?`. It returns function data if the function is the form
`fun x ↦ f y₁ ... yₙ`. Two other cases are `fun x ↦ let y := ...` or `fun x y ↦ ...`
-/
inductive MaybeFunctionData' where
  /-- Can't generate function data as function body has let binder. -/
  | letE (f : Expr)
  /-- Can't generate function data as function body has lambda binder. -/
  | lam (f : Expr)
  /-- Function data has been successfully generated. -/
  | data (fData : FunctionData)

/-- Turn `MaybeFunctionData` to the function -/
def MaybeFunctionData.get' (fData : MaybeFunctionData) : MetaM Expr :=
  match fData with
  | .letE f | .lam f => pure f
  | .data d => d.toExpr

/- Get `FunctionData` for `f`. -/
def getFunctionData?' (f : Expr)
    (unfoldPred : Name → Bool := fun _ => false) :
    MetaM MaybeFunctionData := do
  withConfig (fun cfg => { cfg with zeta := false, zetaDelta := false}) do
    let unfold := fun e : Expr => do
      if let some n := e.getAppFn'.constName? then
        pure ((unfoldPred n) || (← isReducible n))
      else
        pure false
    let .forallE xName xType _ _  ← instantiateMVars (← inferType f)
      | throwError m! "fun_prop bug: function expected, got `{f} : {← inferType f}, \
                       type ctor {(← inferType f).ctorName}"
    withLocalDeclD xName xType fun x => do
      let fx' := (← Mor.whnfPred (f.beta #[x]).eta unfold) |> headBetaThroughLet
      let f' ← mkLambdaFVars #[x] fx'
      match fx' with
      | .letE .. => return .letE f'
      | .lam .. => return .lam f'
      | _ => return .data (← getFunctionData f')

/- If head function is a let-fvar unfold it and return resulting function.
Return `none` otherwise. -/
def FunctionData.unfoldHeadFVar?' (fData : FunctionData) : MetaM (Option Expr) := do
  let .fvar id := fData.fn | return none
  let some val ← id.getValue? | return none
  let f ← withLCtx fData.lctx fData.insts do
    mkLambdaFVars #[fData.mainVar] (headBetaThroughLet (Mor.mkAppN val fData.args))
  return f

/- Type of morphism application. -/
inductive MorApplication' where
  /- Of the form `↑f` i.e. missing argument. -/
  | underApplied
  /- Of the form `↑f x` i.e. morphism and one argument is provided. -/
  | exact
  /- Of the form `↑f x y ...` i.e. additional applied arguments `y ...` -/
  | overApplied
  /- Not a morphism application. -/
  | none
  deriving Inhabited, BEq

/- Is function body of `f` a morphism application? What kind? -/
def FunctionData.isMorApplication' (f : FunctionData) : MetaM MorApplication := do
  if let some name := f.fn.constName? then
    if ← Mor.isCoeFunName name then
      let info ← getConstInfo name
      let arity := info.type.getNumHeadForalls
      match compare arity f.args.size with
      | .eq => return .exact
      | .lt => return .overApplied
      | .gt => return .underApplied
  match h : f.args.size with
  | 0 => return .none
  | n + 1 =>
    if f.args[n].coe.isSome then
      return .exact
    else if f.args.any (fun a => a.coe.isSome) then
      return .overApplied
    else
      return .none

/- Decomposes `fun x ↦ f y₁ ... yₙ` into `(fun g ↦ g yₙ) ∘ (fun x y ↦ f y₁ ... yₙ₋₁ y)`

returns none if:
  - `n=0`
  - `yₙ` contains `x`
  - `n=1` and `(fun x y ↦ f y)` is identity function i.e. `x=f` -/
def FunctionData.peeloffArgDecomposition' (fData : FunctionData) :
    MetaM (Option (Expr × Expr)) := do
  unless fData.args.size > 0 do return none
  withLCtx fData.lctx fData.insts do
    let n := fData.args.size
    let x := fData.mainVar
    let yₙ := fData.args[n-1]!

    if yₙ.expr.containsFVar x.fvarId! then
      return none

    if fData.args.size = 1 &&
        fData.mainVar == fData.fn then
      return none

    let gBody' := Mor.mkAppN fData.fn fData.args[:n-1]
    let gBody' := if let some coe := yₙ.coe then coe.app gBody' else gBody'
    let g' ← mkLambdaFVars #[x] gBody'
    let f' := Expr.lam `f (← inferType gBody') (.app (.bvar 0) (yₙ.expr)) default
    return (f', g')


/- Decompose function `f = (← fData.toExpr)` into composition of two functions.

Returns none if the decomposition would produce composition with identity function.
-/
def FunctionData.nontrivialDecomposition' (fData : FunctionData) :
    MetaM (Option (Expr × Expr)) := do

  let mut lctx := fData.lctx
  let insts := fData.insts

  let x := fData.mainVar
  let xId := x.fvarId!
  -- userName of the main variable
  let xName ← withLCtx lctx insts xId.getUserName

  let fn := fData.fn
  let mut args := fData.args

  if fn.containsFVar xId then
    return ← fData.peeloffArgDecomposition

  let mut yVals : Array Expr := #[]
  let mut yVars : Array Expr := #[]

  -- loop over ther arguments of `f` that contain `mainVars`
  for argId in fData.mainArgs do
    -- get the current `Mor.Arg`
    let yVal := args[argId]!
    let yVal' := yVal.expr
    -- Make a fresh free variable Id
    let yId ← withLCtx lctx insts mkFreshFVarId
    -- infer the type of the current argument
    let yType ← withLCtx lctx insts (inferType yVal')
    -- Problemo if it depends on the type!
    if yType.containsFVar fData.mainVar.fvarId! then
      return none
    -- Make the local context the of the new free variable
    lctx := lctx.mkLocalDecl yId (xName.appendAfter (toString argId)) yType
    -- make the new free variable
    let yVar := Expr.fvar yId
    -- push these onto the array (it seems we are basically abstracting "main var"?)
    yVars := yVars.push yVar
    yVals := yVals.push yVal'
    args := args.set! argId ⟨yVar, yVal.coe⟩

  --  g "computes" the argumets
  let g ← withLCtx lctx insts do
    mkLambdaFVars #[x] (← mkProdElem yVals)
  -- f "selects" the arguments and then applies the head function!
  let f ← withLCtx lctx insts do
    (mkLambdaFVars yVars (Mor.mkAppN fn args))
    >>=
    mkUncurryFun yVars.size

  -- check if is non-triviality
  let f' ← fData.toExpr
  if (← withReducibleAndInstances <| isDefEq f' f <||> isDefEq f' g) then
    return none
  return (f, g)

/- REVIEW DOCUMENTATION (NEXT UP!!!) -/
def FunctionData.decompositionOverArgs' (fData : FunctionData) (args : Array Nat) :
  MetaM (Option (Expr × Expr)) := do sorry

/- # Types? -/

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

/- Cache result if it does not have any subgoals -/
def cacheResult' (e : Expr) (r : Result) : FunPropM Result := do
  modify (fun s => { s with cache := s.cache.insert e { expr := q(True), proof? := r.proof}})
  return r

mutual
  /-- Main `funProp` function. Returns proof of `e`. -/
  partial def funProp' (e : Expr) : FunPropM (Option Result) := do
    let e ← instantiateMVars e
    withTraceNode `Meta.Tactic.fun_prop
      (fun r => do pure s!"[{ExceptToEmoji.toEmoji r}] {← ppExpr e}") do
    -- check cache for successful goals
    if let some {expr := _, proof? := some proof } := (← get).cache.find? e then
      trace[Meta.Tactic.fun_prop] "reusing previously found proof for {e}"
      return some { proof := proof}
    else if (← get).failureCache.contains e then
      trace[Meta.Tactic.fun_prop] "skipping proof search, proving {e} was tried already and failed"
      return none
    else
      match e with
      | .letE .. =>
        letTelescope e fun xs b => do
          let some r ← funProp b
            | return none
          cacheResult e {proof := ← mkLambdaFVars (generalizeNondepLet := false) xs r.proof }
      | .forallE .. =>
        forallTelescope e fun xs b => do
          let some r ← funProp b
            | return none
          cacheResult e {proof := ← mkLambdaFVars xs r.proof}
      | .mdata _ e' => funProp e'
      | _ =>
        if let some r ← main' e then
          cacheResult e r
        else
          cacheFailure e
          return none

  private partial def main' (e : Expr) : FunPropM (Option Result) := do
    let some (funPropDecl, f) ← getFunProp? e
      | return none
    increaseSteps
    -- if function starts with let binding move them to the top of `e` and try again
    if f.isLet then
      return ← funProp (← mapLetTelescope f fun _ b => pure <| e.setArg funPropDecl.funArgId b)
    match ← getFunctionData? f (← unfoldNamePred) with
      sorry
