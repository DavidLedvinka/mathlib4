# Overview of the inclusion tactic:

## Overview

The primary function of the inclusion tactic is as follows: Given an expression `e` (for example the type of a goal), compute an inclusion expression for `e`:

(In `Inclusion/Core/Types`)
```
structure ExprInclusion where
  inclusion : Expr
  proof : Expr
```

where `inclusion` is some expression that is built up of some kernel computation friendly expressions in some kernel computation friendly type, and `proof` is a proof of `e ∈ inclusion`.

Since `inclusion` itself is meant to live in some kernel computation friendly type, we need a way to interpret `inclusion` as a set in the type of `e`. That is the idea behind the following class :

(In `Inclusion/Core/ToSet`)
```
class ToSet (Iα : Type*) (α : outParam Type*) where
  toSet : Iα → Set α
```

Examples can be things like "intervals with dyadic endpoints" to sets of `ℝ`, "vectors of intervals of dyadic endpoints" to sets of `ℝⁿ`, "balls with a dyadic complex center and dyadic radius" to sets of `ℂ` etc...

The most important example however is `IntervalBool` to `Prop`:

```
def IntervalBool.toPropSet : IntervalBool → Set Prop
  | true => {True}
  | false => {False}
  | undetermined => {True, False}

instance : ToSet IntervalBool Prop := ⟨IntervalBool.toPropSet⟩
```

Using this, the tactic can generate an inclusion expression for a goal like `x ^ 2 + 1 < 5`, and then the proof of the goal is `proof` that `(x ^2 + 1 < 5) ∈ inclusion` along with a proof by reflection that `inclusion = IntervalBool.true`.

## Constructing `ExprInclusion`s

`ExprInclusion`s are constructed in two phases which take place inside two different monads. The first phase takes place in the `InclusionM` monad and is to construct an inclusion body:

(In `Inclusion/Core/Types`)
```
structure ExprInclusionBody where
  inclusionBody : Expr
  proofBody : Expr
```

which is the same as `ExprInclusion` except that `inclusionBody` is allowed to have "free `IVar`s (inclusion variables)" (see the structure `IVar` in `inclusion/Core/Types`) which represent "atomic" variables whose initial value will be determined by hypotheses in the local context (in the next phase). As an example, if we are applying the `inclusionBody` tactic to the goal `(x : ℝ) + 1 ≤ 5` then (depending on which extensions we have enabled) we might have that `x` is made into an `IVar`, which contains the expression of a placeholder variable `I` (which could be of type `Interval Dyadic` for example) and a placeholder hypothesis `x ∈ I`. For technical reasons these variables are synthetic opaque metavariables rather than free variables.

This phase uses inclusion extensions:

(In `Inclusion/Core/Extensions`)
```
structure InclusionExt where
  declName : Name := by exact decl_name%
  userName : Name := by exact decl_name%
  derive (e : Expr) : InclusionM ExprInclusionBody
  priority : Nat := eval_prio default
```

which belong to families (for example `interval_dyadic_real` containing extensions involving computations as intervals of dyadics as inclusions for operations on the reals)  and are registered under discrimination tree keys which determine which expressions they match on (and thus can possibly apply to).

The main driver of this phase is the function `mkExprInclusionBody` (in`Inclusion/Core/Inclusion`) which collects all the extensions (from enabled families) that match the current expression `e`, sort them in order of priority, and then try applying their `derive` to `e` until one succeeds in producing an `ExprInclusionBody`. The expectation is that if `derive e` succeeds it should produce a valid `ExprInclusionBody` for `e` and the metadata in the InclusionM monad should be up to date. Many derives will recursively call `mkExprInclusionBody`, for example you would expect that the extension which matches `e := e1 ≤ e2` will call `mkExprInclusionBody` on `e1` and `e2` and then combine the results to produce the `ExprInclusionBody` for `e`.

The second phase (taking place in the `HypothesisM` monad) is to convert hypotheses in the local
context into usable "inclusion hypotheses" for the expressions represented by `IVar`s. Each
`IVar` has a main inclusion representation, used in the body, and a hypothesis representation in
which these hypotheses are accumulated. A `HypothesisAccumulator` supplies an initial universal
constraint, a way to combine constraints, a conversion from the main representation, and a partial
conversion of the accumulated result back to the main representation. This permits, for example,
two one-sided interval constraints to be accumulated as a possibly unbounded interval and then
converted to a bounded ball once both endpoints are known. The resulting main inclusion and its
membership proof are substituted for the synthetic opaque placeholders in the body. When this is
done for every `IVar`, it produces an `ExprInclusion`.

Alternatively an `IVar` can contain a `Cover` which describes how to compute an inclusion function
separately on a cover of its input and then combine the resulting output inclusions using a
`Coarsen` instance. This is used to minimize the so-called "dependency" effect in interval
arithmetic. For example, ordinary interval arithmetic cannot prove `x ≤ x + 1` from
`x ∈ [0,2]`, since the two sides evaluate to `[0,2]` and `[1,3]`; splitting `[0,2]` into
`[0,1] ∪ [1,2]` makes the inclusion succeed on each piece.

This phase uses hypothesis extensions:

(In `Inclusion/Core/Extensions`)
```
structure HypothesisExt where
  declName : Name := by exact decl_name%
  userName : Name := by exact decl_name%
  derive (h : Expr) : HypothesisM Unit
```

where `derive h` generates inclusion hypotheses from `h` and puts them into the state of
HypothesisM. The main driver for this phase is `collectHyps` (in `Inclusion/Core/Inclusion`)
which loops over all local declarations `h`, finds all hypothesis extensions matching the type of
`h`, and then tries each of their `derive` functions. The changes made by a failed extension are
rolled back, while every successful extension is allowed to add one or more inclusion hypotheses.

## Params

Some inclusion computations depend on values which should be chosen by the user of the tactic.
Examples include the precision used to enclose a rational number by dyadics and the number of times
an interval should be split. These values are represented by registered inclusion parameters:

(In `Inclusion/Core/Extensions`)
```
structure InclusionParamDecl where
  name : Name
  type : Expr
  defaultValue? : Option Expr := none
```

Despite the examples above, an inclusion parameter is not restricted to being a natural number:
its `type` can be any closed type expression. A parameter is registered by tagging a meta
declaration with `inclusionParam`. For example:

```
@[inclusionParam]
def precParam : InclusionParamDecl where
  name := `prec
  type := q(ℕ)
```

The user can then supply a value with syntax such as

```
inclusion [core, interval_dyadic_real, prec := 100]
```

The elaborator looks up `prec`, elaborates `100` with the registered type, and stores the resulting
expression in `InclusionM.Context.paramSettings`. `InclusionM.getParam` and
`HypothesisM.getParam` return the user-supplied value, falling back to `defaultValue?` when one was
registered; the corresponding `getParam?` functions return `none` if neither is available. The
value is inserted directly while the inclusion body or inclusion hypotheses are being constructed,
so parameters do not become additional arguments of the final `ExprInclusion`.

The theorem-based extension API also recognizes parameters automatically. If a theorem argument's
user name and type agree with a registered parameter, the generated extension fills that argument
using the corresponding value. For example, the argument named `prec` in

```
theorem ratCast_mem (q : ℚ) (prec : ℕ) :
    (q : ℝ) ∈ ratInterval q prec := ...
```

is supplied from the registered `prec` parameter. A handwritten extension can instead call
`InclusionM.getParam`, `InclusionM.getParam?`, or their `HypothesisM` counterparts explicitly.


## Writing Extensions

Inclusion and hypothesis extensions are grouped into named `InclusionFamily`s. A family contains
one discrimination tree for each kind of extension and is initialized with:

```
meta initialize myFamily : InclusionFamily ←
  registerInclusionFamily `my_family
```

The file which initializes the family must be imported before declarations are registered in it.
Users explicitly enable the families needed by a tactic invocation; enabling a family makes both
its inclusion and hypothesis extensions available.

For most ordinary operations, an extension can be generated from a theorem without writing any
metaprogramming. An inclusion theorem has a conclusion of the form `e ∈ I` and inclusion premises
for the subexpressions which should be processed recursively. For example:

```
@[inclusionOp my_family]
theorem add_mem {x y : α} {I J : Iα}
    (hx : x ∈ I) (hy : y ∈ J) : x + y ∈ add I J := ...
```

The `inclusionOp` attribute analyzes the theorem, constructs a discrimination-tree key from
`x + y`, and generates an `InclusionExt`. When that extension is applied, it calls
`mkExprInclusionBody` on `x` and `y`, substitutes the resulting inclusion bodies and proofs for
`I`, `J`, `hx`, and `hy`, supplies any registered parameters and instance-implicit arguments, and
returns the instantiated conclusion and theorem application as an `ExprInclusionBody`.

Similarly, a hypothesis theorem describes how one source hypothesis can produce an inclusion
hypothesis. It must have exactly one explicit proposition premise which is not itself an inclusion;
this is the source hypothesis used as the discrimination-tree pattern. Other inclusion premises
are constructed recursively, but with the creation of new `IVar`s disabled. For example:

```
@[hypothesisOp my_family]
theorem upper_mem_of_le {x y : α} {I : Iα}
    (hxy : x ≤ y) (hy : y ∈ I) : x ∈ upper I := ...
```

The generated `HypothesisExt` matches hypotheses of the form `x ≤ y`, constructs a closed
inclusion for `y`, instantiates the theorem, checks that `x` is a registered inclusion variable,
and records the resulting inclusion body for `x`.

More complicated behavior can be implemented directly using the lower-level attributes:

```
@[inclusionExt my_family | _ + _]
def evalAdd : InclusionExt where
  derive e := ...

@[hypothesisExt my_family | _ ≤ _]
def evalLeHyp : HypothesisExt where
  derive h := ...
```

The expressions following `|` determine the discrimination-tree keys. A handwritten inclusion
extension can recursively call `mkExprInclusionBody`, create inclusion variables with `mkIVar` or
`mkNDIVarExt`, and access parameters through `InclusionM`. A handwritten hypothesis extension can
find registered variables with `findIVar?`, construct closed recursive inputs with
`mkHypExprInclusionBody`, and record results with `addInclusionHyp`. An extension which does not
apply should fail; the driver restores the saved metaprogram and monad state before trying the next
matching extension.

Finally, a family must supply the structures required by the representations it uses. Every
inclusion representation needs a `ToSet` instance, and every `IVar` needs a
`HypothesisAccumulator`. `HypothesisAccumulator.self` derives the usual same-representation
accumulator from `Univ` and `Refine` instances. If the family attaches a `Cover` to an `IVar`, the
possible output representations also need suitable `Coarsen` instances. The theorem-based API
guarantees the correctness of the generated bodies from the tagged theorem; a handwritten
extension is responsible for returning a body whose proof really has the form
`e ∈ inclusionBody` and for updating the monad state consistently.
