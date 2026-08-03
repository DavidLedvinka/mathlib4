module

public meta import Lean.Elab.Command

@[expose] public section

open Lean Elab Command

/--
Elaborate a command, wait for all asynchronous kernel checking it scheduled, and report the
combined elapsed time. Unlike `#time`, this includes kernel checking of the resulting declaration.
-/
syntax (name := timeWithKernelCmd) "#time_with_kernel " command : command

@[command_elab timeWithKernelCmd]
meta def elabTimeWithKernel : CommandElab
  | `(#time_with_kernel%$tk $cmd:command) => do
      let start ← IO.monoMsNow
      withScope (fun scope => { scope with opts := Elab.async.set scope.opts false }) do
        elabCommand cmd
      let env ← getEnv
      let _ ← pure env.checked.get
      logInfoAt tk m!"time including kernel checking: {(← IO.monoMsNow) - start}ms"
  | _ => throwUnsupportedSyntax
