import Lean

open Lean
open Lean.Meta

def tst : MetaM Unit := do
  let (t, m1)  ← withLocalDeclD `x (mkConst ``Nat) fun x => do
    let m1 ← mkFreshTypeMVar MetavarKind.syntheticOpaque
    return (← mkLambdaFVars #[x] m1, m1)
  let m2 := t.bindingBody!.appFn!
  trace[Meta.debug]! "m1: {m1}, m2: {m2}"
  -- assignExprMVar m1.mvarId! (mkApp m2 (mkNatLit 0))
  return ()

set_option trace.Meta.debug true
#eval tst
