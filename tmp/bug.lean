open Lean

inductive BoolExpr where
  | var (name : String)
  | val (b : Bool)

syntax "`[BExpr|" term "]" : term

macro_rules
 | `(`[BExpr| true])     => `(BoolExpr.val true)
 | `(`[BExpr| $x:ident]) => `(BoolExpr.var $(quote x.getId.toString))

#check `[BExpr| p]
-- BoolExpr.val true : BoolExpr
