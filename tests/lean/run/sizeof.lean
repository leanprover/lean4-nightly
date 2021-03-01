import Lean


inductive Vec (α : Type u) : Nat → Type u
  | nil  : Vec α 0
  | cons : α → {n : Nat} → Vec α n → Vec α (n+1)

#print Vec.nil.sizeOf_spec
#print Vec.cons.sizeOf_spec

inductive Expr where
  | app3 (args : Vec Expr 3)
  | app2 (args : Vec Expr 2)

#check Expr._sizeOf_2
#check @Expr.rec_1

-- set_option trace.Meta.sizeOf true

mutual

inductive TreePos (α : Type u) (β : Type u → Type v) (n : Nat) where
  | leaf (a : α)
  | node (children : List (List (TreeNeg α β n)))

inductive TreeNeg (α : Type u) (β : Type u → Type v) (n : Nat) where
  | leaf (a : β α)
  | node (children : List (List (TreePos α β n)))

end

#check @TreePos._sizeOf_inst

#print TreePos.node.sizeOf_spec
