mutual
  inductive AList (α β : Type u) : Nat → Type u
    | nil : AList α β 0
    | cons (a : α) {n : Nat} (t : BList α β n) : AList α β (n+1)

  inductive BList (α β : Type u) : Nat → Type u
    | cons (b : β) {n : Nat} (t : AList α β n) : BList α β (n+1)
end


#check @AList.cons.sizeOf_spec

mutual

inductive Expr : Type
  | app2 (f : String) (args : VecExpr 2)
  | app3 (f : String) (args : VecExpr 3)

inductive VecExpr : Nat → Type
  | nil : VecExpr 0
  | cons (a : Expr) {n : Nat} (t : VecExpr n) : VecExpr (n+1)

end

#print Expr.rec

#print Expr._sizeOf_1
#print Expr._sizeOf_2
