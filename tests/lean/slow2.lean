def n := 40000000

structure State where
  a : Array Nat := mkArray n 0
  b : Array Nat := mkArray n 0

partial def f1 (i : Nat) : StateT State Id Unit := do
  if i < n then
    modify fun s => { a := s.a.set! i i, b := s.b }
    f1 (i+1)

partial def f2 (i : Nat) : StateT State Id Unit := do
  if i < n then
    modify fun ⟨a, b⟩ => ⟨a.set! i i, b⟩
    f2 (i+1)

def main : IO Unit := do
  let (_, s) := f1 0 |>.run {}
  IO.println s.a[n/2]
  IO.println s.a.size
