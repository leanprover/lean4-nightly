#exit

def PList (α : Type u) := List (α × α)

inductive Foo1 (α : Type u) where
  | mk (x : PList (Foo1 α))

set_option genSizeOf false

inductive Foo2 (α : Type u) where
  | mk (x : BoolFn (Foo2 α))
