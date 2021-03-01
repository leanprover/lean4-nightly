class A (α : Type u) where
  a : Unit

class B (α : Type u) where
  a : Unit

instance [B (Array α)] : A α  where
  a := ()

instance [A (Array α)] : B α where
  a := ()

#exit

def f : B Nat :=
  inferInstance
