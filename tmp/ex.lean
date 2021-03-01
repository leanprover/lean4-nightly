namespace tst

def or (a b : Bool) :=
  match a with
  | true  => true
  | false => b

#check or true false
#eval or true false

def or' : Bool → Bool → Bool
 | true, _  => true
 | false, b => b

#check @rfl

theorem or_true (b : Bool) : or true b = true :=
  rfl

theorem or_self : ∀ (b : Bool), or b b = b
  | true  => rfl
  | false => rfl

theorem or_self' : ∀ (b : Bool), or b b = b := by
  intro b; cases b <;> rfl

instance [Inhabited α] [Inhabited β] : Inhabited (α × β) where
  default := (arbitrary, arbitrary)



def fact (x : Nat) :=
  match x with
  | 0   => 1
  | n+1 => (n+1) * fact n

theorem fact_succ : fact (n+1) = (n+1) * fact n :=
  rfl

#eval fact 5
