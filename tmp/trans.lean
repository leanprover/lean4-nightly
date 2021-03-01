class Trans (r : α → β → Prop) (s : β → γ → Prop) (t : outParam (α → γ → Prop)) where
  trans : r a b → s b c → t a c

-- enforce indentation of calc steps so we know when to stop parsing them
syntax calcStep := colGe term " := " term
syntax "calc " withPosition(calcStep+) : term

macro_rules
  | `(calc $p:term := $h:term) => `(($h : $p))
  | `(calc $p:term := $h:term $rest:calcStep*) => `(Trans.trans ($h : $p) (calc $rest:calcStep*))

instance (r : α → γ → Prop) : Trans Eq r r where
  trans heq h := heq ▸ h

instance (r : α → β → Prop) : Trans r Eq r where
  trans h heq := heq ▸ h

instance : Trans (α := Nat) Less Less Less where
  trans := Nat.ltTrans

theorem ex₂ (h₁ : a < b + 0) (h₂ : b < c) : a < c :=
 calc
   a < b + 0 := h₁
   _ = b     := rfl
   _ < c     := h₂


-- h₁ h₂
