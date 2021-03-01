class Num (α : Type) where
  zero : α
  succ : α → α

protected def Num.ofNat [Num α] : Nat → α
  | 0   => Num.zero
  | n+1 => Num.succ (Num.ofNat n)

instance [Num α] : OfNat α n where
  ofNat := Num.ofNat n

theorem Num.ofNat_inj [Num α] {n m : Nat} : Num.ofNat (α := α) n = Num.ofNat m → n = m :=
  sorry

class OfNat' (α : Type u) where
  ofNat : Nat → α

instance [OfNat' α] : OfNat α n where
  ofNat := OfNat'.ofNat n

instance [(n : Nat) → OfNat α n] : OfNat' α where
  ofNat n := OfNat.ofNat n

def one [OfNat' α] : α :=
  1

def g (x : Int) : Int :=
  x + one

set_option pp.all true in
#print g

#eval g 2

#exit

open OfNat (ofNat)

structure NormNum (α : Type) where
  ofNatInst : (n : Nat) → OfNat α n
  addInst   : Add α
  mulInst   : Mul α
  addNorm   : (n m : Nat) → ofNat (α := α) n + ofNat m = ofNat (n+m : Nat)
  mulNorm   : (n m : Nat) → ofNat (α := α) n * ofNat m = ofNat (n*m : Nat)

def Nat.NormNum : NormNum Nat where
  ofNatInst := inferInstance
  addInst   := inferInstance
  mulInst   := inferInstance
  addNorm n m := rfl
  mulNorm n m := rfl

class OfNatAdd (α : Type u) extends Add α where
  ofNatInst : (n : Nat) → OfNat α n
  addNorm : (n m : Nat) → ofNat (α := α) n + ofNat m = ofNat (n+m : Nat)

structure SimpNum (α : Type) where
  ofNatInst : (n : Nat) → OfNat α n

protected theorem Nat.add_sub_add_right : (n k m : Nat) → (n + k) - (m + k) = n - m
  | n, 0,      m => by rw [Nat.addZero, Nat.addZero]
  | n, succ k, m => by
    rw [Nat.addSucc, Nat.addSucc, succSubSuccEqSub, Nat.add_sub_add_right]

protected theorem Nat.add_sub_add_left (k n m : Nat) : (k + n) - (k + m) = n - m := by
  rw [Nat.addComm k n, Nat.addComm k m, Nat.add_sub_add_right]

theorem Nat.add_sub_of_le : {n m : ℕ} → n ≤ m → n + (m - n) = m
  | 0,   m, h => by done
  | n+1, m, h => by
    show n.succ + pred (m - n) = m
    tracetate
    done

#exit

theorem Nat.le.dest : {n m : Nat} → n ≤ m → ∃ k, n + k = m
  | n, _ Nat.Lessless_than_or_equal.refl ._)  := ⟨0, rfl⟩
  | n ._ (@less_than_or_equal.step ._ m h) :=
    match le.dest h with
    | ⟨w, hw⟩ := ⟨succ w, hw ▸ add_succ n w⟩
    end

protected theorem Nat.sub_add_cancel {n m : Nat} (h : n ≥ m) : n - m + m = n := by
  rw [Nat.addComm, add_sub_of_le h]


def boundedMeasure (n : Nat) (i : Nat) := n - i

theorem boundedMeasureProp {n i : Nat} (h : i < n) : boundedMeasure n (i+1) < boundedMeasure n i :=
  have n - i ≠ 0 by
    intro h

    done
  Nat.predLt this
