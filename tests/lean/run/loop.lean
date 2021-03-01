theorem Nat.succAddPred : (n m : Nat) → (h : m > 0) → n.succ + m.pred = n + m
  | n, 0, h   => absurd h (Nat.ltIrrefl _)
  | n, m+1, h => by
    show n.succ + m = n + m.succ
    rw [Nat.succ_add, Nat.add_succ]

#exit

theorem Nat.subPos : {n m : Nat} → n < m → m - n > 0
  | 0,   m,   h => h
  | n+1, 0,   h => absurd h (Nat.notSuccLeZero _)
  | n+1, m+1, h => by
    show m.succ - (n + 1) > 0
    show pred (m.succ - n) > 0

    done


theorem Nat.add_sub_of_le : {n m : Nat} → n ≤ m → n + (m - n) = m
  | 0,   m, h => by rw [Nat.zeroAdd]; rfl
  | n+1, m, h => by
    show n.succ + pred (m - n) = m
    have m - n > 0 from _
    rw [Nat.succAddPred (h := this)]
    apply add_sub_of_le (Nat.leOfSuccLe h)
