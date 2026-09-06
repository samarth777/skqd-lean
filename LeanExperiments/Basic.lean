/-!
# Example theorems in Lean 4

These proofs use only Lean's core library (no Mathlib).
-/

/-- `n` is even if it is twice some natural number. -/
def NatEven (n : Nat) : Prop :=
  ∃ k, n = 2 * k

/-- Zero is even, since `0 = 2 * 0`. -/
theorem even_zero : NatEven 0 :=
  ⟨0, rfl⟩

/-- The sum of two even numbers is even. -/
theorem even_add_even {m n : Nat} (hm : NatEven m) (hn : NatEven n) : NatEven (m + n) := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hn
  refine ⟨a + b, ?_⟩
  rw [ha, hb, Nat.mul_add]

/-- `4` and `6` are even, so their sum `10` is even. -/
example : NatEven (4 + 6) :=
  even_add_even ⟨2, rfl⟩ ⟨3, rfl⟩

namespace AddComm

/-!
Commutativity of addition, proved by induction from the
definitions `n + 0 = n` and `n + succ m = succ (n + m)`.
-/

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    rw [Nat.add_succ, ih]

theorem succ_add (n m : Nat) : n.succ + m = (n + m).succ := by
  induction m with
  | zero =>
    rfl
  | succ m ih =>
    -- n.succ + m.succ = (n.succ + m).succ
    --                 = (n + m).succ.succ
    --                 = (n + m.succ).succ
    rw [Nat.add_succ, ih, Nat.add_succ]

/-- Addition of natural numbers is commutative: `n + m = m + n`. -/
theorem add_comm (n m : Nat) : n + m = m + n := by
  induction n with
  | zero =>
    rw [Nat.zero_add, Nat.add_zero]
  | succ n ih =>
    -- n.succ + m = (n + m).succ = (m + n).succ = m + n.succ
    rw [succ_add, ih, Nat.add_succ]

end AddComm

def hello := "Lean"
