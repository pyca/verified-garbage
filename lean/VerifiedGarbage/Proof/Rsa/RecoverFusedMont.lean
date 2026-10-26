module

public import VerifiedGarbage.Proof.Rsa.RecoverFused
import VerifiedGarbage.Proof.Rsa.RecoverMath
public import VerifiedGarbage.Spec.Rsa
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic

/-! Montgomery representation of the existing fused-recovery algorithm.

This reuses its result theorem, including invalid-key behavior. It proves
an algorithmic refinement, not the C prototype or a target ISA program.
The multiplication hypothesis is exactly the boundary an ISA proof must
supply from the existing Montgomery kernel. -/

@[expose] public section
namespace VG.Proof.Rsa.FusedMont

abbrev State := Fused.State

def encode (n R : Nat) (s : State) : State :=
  ⟨s.value * R % n, s.root.map (fun y => y * R % n), s.done⟩

/-- All tests use Montgomery encodings; multiplying by a public candidate
is ordinary multiplication modulo n even in Montgomery representation. -/
def step (mul : Nat → Nat → Nat) (n R b : Nat) (bit : Bool) (s : State) : State :=
  let x := mul s.value s.value
  if bit then
    let y := x * b % n
    ⟨y, none, decide (y = R % n ∨ y = n - R % n)⟩
  else
    ⟨x, if !s.done && decide (x = R % n) then some s.value else s.root,
      s.done || decide (x = R % n ∨ x = n - R % n)⟩

theorem scale (n R b x : Nat) : (x * R % n) * b % n = (x * b % n) * R % n := by
  rw [Nat.mod_mul_mod, Nat.mod_mul_mod]
  congr 1
  ac_rfl

theorem step_encode (mul : Nat → Nat → Nat) (n R b : Nat) (bit : Bool) (s : State)
    (hn : 1 < n) (coprime : Nat.Coprime R n) (bound : s.value < n)
    (multiply : ∀ a < n, ∀ b < n, mul (a * R % n) (b * R % n) = (a * b % n) * R % n) :
    step mul n R b bit (encode n R s) = encode n R (Fused.step n b bit s) := by
  have pos : 0 < n := by omega
  have sq := multiply s.value bound s.value bound
  have one (x : Nat) (hx : x < n) : x * R % n = R % n ↔ x = 1 :=
    eq_one_mont coprime hn hx rfl
  have neg (x : Nat) (hx : x < n) : x * R % n = n - R % n ↔ x = n - 1 :=
    eq_neg_mont coprime hn hx rfl
  cases bit
  · simp only [step, encode, Fused.step, Bool.false_eq_true, ↓reduceIte, sq]
    simp only [one _ (Nat.mod_lt _ pos), neg _ (Nat.mod_lt _ pos)]
    cases h : (!s.done && decide (s.value * s.value % n = 1)) <;> simp
  · simp only [step, encode, Fused.step, ↓reduceIte, sq, scale n R b (s.value * s.value % n), Fused.start]
    simp only [one _ (Nat.mod_lt _ pos), neg _ (Nat.mod_lt _ pos)]
    rfl

def bits (mul : Nat → Nat → Nat) (n R b : Nat) : Nat → Nat → State → State
  | 0, _, s => s
  | k + 1, e, s => bits mul n R b k e (step mul n R b (decide (e / 2 ^ k % 2 = 1)) s)

theorem bits_encode (mul : Nat → Nat → Nat) (n R b k e : Nat) (s : State)
    (hn : 1 < n) (coprime : Nat.Coprime R n) (bound : s.value < n)
    (multiply : ∀ a < n, ∀ b < n, mul (a * R % n) (b * R % n) = (a * b % n) * R % n) :
    bits mul n R b k e (encode n R s) = encode n R (Fused.bits n b k e s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [bits, step_encode mul n R b _ s hn coprime bound multiply, Fused.bits]
    exact ih _ (Fused.step_lt _ _ _ _ (by omega))

/-- The complete fixed-width Montgomery pass returns exactly the specified
root in Montgomery form. No assumption that n is a product of primes, or
that e came from a valid key, is used. -/
theorem result (mul : Nat → Nat → Nat) (n R b e c : Nat)
    (hn : 1 < n) (coprime : Nat.Coprime R n)
    (positive : 0 < e) (fit : e < 2 ^ c) (even : e % 2 = 0)
    (multiply : ∀ a < n, ∀ b < n, mul (a * R % n) (b * R % n) = (a * b % n) * R % n) :
    (bits mul n R b c e (encode n R (Fused.start n 1))).root =
      (Spec.Rsa.recoverStep n (Spec.Rsa.splitTwos e).1 (Spec.Rsa.splitTwos e).2 b).map
        (fun y => y * R % n) := by
  rw [bits_encode mul n R b c e _ hn coprime (by exact hn) multiply]
  change (Fused.bits n b c e (Fused.start n 1)).root.map _ = _
  rw [Fused.result n b e c hn positive fit even]

end VG.Proof.Rsa.FusedMont
