module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialStep
import VerifiedGarbage.Proof.Framework.Omega

/-! The remaining big-endian input, grouped by the same byte pairs as RSA's
radix-2^16 reducer. The final odd octet is a zero-padded leading digit. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm

def trialValue (m : Mem) (endPtr : BitVec 32) : Nat → Nat
  | 0 => 0
  | 1 => trialDigitNat m endPtr 1
  | n + 2 => trialDigitNat m endPtr (n + 2) + 2 ^ 16 * trialValue m (endPtr - 2) n

theorem trialValue_step (m : Mem) (endPtr : BitVec 32) {n : Nat} (positive : 0 < n) :
    trialValue m endPtr n = trialDigitNat m endPtr n +
      2 ^ 16 * trialValue m (endPtr - BitVec.ofNat 32 (min 2 n)) (n - min 2 n) := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => simp [trialValue]
    | succ n =>
      rw [Nat.min_eq_left (by omega : 2 ≤ n + 1 + 1)]
      simp only [show n + 1 + 1 - 2 = n by omega]
      rfl

/-- Readability of the n bytes immediately preceding a native end pointer. -/
def TrialReadable (s : State) (endPtr : BitVec 32) (n : Nat) : Prop :=
  ∀ i < n, InRegions (s.rd ++ s.wr) (State.addr (endPtr - BitVec.ofNat 32 (i + 1))) 1

theorem TrialReadable.low {s : State} {endPtr : BitVec 32} {n : Nat}
    (h : TrialReadable s endPtr n) (positive : 0 < n) :
    InRegions (s.rd ++ s.wr) (State.addr (endPtr - 1)) 1 := h 0 positive

theorem TrialReadable.high {s : State} {endPtr : BitVec 32} {n : Nat}
    (h : TrialReadable s endPtr n) (more : 1 < n) :
    InRegions (s.rd ++ s.wr) (State.addr (endPtr - 2)) 1 := h 1 more

theorem TrialReadable.advance {s t : State} {endPtr : BitVec 32} {n c : Nat} {rs : List Reg}
    (h : TrialReadable s endPtr n) (rest : Rest rs s t) (bound : c ≤ n) :
    TrialReadable t (endPtr - BitVec.ofNat 32 c) (n - c) := by
  intro i hi
  rw [rest.rd, rest.wr, BitVec.sub_sub, ← BitVec.ofNat_add]
  have offset : c + (i + 1) = c + i + 1 := by omega
  rw [offset]
  exact h (c + i) (by omega)

end VG.Proof.Ffdh.Arm.ParameterCandidate
