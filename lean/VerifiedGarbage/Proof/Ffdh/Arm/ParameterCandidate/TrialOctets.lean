module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialValue
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `Ffdh.Arm.ParameterCandidate.TrialMath`, which the modules that import this one used -/

section

/-! Compose the shared RSA reducer over a variable number of byte pairs.
FFDH also permits byte lengths that are not multiples of eight. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate

/-- Move one consumed digit from the unprocessed suffix into the scaled
accumulator, preserving the original candidate modulo the divisor. -/
theorem trialRemaining_congruence {s acc next digit remaining value j : Nat}
    (step : next * 2 ^ 16 % s = (digit + acc) % s)
    (previous : (acc + (digit + 2 ^ 16 * remaining)) * 2 ^ (16 * j) % s = value % s) :
    (next + remaining) * 2 ^ (16 * (j + 1)) % s = value % s := by
  have scale : ∀ {a b : Nat} (c : Nat), a % s = b % s → a * c % s = b * c % s :=
    fun c h => by rw [Nat.mul_mod, h, ← Nat.mul_mod]
  have add : (next * 2 ^ 16 + remaining * 2 ^ 16) % s =
      (digit + acc + remaining * 2 ^ 16) % s := by
    rw [Nat.add_mod, step, ← Nat.add_mod]
  have power : (next + remaining) * 2 ^ (16 * (j + 1)) =
      (next * 2 ^ 16 + remaining * 2 ^ 16) * 2 ^ (16 * j) := by
    rw [← Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    omega_using []
  rw [power, scale _ add]
  have rearrange : digit + acc + remaining * 2 ^ 16 = acc + (digit + 2 ^ 16 * remaining) := by
    rw [Nat.mul_comm remaining]
    omega_using []
  rw [rearrange]
  exact previous

/-- An odd divisor is coprime to every power of the reduction radix. -/
theorem trialDigit_divides {acc value divisor j : Nat}
    (odd : divisor % 2 = 1) (bound : acc < 2 * divisor)
    (congruence : acc * 2 ^ (16 * j) % divisor = value % divisor) :
    value % divisor = 0 ↔ acc = 0 ∨ acc = divisor := by
  have coprime : Nat.Coprime divisor (2 ^ (16 * j)) := by
    apply Nat.Coprime.pow_right
    show Nat.gcd divisor 2 = 1
    rw [Nat.gcd_comm, Nat.gcd_rec, odd]
    rfl
  rw [← congruence]
  constructor
  · intro zero
    have divides : divisor ∣ acc := coprime.dvd_of_dvd_mul_right (Nat.dvd_of_mod_eq_zero zero)
    obtain ⟨q, eq⟩ := divides
    rcases q with _ | _ | q
    · left; rw [eq, Nat.mul_zero]
    · right; rw [eq, Nat.mul_one]
    · exfalso
      rw [eq] at bound
      have := Nat.mul_le_mul_left divisor (show 2 ≤ q + 1 + 1 by omega_using [])
      omega_using [bound, this]
  · rintro (rfl | rfl)
    · simp
    · exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right _ _)

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! RSA's trial reducer reads FFDH's big-endian encoding backwards in
pairs; grouping the octets leaves the encoded integer unchanged. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm

def trialBytes (m : Mem) (endPtr : BitVec 32) (n : Nat) : List Byte :=
  (List.range n).map fun j => m (State.addr (endPtr - BitVec.ofNat 32 (n - j)))

theorem trialBytes_pair (m : Mem) (endPtr : BitVec 32) (n : Nat) :
    trialBytes m endPtr (n + 2) = trialBytes m (endPtr - 2) n ++
      [m (State.addr (endPtr - 2)), m (State.addr (endPtr - 1))] := by
  unfold trialBytes
  rw [List.range_add, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro j hj
    have bound := List.mem_range.mp hj
    rw [BitVec.sub_sub]
    have offset : (2 : BitVec 32) + BitVec.ofNat 32 (n - j) = BitVec.ofNat 32 (n + 2 - j) := by
      change BitVec.ofNat 32 2 + BitVec.ofNat 32 (n - j) = _
      rw [BitVec.ofNat_add_ofNat]
      congr 1
      omega_using [bound]
    rw [offset]
  · change [m (State.addr (endPtr - BitVec.ofNat 32 (n + 2 - (n + 0)))),
        m (State.addr (endPtr - BitVec.ofNat 32 (n + 2 - (n + 1))))] = _
    rw [show n + 2 - (n + 0) = 2 by omega_using [], show n + 2 - (n + 1) = 1 by omega_using []]
    rfl

theorem trialValue_octets (m : Mem) (endPtr : BitVec 32) (n : Nat) :
    trialValue m endPtr n = Spec.Rsa.os2ip (trialBytes m endPtr n) := by
  induction n using Nat.strongRecOn generalizing endPtr with
  | ind n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => simp [trialValue, trialDigitNat, trialBytes, Spec.Rsa.os2ip]
      | succ n =>
        rw [trialValue, trialBytes_pair, ih n (by omega_using [])]
        rw [show [m (State.addr (endPtr - 2)), m (State.addr (endPtr - 1))] =
          [m (State.addr (endPtr - 2))] ++ [m (State.addr (endPtr - 1))] from rfl,
          ← List.append_assoc, VG.Proof.Rsa.os2ip_snoc, VG.Proof.Rsa.os2ip_snoc]
        simp only [trialDigitNat, show n + 1 + 1 ≠ 1 by omega_using [], ite_false]
        omega_using []

theorem trialBytes_at (m : Mem) (dst : BitVec 32) {n : Nat}
    (fits : n < 2 ^ 32) (bufferFits : dst.toNat + n ≤ 2 ^ 32) :
    trialBytes m (dst + BitVec.ofNat 32 n) n = Spec.Rsa.bytesAt m (State.addr dst) n := by
  unfold trialBytes Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro j hj
  have bound := List.mem_range.mp hj
  have ptr : dst + BitVec.ofNat 32 n - BitVec.ofNat 32 (n - j) = dst + BitVec.ofNat 32 j := by
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using [fits]) (by omega_using [])]
    congr 2
    omega_using [bound]
  rw [ptr, VG.Arm.addr_add (by omega_using [bufferFits, bound] : dst.toNat + j < 2 ^ 32)]

end VG.Proof.Ffdh.Arm.ParameterCandidate
