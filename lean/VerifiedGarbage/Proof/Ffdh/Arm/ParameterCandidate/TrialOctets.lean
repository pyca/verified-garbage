module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialValue
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

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
      omega
    rw [offset]
  · change [m (State.addr (endPtr - BitVec.ofNat 32 (n + 2 - (n + 0)))),
        m (State.addr (endPtr - BitVec.ofNat 32 (n + 2 - (n + 1))))] = _
    rw [show n + 2 - (n + 0) = 2 by omega, show n + 2 - (n + 1) = 1 by omega]
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
        rw [trialValue, trialBytes_pair, ih n (by omega)]
        rw [show [m (State.addr (endPtr - 2)), m (State.addr (endPtr - 1))] =
          [m (State.addr (endPtr - 2))] ++ [m (State.addr (endPtr - 1))] from rfl,
          ← List.append_assoc, VG.Proof.Rsa.os2ip_snoc, VG.Proof.Rsa.os2ip_snoc]
        simp only [trialDigitNat, show n + 1 + 1 ≠ 1 by omega, ite_false]
        omega

theorem trialBytes_at (m : Mem) (dst : BitVec 32) {n : Nat}
    (fits : n < 2 ^ 32) (bufferFits : dst.toNat + n ≤ 2 ^ 32) :
    trialBytes m (dst + BitVec.ofNat 32 n) n = Spec.Rsa.bytesAt m (State.addr dst) n := by
  unfold trialBytes Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro j hj
  have bound := List.mem_range.mp hj
  have ptr : dst + BitVec.ofNat 32 n - BitVec.ofNat 32 (n - j) = dst + BitVec.ofNat 32 j := by
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
    congr 2
    omega
  rw [ptr, VG.Arm.addr_add (by omega : dst.toNat + j < 2 ^ 32)]

end VG.Proof.Ffdh.Arm.ParameterCandidate
