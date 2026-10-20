module

public import VerifiedGarbage.Proof.Dsa.AArch64.SignCompute
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyCompute
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Arithmetic

/-! # Connecting implementation acceptance masks with DSA's operational checks -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.Impl.Dsa.Layout

/-- The public checks express domain consistency and public-key validity;
no exact or probabilistic primality proposition appears in the proof. -/
theorem publicAccepted_spec (L : ExecutionLayout) (gb yb : List Byte)
    (hsize : Spec.Dsa.supportedSizes (Spec.Dsa.bitLength L.modulus) (Spec.Dsa.bitLength L.subgroup))
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1) :
    publicAccepted L gb yb true =
      (decide (Spec.Dsa.parametersValid ⟨L.modulus, L.subgroup, Spec.Dsa.decodeBE gb⟩) &&
        Spec.Dsa.keyValid ⟨⟨L.modulus, L.subgroup, Spec.Dsa.decodeBE gb⟩, Spec.Dsa.decodeBE yb, none⟩) := by
  have hqp := (VG.Proof.Dsa.supported_bounds hsize).2.2
  apply Bool.eq_iff_iff.mpr
  simp only [publicAccepted, Spec.Dsa.parametersValid, Spec.Dsa.keyValid,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.and_true, hsize, hop, hoq, hqp, true_and]
  simp only [and_assoc, and_left_comm, and_comm]

theorem privateAccepted_spec (L : ExecutionLayout) (data : SignValues) (yb : List Byte)
    (hsize : Spec.Dsa.supportedSizes (Spec.Dsa.bitLength L.modulus) (Spec.Dsa.bitLength L.subgroup))
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hyl : yb.length = L.pLen) :
    privateAccepted L data yb true =
      (decide (Spec.Dsa.parametersValid ⟨L.modulus, L.subgroup, Spec.Dsa.decodeBE data.generator⟩) &&
        Spec.Dsa.keyValid ⟨⟨L.modulus, L.subgroup, Spec.Dsa.decodeBE data.generator⟩,
          Spec.Dsa.decodeBE yb, some (Spec.Dsa.decodeBE data.privateScalar)⟩ &&
        decide (0 < Spec.Dsa.decodeBE data.nonce ∧ Spec.Dsa.decodeBE data.nonce < L.subgroup)) := by
  have hp := (VG.Proof.Dsa.supported_bounds hsize).1
  have hfit := Nat.lt_of_lt_of_le (VG.Proof.Dsa.powMod_lt (Spec.Dsa.decodeBE data.generator)
    (Spec.Dsa.decodeBE data.privateScalar) (by omega : 0 < L.modulus)) hpf
  unfold privateAccepted
  rw [publicAccepted_spec L data.generator yb hsize hop hoq]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, VG.Proof.Dsa.encodeBE_eq_bytes hyl hfit,
    Spec.Dsa.keyValid, beq_iff_eq, Bool.and_true]
  simp only [and_assoc, and_left_comm, and_comm]

theorem signAccepted_nonzero (L : ExecutionLayout) (data : SignValues) (yb : List Byte) (valid : Bool)
    (hq : 0 < L.subgroup) (hqf : L.subgroup ≤ 256 ^ L.qLen) :
    signAccepted L data yb valid =
      (decide (data.s L ≠ 0) && (decide (data.r L ≠ 0) && privateAccepted L data yb valid)) := by
  have hr : data.r L < L.subgroup := Nat.mod_lt _ hq
  have hs : data.s L < L.subgroup := Nat.mod_lt _ hq
  unfold signAccepted
  simp only [← VG.Proof.Dsa.decodeBE_eq_zero,
    VG.Proof.Dsa.decodeBE_encodeBE (Nat.lt_of_lt_of_le hr hqf),
    VG.Proof.Dsa.decodeBE_encodeBE (Nat.lt_of_lt_of_le hs hqf), decide_not]

theorem verifyAccepted_value (L : ExecutionLayout) (data : VerifyValues) (valid : Bool)
    (hq : 0 < L.subgroup) (hqf : L.subgroup ≤ 256 ^ L.qLen) (hrl : data.signatureR.length = L.qLen) :
    verifyAccepted L data valid =
      (decide (data.value L = Spec.Dsa.decodeBE data.signatureR) &&
      (decide (0 < Spec.Dsa.decodeBE data.signatureS ∧ Spec.Dsa.decodeBE data.signatureS < L.subgroup) &&
      (decide (0 < Spec.Dsa.decodeBE data.signatureR ∧ Spec.Dsa.decodeBE data.signatureR < L.subgroup) &&
        publicAccepted L data.generator data.publicValue valid))) := by
  have hv : data.value L < L.subgroup := Nat.mod_lt _ hq
  unfold verifyAccepted
  simp only [VG.Proof.Dsa.encodeBE_eq_bytes hrl (Nat.lt_of_lt_of_le hv hqf)]

end VG.Proof.Dsa.AArch64
