module
public import VerifiedGarbage.Proof.Dsa.X86_64.SignCompute

import VerifiedGarbage.Proof.Dsa.X86_64.AcceptedSpec
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Dsa.SizeBounds
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Dsa.SignVerify
import VerifiedGarbage.Proof.Dsa.Arithmetic

/-! # The computed scalars and rejection mask implement the packed signing spec -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG

def SignValues.key (L : ExecutionLayout) (data : SignValues) (yb : List Byte) : Spec.Dsa.Key :=
  ⟨⟨L.modulus, L.subgroup, Spec.Dsa.decodeBE data.generator⟩, Spec.Dsa.decodeBE yb,
    some (Spec.Dsa.decodeBE data.privateScalar)⟩

theorem signNonce_compute (L : ExecutionLayout) (data : SignValues) (yb digest : List Byte) (n : Nat)
    (hq : Spec.Dsa.bitLength L.subgroup = 8 * n) (hz : data.digest = digest.take n) :
    Spec.Dsa.signWithNonce (data.key L yb) digest (Spec.Dsa.decodeBE data.nonce) =
      if !Spec.Dsa.keyValid (data.key L yb) ||
          !(0 < Spec.Dsa.decodeBE data.nonce && Spec.Dsa.decodeBE data.nonce < L.subgroup) then none else
        if data.r L == 0 || data.s L == 0 then none else some ⟨data.r L, data.s L⟩ := by
  have h := VG.Proof.Dsa.signWithNonce_reduced (data.key L yb) digest (Spec.Dsa.decodeBE data.nonce)
    (Spec.Dsa.decodeBE data.privateScalar) n rfl hq
  simp only [SignValues.key, SignValues.r, SignValues.s, VG.Proof.Dsa.powMod_rsa, hz,
    Bool.or_eq_true, beq_iff_eq] at h ⊢
  convert h using 1
  congr 1

theorem signBytes_compute (L : ExecutionLayout) (data : SignValues) (yb key digest : List Byte) (n : Nat)
    (hsize : Spec.Dsa.supportedSizes (Spec.Dsa.bitLength L.modulus) (Spec.Dsa.bitLength L.subgroup))
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (hyl : yb.length = L.pLen) (hkl : key.length = 3 * L.pLen + 2 * L.qLen)
    (hnl : data.nonce.length = L.qLen)
    (hk : Spec.Dsa.privateKeyBytes L.pLen L.qLen key = data.key L yb)
    (hq : Spec.Dsa.bitLength L.subgroup = 8 * n) (hz : data.digest = digest.take n) :
    Spec.Dsa.signBytes L.pLen L.qLen key data.nonce digest =
      if signAccepted L data yb true then some (Spec.Dsa.encodeBE L.qLen (data.r L) ++
        Spec.Dsa.encodeBE L.qLen (data.s L)) else none := by
  have hqpos : 0 < L.subgroup := by have := (VG.Proof.Dsa.supported_bounds hsize).2.1; omega
  rw [signAccepted_nonzero L data yb true hqpos hqf, privateAccepted_spec L data yb hsize hop hoq hpf hyl]
  unfold Spec.Dsa.signBytes
  simp only [L.lengths, decide_true, Bool.not_true, hkl, hnl, bne_self_eq_false,
    Bool.false_or, Bool.false_eq_true, ↓reduceIte, hk]
  rw [signNonce_compute L data yb digest n hq hz]
  change (if !decide (Spec.Dsa.parametersValid (data.key L yb).params) then none else
    (if !Spec.Dsa.keyValid (data.key L yb) ||
      !(0 < Spec.Dsa.decodeBE data.nonce && Spec.Dsa.decodeBE data.nonce < L.subgroup) then none else
      if data.r L == 0 || data.s L == 0 then none else some (⟨data.r L, data.s L⟩ : Spec.Dsa.Signature)) >>= fun sig =>
        some (Spec.Dsa.encodeBE L.qLen sig.r ++ Spec.Dsa.encodeBE L.qLen sig.s)) = _
  by_cases hp : Spec.Dsa.parametersValid (data.key L yb).params <;>
    cases hv : Spec.Dsa.keyValid (data.key L yb) <;>
    by_cases hn : 0 < Spec.Dsa.decodeBE data.nonce ∧ Spec.Dsa.decodeBE data.nonce < L.subgroup <;>
    by_cases hr : data.r L = 0 <;> by_cases hs : data.s L = 0 <;>
    simp_all [SignValues.key, ← Bool.decide_and]

end VG.Proof.Dsa.X86_64
