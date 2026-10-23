module

public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyBody
public import VerifiedGarbage.Proof.Dsa.AArch64.PrevalidatedCompute
public import VerifiedGarbage.Spec.Dsa.Prevalidated
import VerifiedGarbage.Proof.Dsa.AArch64.AcceptedSpec
public import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify
import VerifiedGarbage.Proof.Dsa.AArch64.Result
import VerifiedGarbage.Proof.Dsa.SizeBounds

/-! # Verification computation, result return and ABI register restoration -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def prevalidatedBody (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (Prevalidated.compute mul) (.block SignVerify.result)

theorem prevalidatedBody_ok (M : Mont) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup)
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (data : VerifyValues) {qb : List Byte} (h : VerificationOperands L data qb s0)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid) :
    WP isa (prevalidatedBody M.mm) s0 fun t =>
      t.gpr .x0 = BitVec.ofNat 64 (prevalidatedAccepted L data valid).toNat ∧
      Outside L.base 128 (usedBytes - 128) s0.mem t.mem ∧ Keep coreRegs s0 t := by
  unfold prevalidatedBody
  refine WP.seq (WP.mono (prevalidatedCompute_ok M h0 hp hq hop hoq hpf hqf data h.generator h.publicValue
    h.signatureR h.signatureS h.digest h.generatorLength h.publicLength
    h.rLength h.sLength h.digestBound hm)
    fun s1 ⟨h1, hm1, hf1, hk1⟩ => ?_)
  refine WP.mono (result_ok h1.scratch h1.parent.x0 (by decide) hm1)
    fun t ⟨ha, hmem, hk⟩ => ?_
  exact ⟨ha,
    by rw [hmem]; exact hf1, (hk1.trans hk).mono (by decide)⟩

theorem prevalidatedBody_spec (M : Mont) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (data : VerifyValues) {qb key signature digest : List Byte} {n : Nat}
    (h : VerificationOperands L data qb s0)
    (hsize : Spec.Dsa.supportedSizes (Spec.Dsa.bitLength L.modulus) (Spec.Dsa.bitLength L.subgroup))
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (hkl : key.length = 3 * L.pLen + L.qLen) (hsl : signature.length = 2 * L.qLen)
    (hk : Spec.Dsa.publicKeyBytes L.pLen L.qLen key = data.key L)
    (hr : signature.take L.qLen = data.signatureR) (hs : signature.drop L.qLen = data.signatureS)
    (hqn : Spec.Dsa.bitLength L.subgroup = 8 * n) (hz : data.digest = digest.take n)
    (hv : Spec.Dsa.validatePublicKeyBytes L.pLen L.qLen key = true)
    (hm : word s0.mem L.base Field.mask.offset = mask true) :
    WP isa (prevalidatedBody M.mm) s0 fun t =>
      t.gpr .x0 = BitVec.ofNat 64 (Spec.Dsa.verifyBytes L.pLen L.qLen key signature digest).toNat ∧
      Outside L.base 128 (usedBytes - 128) s0.mem t.mem ∧ Keep coreRegs s0 t := by
  obtain ⟨hp, hq, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  have hv' : publicAccepted L data.generator data.publicValue true = true := by
    rw [publicAccepted_spec L data.generator data.publicValue hsize hop hoq]
    simpa only [Spec.Dsa.validatePublicKeyBytes, L.lengths, decide_true, Bool.not_true,
      hkl, bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte, hk,
      VerifyValues.key] using hv
  have he : verifyAccepted L data true = prevalidatedAccepted L data true := by
    simp only [verifyAccepted, prevalidatedAccepted, hv']
  rw [verifyBytes_compute L data key signature digest n hsize hop hoq hqf h.rLength hkl hsl hk hr hs hqn hz, he]
  exact prevalidatedBody_ok M h0 hp hq hop hoq hpf hqf data h hm

end VG.Proof.Dsa.AArch64
