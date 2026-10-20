module

public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyBytesSpec
public import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify
import VerifiedGarbage.Proof.Dsa.X86_64.Result
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Dsa.SizeBounds
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-! # Verification computation, result return and ABI register restoration -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure VerificationOperands (L : ExecutionLayout) (data : VerifyValues) (qb : List Byte) (s : State) : Prop where
  generator : OperandBytes s L.base usedBytes Core.generator data.generator
  publicValue : OperandBytes s L.base usedBytes Core.publicValue data.publicValue
  subgroup : OperandBytes s L.base usedBytes ⟨.input .q, .qLen⟩ qb
  signatureR : OperandBytes s L.base usedBytes Core.signatureR data.signatureR
  signatureS : OperandBytes s L.base usedBytes Core.signatureS data.signatureS
  digest : OperandBytes s L.base usedBytes Core.digest data.digest
  generatorLength : data.generator.length = L.pLen
  publicLength : data.publicValue.length = L.pLen
  subgroupLength : qb.length = L.qLen
  rLength : data.signatureR.length = L.qLen
  sLength : data.signatureS.length = L.qLen
  digestBound : data.digest.length < 2 ^ 64
  subgroupValue : Spec.Dsa.decodeBE qb = L.subgroup

def verifyBody (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (verifyCompute sq mul) (.block SignVerify.result)

theorem verifyBody_ok (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup)
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (data : VerifyValues) {qb : List Byte} (h : VerificationOperands L data qb s0)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid) :
    WP isa (verifyBody Sq.mm M.mm) s0 fun t =>
      t.gpr .rax = BitVec.ofNat 64 (verifyAccepted L data valid).toNat ∧
      (∀ i < 6, t.gpr (saved.getD i .rax) = word s0.mem L.base (8 * i)) ∧
      Outside L.base 128 (usedBytes - 128) s0.mem t.mem ∧ Keep coreRegs s0 t := by
  unfold verifyBody
  refine WP.seq (WP.mono (verifyCompute_ok M Sq h0 hp hq hop hoq hpf hqf data h.generator h.publicValue
    h.subgroup h.signatureR h.signatureS h.digest h.generatorLength h.publicLength h.subgroupLength
    h.rLength h.sLength h.digestBound h.subgroupValue hm)
    fun s1 ⟨h1, hm1, hf1, hk1⟩ => ?_)
  refine WP.mono (result_ok h1.scratch h1.parent.rdi (by decide) hm1)
    fun t ⟨ha, hsave, hmem, hk⟩ => ?_
  exact ⟨ha, fun i hi => (hsave i hi).trans (hf1.word (Or.inl (by omega)) (by omega)),
    by rw [hmem]; exact hf1, (hk1.trans hk).mono (by decide)⟩

theorem verifyBody_spec (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (data : VerifyValues) {qb key signature digest : List Byte} {n : Nat}
    (h : VerificationOperands L data qb s0)
    (hsize : Spec.Dsa.supportedSizes (Spec.Dsa.bitLength L.modulus) (Spec.Dsa.bitLength L.subgroup))
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (hkl : key.length = 3 * L.pLen + L.qLen) (hsl : signature.length = 2 * L.qLen)
    (hk : Spec.Dsa.publicKeyBytes L.pLen L.qLen key = data.key L)
    (hr : signature.take L.qLen = data.signatureR) (hs : signature.drop L.qLen = data.signatureS)
    (hqn : Spec.Dsa.bitLength L.subgroup = 8 * n) (hz : data.digest = digest.take n)
    (hm : word s0.mem L.base Field.mask.offset = mask true) :
    WP isa (verifyBody Sq.mm M.mm) s0 fun t =>
      t.gpr .rax = BitVec.ofNat 64 (Spec.Dsa.verifyBytes L.pLen L.qLen key signature digest).toNat ∧
      (∀ i < 6, t.gpr (saved.getD i .rax) = word s0.mem L.base (8 * i)) ∧
      Outside L.base 128 (usedBytes - 128) s0.mem t.mem ∧ Keep coreRegs s0 t := by
  obtain ⟨hp, hq, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  rw [verifyBytes_compute L data key signature digest n hsize hop hoq hqf h.rLength hkl hsl hk hr hs hqn hz]
  exact verifyBody_ok M Sq h0 hp hq hop hoq hpf hqf data h hm

end VG.Proof.Dsa.X86_64
