module

public import VerifiedGarbage.Proof.Dsa.AArch64.ValidateInitialize
public import VerifiedGarbage.Spec.Dsa.Prevalidated
import VerifiedGarbage.Proof.Dsa.AArch64.AcceptedSpec
import VerifiedGarbage.Proof.Dsa.AArch64.Result
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.SizeBounds

/-! # Complete public-key algebraic validation, with the original rejection policy -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def ValidatingPost (p : VerifyingInput) (original t : State) : Prop :=
  t.gpr .x0 = BitVec.ofNat 64 (Spec.Dsa.validatePublicKeyBytes p.pLen p.qLen p.key).toNat ∧
  InScr p.base usedBytes original.mem t.mem ∧ Keep coreRegs original t

theorem validatingBody_ok (M : Mont) {p : VerifyingInput} {original s : State} (h : ValidatingPre p original)
    (hi : ValidatingInitialized p original h.pLength h.qLength s) (ha : p.accepted = true) :
    WP isa (seqs [Checks.publicKey M.mm, .block SignVerify.result]) s (ValidatingPost p original) := by
  obtain ⟨pi, qi, hr, ⟨hg, hy, hqb⟩, hm, hf, hk⟩ := hi
  let L := (p.layout original h.pLength h.qLength).withInverses pi qi
  obtain ⟨hsize, hpodd, hqodd⟩ := p.shapeFacts ha
  obtain ⟨hp, hq, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  have hpf : L.modulus ≤ 256 ^ L.pLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt p.components.p
    rw [p.components.pLength] at hh
    exact Nat.le_of_lt hh
  have hqf : L.subgroup ≤ 256 ^ L.qLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt p.components.q
    rw [p.components.qLength] at hh
    exact Nat.le_of_lt hh
  have he : Spec.Dsa.validatePublicKeyBytes p.pLen p.qLen p.key =
      publicAccepted L p.components.g p.components.y true := by
    rw [publicAccepted_spec L p.components.g p.components.y hsize hpodd hqodd]
    simp only [Spec.Dsa.validatePublicKeyBytes, p.lengths, decide_true, Bool.not_true,
      p.keyLength, bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    rfl
  refine WP.seq (WP.mono (publicKey_ok M hr hp hq hpodd hqodd hpf hqf hg hy hqb
    p.components.gLength p.components.yLength p.components.qLength rfl hm)
    fun t ⟨ht, hmask, _, hframe, hkeep⟩ => ?_)
  refine WP.mono (result_ok ht.scratch ht.parent.x0 (by decide) hmask) fun u ⟨hret, hmem, hku⟩ => ?_
  refine ⟨?_, ?_, ((hk.trans hkeep).trans hku).mono (by decide)⟩
  · rw [he]; exact hret
  · rw [hmem]
    exact hf.trans (InScr.of_outside hframe (by decide))

end VG.Proof.Dsa.AArch64
