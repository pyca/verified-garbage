module

public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingInitialize
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyFailure
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.DomainWidths

/-! # Both verifying branches return the packed byte specification -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def VerifyingPost (p : VerifyingInput) (original t : State) : Prop :=
  t.gpr .rax = BitVec.ofNat 64 (Spec.Dsa.verifyBytes p.pLen p.qLen p.key p.signature p.digest).toNat ∧
  (∀ i < 6, t.gpr (saved.getD i .rax) = original.gpr (saved.getD i .rax)) ∧
  InScr p.base usedBytes original.mem t.mem ∧ Keep coreRegs original t

theorem verifyingAccepted_ok (M : Mont) (Sq : MontS) {p : VerifyingInput} {original s : State} (h : VerifyingPre p original)
    (hi : VerifyingInitialized p original h.pLength h.qLength s) (ha : p.accepted = true) :
    WP isa (verifyBody Sq.mm M.mm) s (VerifyingPost p original) := by
  obtain ⟨pi, qi, hr, ho, hm, hsave, hf, hk⟩ := hi
  let L := (p.layout original h.pLength h.qLength).withInverses pi qi
  obtain ⟨hsize, hpodd, hqodd⟩ := p.shapeFacts ha
  have hpf : L.modulus ≤ 256 ^ L.pLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt p.components.p
    rw [p.components.pLength] at hh
    exact Nat.le_of_lt hh
  have hqf : L.subgroup ≤ 256 ^ L.qLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt p.components.q
    rw [p.components.qLength] at hh
    exact Nat.le_of_lt hh
  have hqn := VG.Proof.Dsa.subgroup_scan_width hsize
  have hkey : Spec.Dsa.publicKeyBytes L.pLen L.qLen p.key = p.values.key L := rfl
  refine WP.mono (verifyBody_spec M Sq (L := L) hr p.values ho hsize hpodd hqodd hpf hqf
    p.keyLength p.signatureLength hkey rfl rfl hqn rfl hm)
    fun t ⟨hret, hsaved, hframe, hkeep⟩ => ?_
  exact ⟨hret, fun i hi => (hsaved i hi).trans (hsave i hi),
    hf.trans (InScr.of_outside hframe (by decide)), (hk.trans hkeep).mono (by decide)⟩

theorem verifyingRejected_ok {p : VerifyingInput} {original s : State} (h : VerifyingPre p original)
    (hs : VerifyingShapePost p original h.pLength h.qLength s) (ha : p.accepted = false) :
    WP isa (.block (([.mov32 .rax (.imm 0)] : List Instr) ++ VG.Impl.Bignum.X86_64.Public.exit)) s
      (VerifyingPost p original) := by
  have hparams : ¬ Spec.Dsa.parametersValid (Spec.Dsa.publicKeyBytes p.pLen p.qLen p.key).params :=
    shapeAccepted_false ha (Spec.Dsa.decodeBE p.components.g)
  have hfalse := verifyBytes_invalid_shape (signature := p.signature) (digest := p.digest) hparams
  refine WP.mono (verifyFailure_ok hs.scratch hs.rdi (by decide))
    fun t ⟨hret, hsave, hmem, hk⟩ => ?_
  unfold VerifyingPost
  rw [hfalse]
  exact ⟨hret, fun i hi => (hsave i hi).trans (hs.saved i hi),
    by rw [hmem]; exact hs.frame, (hs.keep.trans hk).mono (by decide)⟩

end VG.Proof.Dsa.X86_64
