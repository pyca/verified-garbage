module

public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingShape
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyBody
public import VerifiedGarbage.Proof.Dsa.X86_64.WorkspaceBridge
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingOperands
import VerifiedGarbage.Proof.Dsa.X86_64.WorkspaceReady

/-! # Establishing all verifying operands after public domain acceptance -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem VerifyingInput.shapeFacts {p : VerifyingInput} (ha : p.accepted = true) :
    Spec.Dsa.supportedSizes (Spec.Dsa.bitLength (Spec.Dsa.decodeBE p.components.p))
      (Spec.Dsa.bitLength (Spec.Dsa.decodeBE p.components.q)) ∧
    Spec.Dsa.decodeBE p.components.p % 2 = 1 ∧ Spec.Dsa.decodeBE p.components.q % 2 = 1 := by
  rw [VerifyingInput.accepted, shapeAccepted_spec] at ha
  exact of_decide_eq_true ha

def VerifyingInitialized (p : VerifyingInput) (original : State)
    (hp : original.gpr .rdx = BitVec.ofNat 64 p.pLen)
    (hq : original.gpr .rcx = BitVec.ofNat 64 p.qLen) (s : State) : Prop :=
  ∃ pi qi,
    Ready ((p.layout original hp hq).withInverses pi qi) s ∧
    VerificationOperands ((p.layout original hp hq).withInverses pi qi) p.values p.components.q s ∧
    word s.mem p.base Field.mask.offset = mask true ∧
    (∀ i < 6, word s.mem p.base (8 * i) = original.gpr (saved.getD i .rax)) ∧
    InScr p.base usedBytes original.mem s.mem ∧ Keep coreRegs original s

theorem verifyingInitialize_ok {p : VerifyingInput} {original s : State} (h : VerifyingPre p original)
    (hs : VerifyingShapePost p original h.pLength h.qLength s) (ha : p.accepted = true) :
    WP isa SignVerify.workspaces s (VerifyingInitialized p original h.pLength h.qLength) := by
  let L := p.layout original h.pLength h.qLength
  have hkey := h.keySource.congrK hs.frame hs.keep
  have hps : Src s L.base usedBytes (L.fields .p) p.components.p := source_take hkey
  have hqs : Src s L.base usedBytes (L.fields .q) p.components.q := by
    change Src s p.base usedBytes (original.gpr .rdi + original.gpr .rdx) p.components.q
    rw [h.pLength]
    exact source_slice hkey (by rw [p.keyLength]; omega)
  obtain ⟨_, hpo, hqo⟩ := p.shapeFacts ha
  refine WP.mono (workspacesReady_ok (L := L) hs.scratch hs.rdi hs.fields hps hqs p.components.pLength p.components.qLength
    rfl rfl hpo hqo) fun t ⟨pi, qi, hr, hf, hm, hk⟩ => ?_
  have hframe : InScr p.base usedBytes s.mem t.mem := InScr.of_outside hf (by decide)
  have hfull := hs.frame.trans hframe
  have hkeep := hs.keep.trans hk
  refine ⟨pi, qi, hr, verifyingOperands hr (h.keySource.congrK hfull hkeep)
    (h.signatureSource.congrK hfull hkeep) (h.digestSource.congrK hfull hkeep), ?_, ?_, hfull, hkeep.mono (by decide)⟩
  · exact hm.trans ((hs.fields .mask).trans (congrArg mask ha))
  · intro i hi
    exact (hf.word (Or.inl (by omega)) (by omega)).trans (hs.saved i hi)

end VG.Proof.Dsa.X86_64
