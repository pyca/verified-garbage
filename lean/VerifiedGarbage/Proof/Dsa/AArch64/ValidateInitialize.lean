module

public import VerifiedGarbage.Proof.Dsa.AArch64.ValidateShape
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingInitialize
public import VerifiedGarbage.Proof.Dsa.AArch64.ValidateOperands
public import VerifiedGarbage.Proof.Dsa.AArch64.InitializedLayout
import VerifiedGarbage.Proof.Dsa.AArch64.VerifyBody
import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingOperands
import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceReady
public import VerifiedGarbage.Impl.Dsa.AArch64.Workspace
public import VerifiedGarbage.Proof.Dsa.AArch64.Execution

/-! # Establishing all verifying operands after public domain acceptance -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def ValidatingInitialized (p : VerifyingInput) (original : State)
    (hp : original.gpr .x2 = BitVec.ofNat 64 p.pLen)
    (hq : original.gpr .x3 = BitVec.ofNat 64 p.qLen) (s : State) : Prop :=
  ∃ pi qi,
    Ready ((p.layout original hp hq).withInverses pi qi) s ∧
    (OperandBytes s p.base usedBytes Core.generator p.components.g ∧
      OperandBytes s p.base usedBytes Core.publicValue p.components.y ∧
      OperandBytes s p.base usedBytes ⟨.input .q, .qLen⟩ p.components.q) ∧
    word s.mem p.base Field.mask.offset = mask true ∧
    InScr p.base usedBytes original.mem s.mem ∧ Keep coreRegs original s

theorem validatingInitialize_ok {p : VerifyingInput} {original s : State} (h : ValidatingPre p original)
    (hs : VerifyingShapePost p original h.pLength h.qLength s) (ha : p.accepted = true) :
    WP isa SignVerify.workspaces s (ValidatingInitialized p original h.pLength h.qLength) := by
  let L := p.layout original h.pLength h.qLength
  have hkey := h.keySource.congrK hs.frame hs.keep
  have hps : Src s L.base usedBytes (L.fields .p) p.components.p := source_take hkey
  have hqs : Src s L.base usedBytes (L.fields .q) p.components.q := by
    change Src s p.base usedBytes (original.gpr .x0 + original.gpr .x2) p.components.q
    rw [h.pLength]
    exact source_slice hkey (by rw [p.keyLength]; omega)
  obtain ⟨_, hpo, hqo⟩ := p.shapeFacts ha
  refine WP.mono (workspacesReady_ok (L := L) hs.scratch hs.x0 hs.fields hps hqs p.components.pLength p.components.qLength
    rfl rfl hpo hqo) fun t ⟨pi, qi, hr, hf, hm, hk⟩ => ?_
  have hframe : InScr p.base usedBytes s.mem t.mem := InScr.of_outside hf (by decide)
  have hfull := hs.frame.trans hframe
  have hkeep := hs.keep.trans hk
  refine ⟨pi, qi, hr, validatingOperands hr (h.keySource.congrK hfull hkeep), ?_, hfull, hkeep.mono (by decide)⟩
  · exact hm.trans ((hs.fields .mask).trans (congrArg mask ha))

end VG.Proof.Dsa.AArch64
