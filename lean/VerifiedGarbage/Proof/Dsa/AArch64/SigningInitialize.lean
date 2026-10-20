module

public import VerifiedGarbage.Proof.Dsa.AArch64.SigningShape
public import VerifiedGarbage.Proof.Dsa.AArch64.InitializedLayout
public import VerifiedGarbage.Proof.Dsa.AArch64.SignBody
import VerifiedGarbage.Proof.Dsa.AArch64.SigningOperands
import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceReady

/-! # Establishing all signing operands after public domain acceptance -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem SigningInput.shapeFacts {p : SigningInput} (ha : p.accepted = true) :
    Spec.Dsa.supportedSizes (Spec.Dsa.bitLength (Spec.Dsa.decodeBE p.components.p))
      (Spec.Dsa.bitLength (Spec.Dsa.decodeBE p.components.q)) ∧
    Spec.Dsa.decodeBE p.components.p % 2 = 1 ∧ Spec.Dsa.decodeBE p.components.q % 2 = 1 := by
  rw [SigningInput.accepted, shapeAccepted_spec] at ha
  exact of_decide_eq_true ha

def SigningInitialized (p : SigningInput) (original : State)
    (hp : original.gpr .x4 = BitVec.ofNat 64 p.pLen) (s : State) : Prop :=
  ∃ pi qi,
    Ready ((p.layout original hp).withInverses pi qi) s ∧
    SigningOperands ((p.layout original hp).withInverses pi qi) p.values p.components.y p.components.q s ∧
    word s.mem p.base Field.mask.offset = mask true ∧
    InScr p.base usedBytes original.mem s.mem ∧ Keep coreRegs original s

theorem signingInitialize_ok {p : SigningInput} {original s : State} (h : SigningPre p original)
    (hs : SigningShapePost p original h.pLength s) (ha : p.accepted = true) :
    WP isa SignVerify.workspaces s (SigningInitialized p original h.pLength) := by
  let L := p.layout original h.pLength
  have hkey := h.keySource.congrK hs.frame hs.keep
  have hps : Src s L.base usedBytes (L.fields .p) p.components.p := source_take hkey
  have hqs : Src s L.base usedBytes (L.fields .q) p.components.q := by
    change Src s p.base usedBytes (original.gpr .x2 + original.gpr .x4) p.components.q
    rw [h.pLength]
    exact source_slice hkey (by rw [p.keyLength]; omega)
  obtain ⟨_, hpo, hqo⟩ := p.shapeFacts ha
  refine WP.mono (workspacesReady_ok (L := L) hs.scratch hs.x0 hs.fields hps hqs p.components.pLength p.components.qLength
    rfl rfl hpo hqo) fun t ⟨pi, qi, hr, hf, hm, hk⟩ => ?_
  have hframe : InScr p.base usedBytes s.mem t.mem := InScr.of_outside hf (by decide)
  have hfull := hs.frame.trans hframe
  have hkeep := hs.keep.trans hk
  refine ⟨pi, qi, hr, signingOperands hr (h.keySource.congrK hfull hkeep)
    (h.nonceSource.congrK hfull hkeep) (h.digestSource.congrK hfull hkeep), ?_, hfull, hkeep.mono (by decide)⟩
  · exact hm.trans ((hs.fields .mask).trans (congrArg mask ha))

end VG.Proof.Dsa.AArch64
