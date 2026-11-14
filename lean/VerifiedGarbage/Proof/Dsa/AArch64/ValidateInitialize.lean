module

public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingShape
import VerifiedGarbage.Proof.Dsa.AArch64.ValidateEntry
public import VerifiedGarbage.Impl.Dsa.AArch64.Prevalidated
public import VerifiedGarbage.Proof.Dsa.AArch64.InitializedFields
public import VerifiedGarbage.Spec.Dsa
import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Proof.Dsa.AArch64.InitializedLayout
public import VerifiedGarbage.Impl.Dsa.AArch64.Workspace
public import VerifiedGarbage.Proof.Dsa.AArch64.Execution
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingInput
import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingInitialize
import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceReady
import VerifiedGarbage.Proof.Dsa.AArch64.SigningOperands
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Dsa.AArch64.ValidateShape`, which only this module used -/

section

/-! # Argument capture and public-domain validation for a complete verifying attempt -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure ValidatingPre (p : VerifyingInput) (s : State) : Prop where
  scratch : Scr s p.base usedBytes
  pLength : s.gpr .x2 = BitVec.ofNat 64 p.pLen
  qLength : s.gpr .x3 = BitVec.ofNat 64 p.qLen
  base : s.gpr .x4 = p.base
  keySource : Src s p.base usedBytes (s.gpr .x0) p.key
  digestNil : p.digest = []
  digestPointer : p.digestPointer = 0

theorem validatingShape_ok {p : VerifyingInput} {s0 : State} (h : ValidatingPre p s0) :
    WP isa (.seq (.block Prevalidated.validateEntry) Checks.domainShape) s0 (VerifyingShapePost p s0 h.pLength h.qLength) := by
  refine WP.seq (WP.mono (validateEntry_ok h.scratch h.base (by decide)) fun s1 he => ?_)
  have hinside : InScr p.base usedBytes s0.mem s1.mem := InScr.of_outside he.frame (by decide)
  have hkey := h.keySource.congrK hinside he.keep
  have hps : Src s1 p.base usedBytes (s0.gpr .x0) p.components.p := source_take hkey
  have hqs : Src s1 p.base usedBytes (s0.gpr .x0 + BitVec.ofNat 64 p.pLen) p.components.q :=
    source_slice hkey (by rw [p.keyLength]; omega_using [])
  have hp1 : 0 < p.components.p.length := by
    rw [p.components.pLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]
  have hq1 : 0 < p.components.q.length := by
    rw [p.components.qLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]
  have hp64 : p.components.p.length < 2 ^ 64 := by
    rw [p.components.pLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]
  have hq64 : p.components.q.length < 2 ^ 64 := by
    rw [p.components.qLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]
  refine WP.mono (domainShape_ok (h.scratch.congr he.keep.wr) he.base (by decide) (he.fields .p (by decide) (by decide))
    (by rw [he.fields .q (by decide) (by decide)]; change _ + s0.gpr .x2 = _; rw [h.pLength])
    (by rw [he.fields .pLen (by decide) (by decide)]; change s0.gpr .x2 = _; rw [h.pLength, p.components.pLength])
    (by rw [he.fields .qLen (by decide) (by decide)]; change s0.gpr .x3 = _; rw [h.qLength, p.components.qLength]) hps hqs hp1 hp64 hq1 hq64 rfl rfl
    p.digestBound (by rw [he.fields .digestLen (by decide) (by decide), h.digestNil]; rfl)) fun s2 ⟨hprefix, hmask, hbranch, hf, hk⟩ => ?_
  have hall := he.keep.trans hk
  have hft : InScr p.base usedBytes s1.mem s2.mem := by
    apply InScr.of_frm hf
    intro range hr
    simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide
  refine ⟨h.scratch.congr hall.wr, (hk.gpr .x0 (by decide)).trans he.base,
    ?_, hbranch,
    hinside.trans hft,
    hall.mono (by decide)⟩
  intro f
  by_cases hm : f = .mask
  · subst f; exact hmask
  by_cases hp : f = .digestPrefixLen
  · subst f; exact hprefix
  rw [shape_field hf f hp hm, he.fields f hm hp]
  simp only [VerifyingInput.layout, h.digestPointer, h.digestNil, List.length_nil,
    VerifyingInput.prefixLength, Nat.min_eq_left (Nat.zero_le _)]
  cases f <;> simp_all [verifyFieldValues]


end VG.Proof.Dsa.AArch64

end

end

/-! # Establishing all verifying operands after public domain acceptance -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/ValidateOperands.lean`, which only this module imported.
section

/-! # Packed verification operands after workspace initialization -/

section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem validatingOperands {p : VerifyingInput} {original s : State}
    {hp : original.gpr .x2 = BitVec.ofNat 64 p.pLen}
    {hq : original.gpr .x3 = BitVec.ofNat 64 p.qLen} {pi qi : BitVec 64}
    (h : Ready ((p.layout original hp hq).withInverses pi qi) s)
    (hkey : Src s p.base usedBytes (original.gpr .x0) p.key)
 :
    OperandBytes s p.base usedBytes Core.generator p.components.g ∧
    OperandBytes s p.base usedBytes Core.publicValue p.components.y ∧
    OperandBytes s p.base usedBytes ⟨.input .q, .qLen⟩ p.components.q := by
  let L := (p.layout original hp hq).withInverses pi qi
  have hqlen : p.components.q.length = p.qLen := p.components.qLength
  have hglen : p.components.g.length = p.pLen := p.components.gLength
  have hylen : p.components.y.length = p.pLen := p.components.yLength
  have qptr : L.fields .q = original.gpr .x0 + BitVec.ofNat 64 p.pLen := by
    change original.gpr .x0 + original.gpr .x2 = _
    rw [hp]
  have gptr : L.fields .g = original.gpr .x0 + BitVec.ofNat 64 (p.pLen + p.qLen) := by
    change original.gpr .x0 + original.gpr .x2 + original.gpr .x3 = _
    rw [hp, hq, Offset.add_add]
  have yptr : L.fields .y = original.gpr .x0 + BitVec.ofNat 64 (2 * p.pLen + p.qLen) := by
    change original.gpr .x0 + original.gpr .x2 + original.gpr .x3 + original.gpr .x2 = _
    rw [hp, hq, Offset.add_add, Offset.add_add, show p.pLen + (p.qLen + p.pLen) = 2 * p.pLen + p.qLen by omega]
  have hqsrc : Src s p.base usedBytes (L.fields .q) p.components.q := by
    rw [qptr]; exact source_slice hkey (by rw [p.keyLength]; omega)
  have hgsrc : Src s p.base usedBytes (L.fields .g) p.components.g := by
    rw [gptr]; exact source_slice hkey (by rw [p.keyLength]; omega)
  have hysrc : Src s p.base usedBytes (L.fields .y) p.components.y := by
    rw [yptr]; exact source_slice hkey (by rw [p.keyLength]; omega)
  have hpfield : L.fields .pLen = BitVec.ofNat 64 p.pLen := hp
  have hqfield : L.fields .qLen = BitVec.ofNat 64 p.qLen  := hq
  refine ⟨h.inputOperand .g .pLen (by decide) (by decide) hgsrc (by change L.fields .pLen = BitVec.ofNat 64 p.components.g.length; rw [hglen]; exact hpfield),
    h.inputOperand .y .pLen (by decide) (by decide) hysrc (by change L.fields .pLen = BitVec.ofNat 64 p.components.y.length; rw [hylen]; exact hpfield),
    h.inputOperand .q .qLen (by decide) (by decide) hqsrc (by rw [hqlen]; exact hqfield)⟩

end VG.Proof.Dsa.AArch64
end

end

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
    exact source_slice hkey (by rw [p.keyLength]; omega_using [])
  obtain ⟨_, hpo, hqo⟩ := p.shapeFacts ha
  refine WP.mono (workspacesReady_ok (L := L) hs.scratch hs.x0 hs.fields hps hqs p.components.pLength p.components.qLength
    rfl rfl hpo hqo) fun t ⟨pi, qi, hr, hf, hm, hk⟩ => ?_
  have hframe : InScr p.base usedBytes s.mem t.mem := InScr.of_outside hf (by decide)
  have hfull := hs.frame.trans hframe
  have hkeep := hs.keep.trans hk
  refine ⟨pi, qi, hr, validatingOperands hr (h.keySource.congrK hfull hkeep), ?_, hfull, hkeep.mono (by decide)⟩
  · exact hm.trans ((hs.fields .mask).trans (congrArg mask ha))

end VG.Proof.Dsa.AArch64
