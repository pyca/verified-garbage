module

public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyBody
public import VerifiedGarbage.Proof.Dsa.X86_64.WorkspaceBridge
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingInput

import VerifiedGarbage.Proof.Dsa.X86_64.WorkspaceReady
import VerifiedGarbage.Proof.Dsa.X86_64.SigningShape
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import VerifiedGarbage.Proof.Dsa.X86_64.SigningOperands
import VerifiedGarbage.Proof.Framework.AddrArith
/-! # Establishing all verifying operands after public domain acceptance -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/VerifyingShape.lean`, which only this module imported.
section

/-! # Argument capture and public-domain validation for a complete verifying attempt -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure VerifyingShapePost (p : VerifyingInput) (original : State)
    (hp : original.gpr .rdx = BitVec.ofNat 64 p.pLen)
    (hq : original.gpr .rcx = BitVec.ofNat 64 p.qLen) (s : State) : Prop where
  scratch : Scr s p.base usedBytes
  rdi : s.gpr .rdi = p.base
  fields : ∀ f, word s.mem p.base f.offset = (p.layout original hp hq).fields f
  branch : s.zf = some (!p.accepted)
  saved : ∀ i < 6, word s.mem p.base (8 * i) = original.gpr (saved.getD i .rax)
  frame : InScr p.base usedBytes original.mem s.mem
  keep : Keep coreRegs original s

theorem verifyingShape_ok {p : VerifyingInput} {s0 : State} (h : VerifyingPre p s0) :
    WP isa (.seq (.block SignVerify.verifyEntry) Checks.domainShape) s0 (VerifyingShapePost p s0 h.pLength h.qLength) := by
  refine WP.seq (WP.mono (verifyEntry_ok h.scratch rfl (by decide) h.stackRead h.stackSeparate
    h.digestPointer h.digestLength h.base) fun s1 he => ?_)
  have hinside : InScr p.base usedBytes s0.mem s1.mem := InScr.of_outside he.frame (by decide)
  have hkey := h.keySource.congrK hinside he.keep
  have hps : Src s1 p.base usedBytes (s0.gpr .rdi) p.components.p := source_take hkey
  have hqs : Src s1 p.base usedBytes (s0.gpr .rdi + BitVec.ofNat 64 p.pLen) p.components.q :=
    source_slice hkey (by rw [p.keyLength]; omega)
  have hp1 : 0 < p.components.p.length := by
    rw [p.components.pLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega
  have hq1 : 0 < p.components.q.length := by
    rw [p.components.qLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega
  have hp64 : p.components.p.length < 2 ^ 64 := by
    rw [p.components.pLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega
  have hq64 : p.components.q.length < 2 ^ 64 := by
    rw [p.components.qLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega
  refine WP.mono (domainShape_ok (h.scratch.congr he.keep.2.2) he.base (by decide) he.p
    (by rw [he.q, h.pLength]) (by rw [he.pLen, h.pLength, p.components.pLength])
    (by rw [he.qLen, h.qLength, p.components.qLength]) hps hqs hp1 hp64 hq1 hq64 rfl rfl
    p.digestBound he.digestLen) fun s2 ⟨hprefix, hmask, hbranch, hf, hk⟩ => ?_
  have hall := he.keep.trans hk
  have hft : InScr p.base usedBytes s1.mem s2.mem := by
    apply InScr.of_frm hf
    intro range hr
    simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide
  exact ⟨h.scratch.congr hall.2.2, (hk.gpr (by decide)).trans he.base,
    he.shapeFields hf hprefix hmask, hbranch,
    fun i hi => (shape_saved hf hi).trans (he.saved i hi), hinside.trans hft,
    hall.mono (by decide)⟩

end VG.Proof.Dsa.X86_64
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/VerifyingOperands.lean`, which only this module imported.
section

/-! # Packed verification operands after workspace initialization -/

section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem verifyingOperands {p : VerifyingInput} {original s : State}
    {hp : original.gpr .rdx = BitVec.ofNat 64 p.pLen}
    {hq : original.gpr .rcx = BitVec.ofNat 64 p.qLen} {pi qi : BitVec 64}
    (h : Ready ((p.layout original hp hq).withInverses pi qi) s)
    (hkey : Src s p.base usedBytes (original.gpr .rdi) p.key)
    (hsig : Src s p.base usedBytes (original.gpr .r8) p.signature)
    (hdigest : Src s p.base usedBytes p.digestPointer p.digest) :
    VerificationOperands ((p.layout original hp hq).withInverses pi qi) p.values p.components.q s := by
  let L := (p.layout original hp hq).withInverses pi qi
  have hqlen : p.components.q.length = p.qLen := p.components.qLength
  have hglen : p.components.g.length = p.pLen := p.components.gLength
  have hylen : p.components.y.length = p.pLen := p.components.yLength
  have hrlen : (p.signature.take p.qLen).length = p.qLen := by
    simp only [List.length_take, p.signatureLength]; omega
  have hslen : (p.signature.drop p.qLen).length = p.qLen := by
    simp only [List.length_drop, p.signatureLength]; omega
  have qptr : L.fields .q = original.gpr .rdi + BitVec.ofNat 64 p.pLen := by
    change original.gpr .rdi + original.gpr .rdx = _
    rw [hp]
  have gptr : L.fields .g = original.gpr .rdi + BitVec.ofNat 64 (p.pLen + p.qLen) := by
    change original.gpr .rdi + original.gpr .rdx + original.gpr .rcx = _
    rw [hp, hq, Offset.add_add]
  have yptr : L.fields .y = original.gpr .rdi + BitVec.ofNat 64 (2 * p.pLen + p.qLen) := by
    change original.gpr .rdi + original.gpr .rdx + original.gpr .rcx + original.gpr .rdx = _
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
    h.inputOperand .q .qLen (by decide) (by decide) hqsrc (by rw [hqlen]; exact hqfield),
    h.inputOperand .signature .qLen (by decide) (by decide) (source_take hsig)
      (by change L.fields .qLen = BitVec.ofNat 64 (p.signature.take p.qLen).length; rw [hrlen]; exact hqfield),
    ?_,
    h.inputOperand .digest .digestPrefixLen (by decide) (by decide) (source_take hdigest) ?_,
    hglen, hylen, hqlen, hrlen, hslen, ?_, rfl⟩
  · refine ⟨(h.fields .qLen (by decide)).trans ?_, ?_⟩
    · change L.fields .qLen = BitVec.ofNat 64 (p.signature.drop p.qLen).length
      rw [hslen]; exact hqfield
    · simp only [Core.signatureS, pointerValue, h.fields .signature (by decide), h.fields .qLen (by decide)]
      change Src s p.base usedBytes (original.gpr .r8 + original.gpr .rcx) (p.signature.drop p.qLen)
      rw [hq]
      have hh := source_slice (offset := p.qLen) (len := p.qLen) hsig (by rw [p.signatureLength]; omega)
      rw [List.take_of_length_le (Nat.le_of_eq hslen)] at hh
      exact hh
  · change BitVec.ofNat 64 p.prefixLength = BitVec.ofNat 64 (p.digest.take _).length
    rw [List.length_take, Nat.min_comm]
  · change (p.digest.take _).length < 2 ^ 64
    simp only [List.length_take]
    exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) p.digestBound

end VG.Proof.Dsa.X86_64
end

end

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
