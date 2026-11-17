module

import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Spec.Dsa.Prevalidated
import VerifiedGarbage.Proof.Dsa.AArch64.AcceptedSpec
import VerifiedGarbage.Proof.Dsa.AArch64.Result
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.SizeBounds
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingInitialize
import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.Dsa.AArch64.ValidateEntry
public import VerifiedGarbage.Impl.Dsa.AArch64.Prevalidated
public import VerifiedGarbage.Proof.Dsa.AArch64.InitializedFields
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Proof.Dsa.AArch64.InitializedLayout
public import VerifiedGarbage.Impl.Dsa.AArch64.Workspace
public import VerifiedGarbage.Proof.Dsa.AArch64.Execution
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingInput
import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceReady
import VerifiedGarbage.Proof.Dsa.AArch64.SigningOperands
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Dsa.AArch64.ValidateBody`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.ValidateInitialize`, which this module and modules that import it used -/

section

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

end

end

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

end

end

/-! # Functional correctness of the complete separate DSA public-key validator -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem validatingMain_ok (M : Mont) {p : VerifyingInput} {s0 : State} (h : ValidatingPre p s0) :
    WP isa (Prevalidated.validate M.mm) s0 (ValidatingPost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (validatingShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => ?_) (fun h => Bool.noConfusion h)
    · change some (s.gpr .x3 == (0#64)) = some true
      simp only [hs.branch, ha, Bool.not_false]
    · have hp := shapeAccepted_false ha (Spec.Dsa.decodeBE p.components.g)
      change ¬ Spec.Dsa.parametersValid (Spec.Dsa.publicKeyBytes p.pLen p.qLen p.key).params at hp
      have hv : Spec.Dsa.validatePublicKeyBytes p.pLen p.qLen p.key = false := by
        simp only [Spec.Dsa.validatePublicKeyBytes, p.lengths, decide_true, Bool.not_true,
          p.keyLength, bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
        simp only [hp, decide_false, Bool.false_and]
      refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 0 ∧ t.mem = s.mem)
        (by brun) rfl rfl rfl) fun t ⟨⟨hret, hmem⟩, hk⟩ => ?_
      exact ⟨by rw [hv]; exact hret, by rw [hmem]; exact hs.frame,
        (hs.keep.trans hk).mono (by decide)⟩
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => ?_)
    · change some (s.gpr .x3 == (0#64)) = some false
      simp only [hs.branch, ha, Bool.not_true]
    · refine WP.seq (WP.mono (validatingInitialize_ok h hs ha) fun t ht => ?_)
      exact validatingBody_ok M h ht ha

end VG.Proof.Dsa.AArch64
