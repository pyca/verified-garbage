module

public import VerifiedGarbage.Proof.Dsa.AArch64.Parameters
public import VerifiedGarbage.Proof.Dsa.AArch64.DomainShapeCT
public import VerifiedGarbage.Proof.Dsa.AArch64.PublicKeyCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.Parameters
meta import VerifiedGarbage.Proof.Dsa.AArch64.DomainShapeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicKeyCT
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
public import VerifiedGarbage.Proof.Dsa.AArch64.ShapeCTState
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Dsa.AArch64.ShapeCTState
public import VerifiedGarbage.Proof.Dsa.AArch64.InitializedLayout
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyBody
import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceReady
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingInput
import VerifiedGarbage.Proof.Dsa.AArch64.SigningOperands
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Dsa.AArch64.InitializedLayout
meta import VerifiedGarbage.Proof.Dsa.AArch64.VerifyBody
meta import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceReady
meta import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingInput
meta import VerifiedGarbage.Proof.Dsa.AArch64.SigningOperands
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Dsa.AArch64.VerifyingCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.VerifyingInitialize`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.VerifyingShape`, which this module and modules that import it used -/

section

/-! # Argument capture and public-domain validation for a complete verifying attempt -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure VerifyingShapePost (p : VerifyingInput) (original : State)
    (hp : original.gpr .x2 = BitVec.ofNat 64 p.pLen)
    (hq : original.gpr .x3 = BitVec.ofNat 64 p.qLen) (s : State) : Prop where
  scratch : Scr s p.base usedBytes
  x0 : s.gpr .x0 = p.base
  fields : ∀ f, word s.mem p.base f.offset = (p.layout original hp hq).fields f
  branch : (s.gpr .x3 == (0#64)) = !p.accepted
  frame : InScr p.base usedBytes original.mem s.mem
  keep : Keep coreRegs original s

theorem verifyingShape_ok {p : VerifyingInput} {s0 : State} (h : VerifyingPre p s0) :
    WP isa (.seq (.block SignVerify.verifyEntry) Checks.domainShape) s0 (VerifyingShapePost p s0 h.pLength h.qLength) := by
  refine WP.seq (WP.mono (verifyEntry_ok h.scratch rfl (by decide) h.stackRead
    h.digestPointer h.digestLength h.base) fun s1 he => ?_)
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
  refine WP.mono (domainShape_ok (h.scratch.congr he.keep.wr) he.base (by decide) he.p
    (by rw [he.q, h.pLength]) (by rw [he.pLen, h.pLength, p.components.pLength])
    (by rw [he.qLen, h.qLength, p.components.qLength]) hps hqs hp1 hp64 hq1 hq64 rfl rfl
    p.digestBound he.digestLen) fun s2 ⟨hprefix, hmask, hbranch, hf, hk⟩ => ?_
  have hall := he.keep.trans hk
  have hft : InScr p.base usedBytes s1.mem s2.mem := by
    apply InScr.of_frm hf
    intro range hr
    simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide
  exact ⟨h.scratch.congr hall.wr, (hk.gpr .x0 (by decide)).trans he.base,
    he.shapeFields hf hprefix hmask, hbranch,
    hinside.trans hft,
    hall.mono (by decide)⟩

end VG.Proof.Dsa.AArch64

end

end

/-! # Establishing all verifying operands after public domain acceptance -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/VerifyingOperands.lean`, which only this module imported.
section

/-! # Packed verification operands after workspace initialization -/

section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem verifyingOperands {p : VerifyingInput} {original s : State}
    {hp : original.gpr .x2 = BitVec.ofNat 64 p.pLen}
    {hq : original.gpr .x3 = BitVec.ofNat 64 p.qLen} {pi qi : BitVec 64}
    (h : Ready ((p.layout original hp hq).withInverses pi qi) s)
    (hkey : Src s p.base usedBytes (original.gpr .x0) p.key)
    (hsig : Src s p.base usedBytes (original.gpr .x4) p.signature)
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
      change Src s p.base usedBytes (original.gpr .x4 + original.gpr .x3) (p.signature.drop p.qLen)
      rw [hq]
      have hh := source_slice (offset := p.qLen) (len := p.qLen) hsig (by rw [p.signatureLength]; omega)
      rw [List.take_of_length_le (Nat.le_of_eq hslen)] at hh
      exact hh
  · change BitVec.ofNat 64 p.prefixLength = BitVec.ofNat 64 (p.digest.take _).length
    rw [List.length_take, Nat.min_comm]
  · change (p.digest.take _).length < 2 ^ 64
    simp only [List.length_take]
    exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) p.digestBound

end VG.Proof.Dsa.AArch64
end

end

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem VerifyingInput.shapeFacts {p : VerifyingInput} (ha : p.accepted = true) :
    Spec.Dsa.supportedSizes (Spec.Dsa.bitLength (Spec.Dsa.decodeBE p.components.p))
      (Spec.Dsa.bitLength (Spec.Dsa.decodeBE p.components.q)) ∧
    Spec.Dsa.decodeBE p.components.p % 2 = 1 ∧ Spec.Dsa.decodeBE p.components.q % 2 = 1 := by
  rw [VerifyingInput.accepted, shapeAccepted_spec] at ha
  exact of_decide_eq_true ha

def VerifyingInitialized (p : VerifyingInput) (original : State)
    (hp : original.gpr .x2 = BitVec.ofNat 64 p.pLen)
    (hq : original.gpr .x3 = BitVec.ofNat 64 p.qLen) (s : State) : Prop :=
  ∃ pi qi,
    Ready ((p.layout original hp hq).withInverses pi qi) s ∧
    VerificationOperands ((p.layout original hp hq).withInverses pi qi) p.values p.components.q s ∧
    word s.mem p.base Field.mask.offset = mask true ∧
    InScr p.base usedBytes original.mem s.mem ∧ Keep coreRegs original s

theorem verifyingInitialize_ok {p : VerifyingInput} {original s : State} (h : VerifyingPre p original)
    (hs : VerifyingShapePost p original h.pLength h.qLength s) (ha : p.accepted = true) :
    WP isa SignVerify.workspaces s (VerifyingInitialized p original h.pLength h.qLength) := by
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
  refine ⟨pi, qi, hr, verifyingOperands hr (h.keySource.congrK hfull hkeep)
    (h.signatureSource.congrK hfull hkeep) (h.digestSource.congrK hfull hkeep), ?_, hfull, hkeep.mono (by decide)⟩
  · exact hm.trans ((hs.fields .mask).trans (congrArg mask ha))

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.VerifyingReadyCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.VerifyingPublic`, which this module and modules that import it used -/

section

/-! # Public observations used to relate two complete verification calls

The reference call supplies public lengths, addresses and domain bytes. The
relation does not equate signatures, digests or scratch contents.
-/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure VerifyingCall where
  input : VerifyingInput
  original : State
  pre : VerifyingPre input original

abbrev VerifyingCall.layout (c : VerifyingCall) : ExecutionLayout := c.input.layout c.original c.pre.pLength c.pre.qLength

structure VerifyingAgrees (reference c : VerifyingCall) : Prop where
  layout : c.layout = reference.layout
  pBytes : c.input.components.p = reference.input.components.p
  qBytes : c.input.components.q = reference.input.components.q
  digestLength : c.input.digest.length = reference.input.digest.length
  stack : c.original.sp = reference.original.sp

def VerifyingStart (reference : VerifyingCall) (s : State) : Prop :=
  ∃ c : VerifyingCall, VerifyingAgrees reference c ∧ c.original = s

def VerifyingEntered (reference : VerifyingCall) (s : State) : Prop :=
  ∃ c : VerifyingCall, VerifyingAgrees reference c ∧
    VerifyEntryPost c.original c.input.base c.input.digestPointer
      (BitVec.ofNat 64 c.input.digest.length) s

def VerifyingShaped (reference : VerifyingCall) (s : State) : Prop :=
  ∃ c : VerifyingCall, VerifyingAgrees reference c ∧ VerifyingShapePost c.input c.original c.pre.pLength c.pre.qLength s

def VerifyingReady (reference : VerifyingCall) (s : State) : Prop :=
  ∃ c : VerifyingCall, VerifyingAgrees reference c ∧ VerifyingInitialized c.input c.original c.pre.pLength c.pre.qLength s

def VerifyingCall.shape (c : VerifyingCall) : ShapePublic where
  base := c.layout.base
  extent := usedBytes
  pPointer := c.layout.fields .p
  qPointer := c.layout.fields .q
  pBytes := c.input.components.p
  qBytes := c.input.components.q
  digestLen := c.input.digest.length
  extentBound := by decide
  pPositive := by rw [c.input.components.pLength]; have := c.layout.widths; change 0 < c.layout.pLen; omega_using [this]
  qPositive := by rw [c.input.components.qLength]; exact c.layout.widths.1
  pBound := by rw [c.input.components.pLength]; have := c.layout.widths; change c.layout.pLen < 2 ^ 64; omega_using [this]
  qBound := by rw [c.input.components.qLength]; have := c.layout.widths; change c.layout.qLen < 2 ^ 64; omega_using [this]
  digestBound := c.input.digestBound

theorem VerifyingAgrees.shape {reference c : VerifyingCall} (h : VerifyingAgrees reference c) :
    c.shape = reference.shape := by
  unfold VerifyingCall.shape
  congr 1
  · exact congrArg ExecutionLayout.base h.layout
  · exact congrArg (fun L => L.fields .p) h.layout
  · exact congrArg (fun L => L.fields .q) h.layout
  · exact h.pBytes
  · exact h.qBytes
  · exact h.digestLength

theorem VerifyingAgrees.accepted {reference c : VerifyingCall} (h : VerifyingAgrees reference c) :
    c.input.accepted = reference.input.accepted := by
  unfold VerifyingInput.accepted
  congr 1
  · exact h.pBytes
  · exact h.qBytes

theorem VerifyingEntered.context {reference : VerifyingCall} {s : State} (h : VerifyingEntered reference s) :
    ShapeContext reference.shape s := by
  obtain ⟨c, ha, he⟩ := h
  rw [← ha.shape]
  have hf : InScr c.input.base usedBytes c.original.mem s.mem := InScr.of_outside he.frame (by decide)
  have hkey := c.pre.keySource.congrK hf he.keep
  refine ⟨c.pre.scratch.congr he.keep.wr, he.base, he.p, he.q, ?_, ?_, he.digestLen,
    source_take hkey, ?_⟩
  · change word s.mem c.input.base Field.pLen.offset = BitVec.ofNat 64 c.input.components.p.length
    rw [c.input.components.pLength]
    exact he.pLen.trans c.pre.pLength
  · change word s.mem c.input.base Field.qLen.offset = BitVec.ofNat 64 c.input.components.q.length
    rw [c.input.components.qLength]
    exact he.qLen.trans c.pre.qLength
  · change Src s c.input.base usedBytes (c.original.gpr .x0 + c.original.gpr .x2) c.input.components.q
    rw [c.pre.pLength]
    exact source_slice hkey (by rw [c.input.keyLength]; omega_using [])

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.VerifyingShapeCT`, which this module and modules that import it used -/

section

/-! # Constant time of verifying argument capture and domain validation -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem verifyingEntered_ct : RelCT isa (Two VerifyingStart) (.block SignVerify.verifyEntry) (Two VerifyingEntered) := by
  refine two_post (two_map (fun c : VerifyingCall => (c.layout.base, c.original.sp)) ?_ verifyEntry_ct) ?_
  · intro reference s ⟨c, ha, hs⟩
    subst s
    have hb : c.input.base = reference.layout.base := congrArg ExecutionLayout.base ha.layout
    refine ⟨ha.stack, ?_, ?_⟩
    · rw [← ha.stack, ← hb]
      exact c.pre.base
    · rw [← ha.stack]
      exact by simpa only [Nat.mul_zero, off_zero] using c.pre.stackRead
  · intro reference s ⟨c, ha, hs⟩
    subst s
    exact WP.mono (verifyEntry_ok c.pre.scratch rfl (by decide) c.pre.stackRead
      c.pre.digestPointer c.pre.digestLength c.pre.base) fun t ht => ⟨c, ha, ht⟩

theorem verifyingShape_ct : RelCT isa (Two VerifyingStart)
    (.seq (.block SignVerify.verifyEntry) Checks.domainShape) (Two VerifyingShaped) := by
  refine two_post (RelCT.seq verifyingEntered_ct
    (two_map VerifyingCall.shape (fun _ _ h => h.context) domainShape_ct)) ?_
  intro reference s ⟨c, ha, hs⟩
  subst s
  exact WP.mono (verifyingShape_ok c.pre) fun t ht => ⟨c, ha, ht⟩

def VerifyingCall.initialization (c : VerifyingCall) (ha : c.input.accepted = true) : InitializationPublic where
  layout := c.layout
  pBytes := c.input.components.p
  qBytes := c.input.components.q
  pLength := c.input.components.pLength
  qLength := c.input.components.qLength
  pValue := rfl
  qValue := rfl
  pOdd := (c.input.shapeFacts ha).2.1
  qOdd := (c.input.shapeFacts ha).2.2

theorem VerifyingShaped.initialization {reference : VerifyingCall} {s : State}
    (h : VerifyingShaped reference s) (ha : reference.input.accepted = true) :
    InitializationPre (reference.initialization ha) s := by
  obtain ⟨c, hag, hs⟩ := h
  have hf : ∀ f, word s.mem c.layout.base f.offset = c.layout.fields f := hs.fields
  have hr : s.gpr .x0 = c.layout.base := hs.x0
  have hscr : Scr s c.layout.base usedBytes := hs.scratch
  have hkey := c.pre.keySource.congrK hs.frame hs.keep
  have hps : Src s c.layout.base usedBytes (c.layout.fields .p) c.input.components.p := source_take hkey
  have hqs : Src s c.layout.base usedBytes (c.layout.fields .q) c.input.components.q := by
    change Src s c.input.base usedBytes (c.original.gpr .x0 + c.original.gpr .x2) c.input.components.q
    rw [c.pre.pLength]
    exact source_slice hkey (by rw [c.input.keyLength]; omega_using [])
  rw [hag.layout] at hf hr hscr hps hqs
  rw [hag.pBytes] at hps
  rw [hag.qBytes] at hqs
  exact ⟨hscr, hr, hf, hps, hqs⟩

abbrev AcceptedVerifyingCall := {c : VerifyingCall // c.input.accepted = true}

theorem verifyingWorkspaces_ct : RelCT isa (Two (fun c : AcceptedVerifyingCall => VerifyingShaped c.val))
    SignVerify.workspaces (Two (fun c : AcceptedVerifyingCall => VerifyingReady c.val)) := by
  refine two_post ((two_map (fun c : AcceptedVerifyingCall => c.val.initialization c.property)
    (fun c _ h => h.initialization c.property) initialization_ct).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
  intro reference s ⟨c, ha, hs⟩
  have hac : c.input.accepted = true := ha.accepted.trans reference.property
  exact WP.mono (verifyingInitialize_ok c.pre hs hac) fun t ht => ⟨c, ha, ht⟩

end VG.Proof.Dsa.AArch64

end

end

/-! # The public schedule after independent verifying-workspace initialization -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def VerifyingCall.schedule (c : VerifyingCall) (ha : c.input.accepted = true) (pi qi : BitVec 64) : SchedulePublic where
  layout := c.layout.withInverses pi qi
  digestLen := c.input.prefixLength
  pGreater := (VG.Proof.Dsa.supported_bounds (c.input.shapeFacts ha).1).1
  qGreater := (VG.Proof.Dsa.supported_bounds (c.input.shapeFacts ha).1).2.1
  pOdd := (c.input.shapeFacts ha).2.1
  qOdd := (c.input.shapeFacts ha).2.2
  pFits := by
    have h := VG.Proof.Dsa.decodeBE_lt c.input.components.p
    rw [c.input.components.pLength] at h
    exact Nat.le_of_lt h
  qFits := by
    have h := VG.Proof.Dsa.decodeBE_lt c.input.components.q
    rw [c.input.components.qLength] at h
    exact Nat.le_of_lt h
  digestBound := Nat.lt_of_le_of_lt (Nat.min_le_left _ _) c.input.digestBound

theorem VerifyingAgrees.prefixLength {reference c : VerifyingCall} (h : VerifyingAgrees reference c) :
    c.input.prefixLength = reference.input.prefixLength := by
  unfold VerifyingInput.prefixLength
  rw [h.digestLength, h.qBytes]

theorem VerifyingReady.body {reference : VerifyingCall} {s : State} (ha : reference.input.accepted = true)
    (h : VerifyingReady reference s) : ∃ pi qi, VerifyingBodyPre (reference.schedule ha pi qi) s := by
  obtain ⟨c, hag, pi, qi, hr, ho, hm, _, hk⟩ := h
  have hmask : word s.mem c.layout.base Field.mask.offset = mask true := hm
  change Ready (c.layout.withInverses pi qi) s at hr
  change VerificationOperands (c.layout.withInverses pi qi) c.input.values c.input.components.q s at ho
  rw [hag.layout] at hr ho hmask
  refine ⟨pi, qi, hr, ⟨c.input.values, c.input.components.q, ho, ?_⟩,
    ⟨true, hmask⟩⟩
  change (c.input.digest.take _).length = reference.input.prefixLength
  rw [List.length_take, Nat.min_comm]
  exact hag.prefixLength

theorem verifyingReady_related {s₁ s₂ : State}
    (h : Two (fun c : AcceptedVerifyingCall => VerifyingReady c.val) s₁ s₂) : Two VerifyingBodyPre s₁ s₂ := by
  obtain ⟨reference, h₁, h₂, hsp⟩ := h
  obtain ⟨pi₁, qi₁, h₁⟩ := h₁.body reference.property
  obtain ⟨pi₂, qi₂, h₂⟩ := h₂.body reference.property
  obtain ⟨rfl, rfl⟩ := readyInverses_eq h₁.1 h₂.1
    (reference.val.input.shapeFacts reference.property).2.1
    (reference.val.input.shapeFacts reference.property).2.2
  exact ⟨_, h₁, h₂, hsp⟩

end VG.Proof.Dsa.AArch64

end

end

/-! # Constant time of the complete verifying entry point -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem VerifyingShaped.branch {reference : VerifyingCall} {s : State} (h : VerifyingShaped reference s) :
    eval (.zero .x .x3) s = some (!reference.input.accepted) := by
  obtain ⟨c, ha, hs⟩ := h
  change some (s.gpr .x3 == (0#64)) = _
  rw [hs.branch, ha.accepted]

theorem VerifyingShaped.x0 {reference : VerifyingCall} {s : State} (h : VerifyingShaped reference s) :
    s.gpr .x0 = reference.layout.base := by
  obtain ⟨c, ha, hs⟩ := h
  exact hs.x0.trans (congrArg ExecutionLayout.base ha.layout)

theorem verifyFailure_ct : RelCT isa (Two (fun B : Addr => fun s => s.gpr .x0 = B))
    (.block [movi .x0 0])
    (fun _ _ => True) :=
  two_taint [.x0] (pins_of (fun B _ => B) (by
    intro B s h r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h)) (by taint_decide)

end VG.Proof.Dsa.AArch64

end

end

/-! # Constant time of the AArch64 DSA domain check

Every input is public: two calls with the same pointers, lengths and domain
bytes take the same path, whatever their scratch holds. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure ParametersCall where
  input : ParametersInput
  original : State
  pre : ParametersPre input original

abbrev ParametersCall.layout (c : ParametersCall) : ExecutionLayout :=
  c.input.layout c.original c.pre.pLength c.pre.qLength

structure ParametersAgrees (reference c : ParametersCall) : Prop where
  layout : c.layout = reference.layout
  params : c.input.params = reference.input.params

def ParametersStart (reference : ParametersCall) (s : State) : Prop :=
  ∃ c : ParametersCall, ParametersAgrees reference c ∧ c.original = s

def ParametersEntered (reference : ParametersCall) (s : State) : Prop :=
  ∃ c : ParametersCall, ParametersAgrees reference c ∧
    KeygenEntryPost c.original c.input.base (checkFieldValues c.original true) s

def ParametersShaped (reference : ParametersCall) (s : State) : Prop :=
  ∃ c : ParametersCall, ParametersAgrees reference c ∧
    ParametersShapePost c.input c.original c.pre.pLength c.pre.qLength s

def ParametersReady (reference : ParametersCall) (s : State) : Prop :=
  ∃ c : ParametersCall, ParametersAgrees reference c ∧
    ParametersInitialized c.input c.original c.pre.pLength c.pre.qLength s

theorem ParametersAgrees.pLen {reference c : ParametersCall} (h : ParametersAgrees reference c) :
    c.input.pLen = reference.input.pLen := congrArg ExecutionLayout.pLen h.layout

theorem ParametersAgrees.qLen {reference c : ParametersCall} (h : ParametersAgrees reference c) :
    c.input.qLen = reference.input.qLen := congrArg ExecutionLayout.qLen h.layout

theorem ParametersAgrees.pb {reference c : ParametersCall} (h : ParametersAgrees reference c) :
    c.input.pb = reference.input.pb := by
  rw [ParametersInput.pb, ParametersInput.pb, h.params, h.pLen]

theorem ParametersAgrees.qb {reference c : ParametersCall} (h : ParametersAgrees reference c) :
    c.input.qb = reference.input.qb := by
  rw [ParametersInput.qb, ParametersInput.qb, h.params, h.pLen, h.qLen]

theorem ParametersAgrees.accepted {reference c : ParametersCall} (h : ParametersAgrees reference c) :
    c.input.accepted = reference.input.accepted := by
  unfold ParametersInput.accepted
  congr 1
  · exact h.pb
  · exact h.qb

theorem checkEntry_ct : RelCT isa (Two (fun B : Addr => fun s => s.gpr .x4 = B))
    (.block Generate.checkEntry) (fun _ _ => True) :=
  two_taint [.x4] (pins_of (fun B _ => B) (by
    intro B s h r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h)) (by taint_decide)

theorem parametersEntered_ct : RelCT isa (Two ParametersStart) (.block Generate.checkEntry)
    (Two ParametersEntered) := by
  refine two_post (two_map (fun c : ParametersCall => c.layout.base) ?_ checkEntry_ct) ?_
  · intro reference s ⟨c, ha, hs⟩
    subst s
    exact c.pre.base.trans (congrArg ExecutionLayout.base ha.layout)
  · intro reference s ⟨c, ha, hs⟩
    subst s
    exact WP.mono (checkEntry_ok c.pre.scratch c.pre.base) fun t ht => ⟨c, ha, ht⟩

def ParametersCall.shape (c : ParametersCall) : ShapePublic where
  base := c.layout.base
  extent := usedBytes
  pPointer := c.layout.fields .p
  qPointer := c.layout.fields .q
  pBytes := c.input.pb
  qBytes := c.input.qb
  digestLen := 0
  extentBound := by decide
  pPositive := c.input.pPositive
  qPositive := c.input.qPositive
  pBound := by rw [c.input.pbLength]; have := c.layout.widths; change c.layout.pLen < 2 ^ 64; omega_using [this]
  qBound := by rw [c.input.qbLength]; have := c.layout.widths; change c.layout.qLen < 2 ^ 64; omega_using [this]
  digestBound := by decide

theorem ParametersAgrees.shape {reference c : ParametersCall} (h : ParametersAgrees reference c) :
    c.shape = reference.shape := by
  unfold ParametersCall.shape
  congr 1
  · exact congrArg ExecutionLayout.base h.layout
  · exact congrArg (fun L => L.fields .p) h.layout
  · exact congrArg (fun L => L.fields .q) h.layout
  · exact h.pb
  · exact h.qb

theorem ParametersEntered.context {reference : ParametersCall} {s : State} (h : ParametersEntered reference s) :
    ShapeContext reference.shape s := by
  obtain ⟨c, ha, he⟩ := h
  rw [← ha.shape]
  have hf : InScr c.input.base usedBytes c.original.mem s.mem := InScr.of_outside he.frame (by decide)
  obtain ⟨hps, hqs, _⟩ := c.pre.sources hf (he.keep.mono (by decide))
  refine ⟨c.pre.scratch.congr he.keep.wr, he.base, he.fields .p (by decide) (by decide),
    he.fields .q (by decide) (by decide), ?_, ?_, he.fields .digestLen (by decide) (by decide), hps, hqs⟩
  · change word s.mem c.input.base Field.pLen.offset = BitVec.ofNat 64 c.input.pb.length
    rw [c.input.pbLength]
    exact (he.fields .pLen (by decide) (by decide)).trans c.pre.pLength
  · change word s.mem c.input.base Field.qLen.offset = BitVec.ofNat 64 c.input.qb.length
    rw [c.input.qbLength]
    exact (he.fields .qLen (by decide) (by decide)).trans c.pre.qLength

theorem parametersShape_ct : RelCT isa (Two ParametersStart)
    (.seq (.block Generate.checkEntry) Checks.domainShape) (Two ParametersShaped) := by
  refine two_post (RelCT.seq parametersEntered_ct
    (two_map ParametersCall.shape (fun _ _ h => h.context) domainShape_ct)) ?_
  intro reference s ⟨c, ha, hs⟩
  subst s
  exact WP.mono (parametersShape_ok c.pre) fun t ht => ⟨c, ha, ht⟩

theorem ParametersShaped.branch {reference : ParametersCall} {s : State} (h : ParametersShaped reference s) :
    eval (.zero .x .x3) s = some (!reference.input.accepted) := by
  obtain ⟨c, ha, hs⟩ := h
  change some (s.gpr .x3 == (0#64)) = _
  rw [hs.branch, ha.accepted]

theorem ParametersShaped.x0 {reference : ParametersCall} {s : State} (h : ParametersShaped reference s) :
    s.gpr .x0 = reference.layout.base := by
  obtain ⟨c, ha, hs⟩ := h
  exact hs.x0.trans (congrArg ExecutionLayout.base ha.layout)

def ParametersCall.initialization (c : ParametersCall) (ha : c.input.accepted = true) : InitializationPublic where
  layout := c.layout
  pBytes := c.input.pb
  qBytes := c.input.qb
  pLength := c.input.pbLength
  qLength := c.input.qbLength
  pValue := rfl
  qValue := rfl
  pOdd := (c.input.shapeFacts ha).2.1
  qOdd := (c.input.shapeFacts ha).2.2

theorem ParametersShaped.initialization {reference : ParametersCall} {s : State}
    (h : ParametersShaped reference s) (ha : reference.input.accepted = true) :
    InitializationPre (reference.initialization ha) s := by
  obtain ⟨c, hag, hs⟩ := h
  have hf : ∀ f, word s.mem c.layout.base f.offset = c.layout.fields f := hs.fields
  have hr : s.gpr .x0 = c.layout.base := hs.x0
  have hscr : Scr s c.layout.base usedBytes := hs.scratch
  obtain ⟨hps, hqs, _⟩ := c.pre.sources hs.frame hs.keep
  have hps' : Src s c.layout.base usedBytes (c.layout.fields .p) c.input.pb := hps
  have hqs' : Src s c.layout.base usedBytes (c.layout.fields .q) c.input.qb := hqs
  rw [hag.layout] at hf hr hscr hps' hqs'
  rw [hag.pb] at hps'
  rw [hag.qb] at hqs'
  exact ⟨hscr, hr, hf, hps', hqs'⟩

abbrev AcceptedParametersCall := {c : ParametersCall // c.input.accepted = true}

theorem parametersWorkspaces_ct : RelCT isa (Two (fun c : AcceptedParametersCall => ParametersShaped c.val))
    SignVerify.workspaces (Two (fun c : AcceptedParametersCall => ParametersReady c.val)) := by
  refine two_post ((two_map (fun c : AcceptedParametersCall => c.val.initialization c.property)
    (fun c _ h => h.initialization c.property) initialization_ct).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
  intro reference s ⟨c, ha, hs⟩
  have hac : c.input.accepted = true := ha.accepted.trans reference.property
  exact WP.mono (parametersInitialize_ok c.pre hs hac) fun t ht => ⟨c, ha, ht⟩

/-- The domain's operands, as the schedule reads them. -/
def parametersInputs (p : SchedulePublic) : List (Operand × Nat) :=
  [(Core.publicValue, p.layout.pLen), (⟨.input .q, .qLen⟩, p.layout.qLen), (Core.generator, p.layout.pLen)]

theorem parametersInputs_stable (p : SchedulePublic) (a : Operand × Nat)
    (ha : a ∈ parametersInputs p) : a.1.length ≠ .mask ∧ stablePointer a.1.pointer := by
  simp only [parametersInputs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · simp [Core.publicValue, stablePointer]
  · change Field.qLen ≠ .mask ∧ Field.q ≠ .mask
    decide
  · simp [Core.generator, stablePointer]

def ParametersCall.schedule (c : ParametersCall) (ha : c.input.accepted = true) (pi qi : BitVec 64) : SchedulePublic where
  layout := c.layout.withInverses pi qi
  digestLen := 0
  pGreater := (VG.Proof.Dsa.supported_bounds (c.input.shapeFacts ha).1).1
  qGreater := (VG.Proof.Dsa.supported_bounds (c.input.shapeFacts ha).1).2.1
  pOdd := (c.input.shapeFacts ha).2.1
  qOdd := (c.input.shapeFacts ha).2.2
  pFits := by
    have h := VG.Proof.Dsa.decodeBE_lt c.input.pb
    rw [c.input.pbLength] at h
    exact Nat.le_of_lt h
  qFits := by
    have h := VG.Proof.Dsa.decodeBE_lt c.input.qb
    rw [c.input.qbLength] at h
    exact Nat.le_of_lt h
  digestBound := by decide

theorem ParametersReady.body {reference : ParametersCall} {s : State} (ha : reference.input.accepted = true)
    (h : ParametersReady reference s) : ∃ pi qi, PublicKeyPre parametersInputs (reference.schedule ha pi qi) s := by
  obtain ⟨c, hag, pi, qi, hr, ho, hm, _, _⟩ := h
  have hmask : word s.mem c.layout.base Field.mask.offset = mask true := hm
  change Ready (c.layout.withInverses pi qi) s at hr
  change ParametersOperands (c.layout.withInverses pi qi) c.input s at ho
  rw [hag.layout] at hr ho hmask
  have hgl : c.input.gb.length = reference.layout.pLen := c.input.gbLength.trans hag.pLen
  have hql : c.input.qb.length = reference.layout.qLen := c.input.qbLength.trans hag.qLen
  refine ⟨pi, qi, ⟨hr, ?_, ⟨true, hmask⟩⟩, c.input.qb, ho.subgroup, hql, ?_⟩
  · intro a ha
    simp only [parametersInputs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨_, ho.publicValue, hgl⟩
    · exact ⟨_, ho.subgroup, hql⟩
    · exact ⟨_, ho.generator, hgl⟩
  · change Spec.Dsa.decodeBE c.input.qb = Spec.Dsa.decodeBE reference.input.qb
    rw [hag.qb]

theorem parametersReady_related {s₁ s₂ : State}
    (h : Two (fun c : AcceptedParametersCall => ParametersReady c.val) s₁ s₂) :
    Two (PublicKeyPre parametersInputs) s₁ s₂ := by
  obtain ⟨reference, h₁, h₂, hsp⟩ := h
  obtain ⟨pi₁, qi₁, h₁⟩ := h₁.body reference.property
  obtain ⟨pi₂, qi₂, h₂⟩ := h₂.body reference.property
  obtain ⟨rfl, rfl⟩ := readyInverses_eq h₁.1.1 h₂.1.1
    (reference.val.input.shapeFacts reference.property).2.1
    (reference.val.input.shapeFacts reference.property).2.2
  exact ⟨_, h₁, h₂, hsp⟩

theorem parametersBody_ct (M : Mont) : RelCT isa (Two (PublicKeyPre parametersInputs))
    (seqs [Checks.signingKey M.mm, .block SignVerify.result]) (fun _ _ => True) := by
  have h1 := signingKey_ct M parametersInputs (fun p => parametersInputs_stable p)
    (by intro p; simp [parametersInputs]) (by intro p; simp [parametersInputs])
    (by intro p; simp [parametersInputs])
  unfold seqs
  refine RelCT.seq h1 ?_
  exact two_map (fun p => p.layout.base) (fun _ _ h => h.1.parent.x0) result_ct

theorem parametersSuccess_ct (M : Mont) :
    RelCT isa (Two (fun c : AcceptedParametersCall => ParametersShaped c.val))
      (seqs [SignVerify.workspaces, Checks.signingKey M.mm, .block SignVerify.result])
      (fun _ _ => True) := by
  refine RelCT.seq parametersWorkspaces_ct ?_
  exact (parametersBody_ct M).mono (fun _ _ h => parametersReady_related h) (fun _ _ h => h)

theorem parametersMain_ct (M : Mont) :
    RelCT isa (Two ParametersStart) (Generate.checkParameters M.mm) (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq parametersShape_ct (RelCT.ite ?_ ?_ ?_)
  · rintro s₁ s₂ ⟨reference, h₁, h₂, hsp⟩
    exact h₁.branch.trans h₂.branch.symm
  · exact ((two_map (fun c : ParametersCall => c.layout.base) (fun _ _ h => h.x0) verifyFailure_ct).mono
      (fun _ _ h => h.1) (fun _ _ h => h))
  · refine (parametersSuccess_ct M).mono ?_ (fun _ _ h => h)
    rintro s₁ s₂ ⟨⟨reference, h₁, h₂, hsp⟩, hb⟩
    have ha : reference.input.accepted = true := by
      change eval (.zero .x .x3) s₁ = some false at hb
      rw [h₁.branch] at hb
      cases h : reference.input.accepted <;> simp_all
    exact ⟨⟨reference, ha⟩, h₁, h₂, hsp⟩

end VG.Proof.Dsa.AArch64
