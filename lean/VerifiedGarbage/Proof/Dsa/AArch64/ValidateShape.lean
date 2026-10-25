module

public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingShape
import VerifiedGarbage.Proof.Dsa.AArch64.ValidateEntry
public import VerifiedGarbage.Impl.Dsa.AArch64.Prevalidated
public import VerifiedGarbage.Proof.Dsa.AArch64.InitializedFields
public import VerifiedGarbage.Spec.Dsa

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
    source_slice hkey (by rw [p.keyLength]; omega)
  have hp1 : 0 < p.components.p.length := by
    rw [p.components.pLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega
  have hq1 : 0 < p.components.q.length := by
    rw [p.components.qLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega
  have hp64 : p.components.p.length < 2 ^ 64 := by
    rw [p.components.pLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega
  have hq64 : p.components.q.length < 2 ^ 64 := by
    rw [p.components.qLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega
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
