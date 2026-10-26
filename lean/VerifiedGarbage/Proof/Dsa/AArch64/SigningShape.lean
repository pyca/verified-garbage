module

public import VerifiedGarbage.Proof.Dsa.AArch64.SigningInput
import Mathlib.Algebra.Group.Nat.Defs

/-! # Argument capture and public-domain validation for a complete signing attempt -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure SigningShapePost (p : SigningInput) (original : State)
    (hp : original.gpr .x4 = BitVec.ofNat 64 p.pLen) (s : State) : Prop where
  scratch : Scr s p.base usedBytes
  x0 : s.gpr .x0 = p.base
  fields : ∀ f, word s.mem p.base f.offset = (p.layout original hp).fields f
  branch : (s.gpr .x3 == (0#64)) = !p.accepted
  frame : InScr p.base usedBytes original.mem s.mem
  keep : Keep coreRegs original s

theorem signingShape_ok {p : SigningInput} {s0 : State} (h : SigningPre p s0) :
    WP isa (.seq (.block SignVerify.signEntry) Checks.domainShape) s0 (SigningShapePost p s0 h.pLength) := by
  refine WP.seq (WP.mono (signEntry_ok h.scratch rfl (by decide) h.stackRead h.stackSeparate
    h.qLength h.digestPointer h.digestLength h.base) fun s1 he => ?_)
  have hinside : InScr p.base usedBytes s0.mem s1.mem := InScr.of_outside he.frame (by decide)
  have hkey := h.keySource.congrK hinside he.keep
  have hps : Src s1 p.base usedBytes (s0.gpr .x2) p.components.p := source_take hkey
  have hqs : Src s1 p.base usedBytes (s0.gpr .x2 + BitVec.ofNat 64 p.pLen) p.components.q :=
    source_slice hkey (by rw [p.keyLength]; omega)
  have hp1 : 0 < p.components.p.length := by
    rw [p.components.pLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega
  have hq1 : 0 < p.components.q.length := by
    rw [p.components.qLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega
  have hp64 : p.components.p.length < 2 ^ 64 := by
    rw [p.components.pLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega
  have hq64 : p.components.q.length < 2 ^ 64 := by
    rw [p.components.qLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega
  refine WP.mono (domainShape_ok (h.scratch.congr he.keep.wr) he.base (by decide) he.p
    (by rw [he.q, h.pLength]) (by rw [he.pLen, h.pLength, p.components.pLength])
    (by rw [he.qLen, p.components.qLength]) hps hqs hp1 hp64 hq1 hq64 rfl rfl
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
