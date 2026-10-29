module

public import VerifiedGarbage.Proof.Dsa.X86_64.SigningInput
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-! # Argument capture and public-domain validation for a complete signing attempt -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure SigningShapePost (p : SigningInput) (original : State)
    (hp : original.gpr .r8 = BitVec.ofNat 64 p.pLen) (s : State) : Prop where
  scratch : Scr s p.base usedBytes
  rdi : s.gpr .rdi = p.base
  fields : ∀ f, word s.mem p.base f.offset = (p.layout original hp).fields f
  branch : s.zf = some (!p.accepted)
  saved : ∀ i < 6, word s.mem p.base (8 * i) = original.gpr (saved.getD i .rax)
  frame : InScr p.base usedBytes original.mem s.mem
  keep : Keep coreRegs original s

theorem shape_saved {s t : State} {B : Addr} (hf : Frm B shapeRanges s.mem t.mem) {i : Nat} (hi : i < 6) :
    word t.mem B (8 * i) = word s.mem B (8 * i) := by
  apply hf.word_eq _ (by omega)
  intro range hr
  simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> left <;> omega

theorem signingShape_ok {p : SigningInput} {s0 : State} (h : SigningPre p s0) :
    WP isa (.seq (.block SignVerify.signEntry) Checks.domainShape) s0 (SigningShapePost p s0 h.pLength) := by
  refine WP.seq (WP.mono (signEntry_ok h.scratch rfl (by decide) h.stackRead h.stackSeparate
    h.qLength h.digestPointer h.digestLength h.base) fun s1 he => ?_)
  have hinside : InScr p.base usedBytes s0.mem s1.mem := InScr.of_outside he.frame (by decide)
  have hkey := h.keySource.congrK hinside he.keep
  have hps : Src s1 p.base usedBytes (s0.gpr .rdx) p.components.p := source_take hkey
  have hqs : Src s1 p.base usedBytes (s0.gpr .rdx + BitVec.ofNat 64 p.pLen) p.components.q :=
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
    (by rw [he.qLen, p.components.qLength]) hps hqs hp1 hp64 hq1 hq64 rfl rfl
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
