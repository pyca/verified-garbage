module

public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Work
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH private-key validation on x86-64: scalar flags -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPrivate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The steps may alter scratch and working registers, preserving the saved ABI values. -/
def StepPost (p : KpP) (s : State) (P : State → Prop) (t : State) : Prop :=
  P t ∧ InScr p.B p.Z s.mem t.mem ∧
    (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ Keep (.rdi :: mmRegs) s t

theorem StepPost.trans {p : KpP} {s u t : State} {P Q : State → Prop}
    (h : StepPost p s P u) (h' : StepPost p u Q t) : StepPost p s Q t :=
  ⟨h'.1, h.2.1.trans h'.2.1, fun i hi => (h'.2.2.1 i hi).trans (h.2.2.1 i hi), keep_trans h.2.2.2 h'.2.2.2⟩

theorem nonzero_ok {p : KpP} {xb : List Byte} {mi : BitVec 64} {s : State} (h : Work p xb mi s)
    (hd : s.gpr .rdi = off p.B (inner p.w)) :
    WP isa (seqs (isNonzero aXm)) s fun t => t.gpr .rax = bit (0 < Spec.Rsa.os2ip xb) ∧
      t.mem = s.mem ∧ Keep mmRegs s t := by
  have hk := h.base.k1
  have hk' := h.base.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold KpP.w; omega
  refine WP.mono (geArr_ok (h.mem.ctx hd).good (Nat.le_refl _) (by omega) (by omega)
    (show aXm < 8 by decide) (show aOne < 8 by decide)) fun t ⟨ha, hm, k⟩ => ?_
  rw [h.x, h.xv.one] at ha
  refine ⟨?_, hm, k⟩
  have he : (¬Spec.Rsa.os2ip xb < 1) = (0 < Spec.Rsa.os2ip xb) := propext (by omega)
  simpa only [bit, he] using ha

/-- Store a flag in the inner header. -/
theorem storeF_ok {p : KpP} {xb : List Byte} {mi : BitVec 64} {s : State} (h : Work p xb mi s)
    (hd : s.gpr .rdi = off p.B (inner p.w)) :
    WP isa (.block [.store (hdr sF) .rax]) s
      (StepPost p s fun t => Work p xb mi t ∧ t.gpr .rdi = off p.B (inner p.w) ∧
        word t.mem (off p.B (inner p.w)) (8 * sF) = s.gpr .rax ∧ t.gpr .rax = s.gpr .rax) := by
  have hc := h.mem.ctx hd
  have hn := hc.good.scr.nowrap
  have hF := hdr_lt_slot p.w 8 (show sF < 32 by decide)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off (off p.B (inner p.w)) (8 * sF)) (s.gpr .rax))
    (by xrun [State.ea, hdr, hdrOff, hd, hc.good.scr.st hF]) rfl) fun t ⟨hm, k⟩ => ?_
  have hf : Frm (off p.B (inner p.w)) [(8 * sF, 8)] s.mem t.mem := by
    rw [hm]
    exact Frm.of_outside (writeW_outside _ _ _ (by omega)) (by simp)
  have hr : ∀ r ∈ [(8 * sF, 8)], 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot p.w 8 := by
    simp only [List.mem_singleton]
    rintro r rfl
    exact ⟨by decide, hF⟩
  have hsep : ∀ {j}, j < 8 → ∀ r ∈ [(8 * sF, 8)], r.1 + r.2 ≤ slot p.w j ∨ slot p.w j + 8 * (p.w + 2) ≤ r.1 :=
    fun hj r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (hdr_lt_slot p.w _ (show sF < 32 by decide))
  obtain ⟨hw, hi, hs⟩ := h.child hd hf hr (hsep (by decide)) (hsep (by decide)) (hsep (by decide)) k
  refine ⟨⟨hw, (k.gpr (by decide)).trans hd, ?_, k.gpr (by decide)⟩, hi, hs, k.mono (by decide)⟩
  rw [hm]
  exact word_writeW_self _ _ _ _

/-- Conjoin a comparison with the saved nonzero flag. -/
theorem andF_flag {p : KpP} {xb : List Byte} {mi : BitVec 64} {s : State} {P Q : Prop}
    [Decidable P] [Decidable Q] (h : Work p xb mi s) (hd : s.gpr .rdi = off p.B (inner p.w))
    (ha : s.gpr .rax = bit Q) (hF : word s.mem (off p.B (inner p.w)) (8 * sF) = bit P) :
    WP isa (.block andF) s (StepPost p s fun t => Work p xb mi t ∧
      t.gpr .rdi = off p.B (inner p.w) ∧ t.gpr .rax = bit (P ∧ Q)) := by
  have hc := h.mem.ctx hd
  have hld := hdr_lt_slot p.w 8 (show sF < 32 by decide)
  unfold andF
  change WP isa (.block (([.alu .and .rax (.mem (hdr sF))] : List Instr) ++ [.store (hdr sF) .rax])) s _
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = bit (P ∧ Q) ∧ t.mem = s.mem)
    (by
      xrun [State.ea, hdr, hdrOff, hd, hc.good.scr.ld hld, ha, hF]
      by_cases hp : P <;> by_cases hq : Q <;> simp [bit, hp, hq]) rfl)
    fun u ⟨⟨hu, hm⟩, k⟩ => ?_
  refine WP.mono (storeF_ok (h.keep hm k) ((k.gpr (by decide)).trans hd))
    fun t ⟨⟨hw, hd', _, ha'⟩, hi, hs, kk⟩ => ?_
  refine ⟨⟨hw, hd', ha'.trans hu⟩, ?_, ?_, keep_trans (k.mono (by decide)) kk⟩
  · rw [hm] at hi; exact hi
  · intro i hi
    rw [hs i hi, hm]

end VG.Proof.Ffdh.X86_64.CheckPrivate
