module

public import VerifiedGarbage.Impl.Ffdh.X86_64.CheckDomain
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Setup

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Loads
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Work
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.Contract
/-! # FFDH domain validation on x86-64: component ranges -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/CheckDomain/Flags.lean`, which only this module imported.
section

/-! # FFDH domain validation on x86-64: flags -/

section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Store a flag in the inner header. -/
theorem storeF_ok {p : CdP} {mi : BitVec 64} {s : State} (h : Work p mi s)
    (hd : s.gpr .rdi = off p.B (inner p.w)) :
    WP isa (.block [.store (hdr sF) .rax]) s
      (StepPost p s fun t => Work p mi t ∧ t.gpr .rdi = off p.B (inner p.w) ∧
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
  obtain ⟨hw, hi, hs⟩ := h.child hd hf hr (hsep (by decide)) (hsep (by decide)) k
  refine ⟨⟨hw, (k.gpr (by decide)).trans hd, ?_, k.gpr (by decide)⟩, hi, hs, k.mono (by decide)⟩
  rw [hm]
  exact word_writeW_self _ _ _ _

/-- Conjoin a comparison with the saved nonzero flag. -/
theorem andF_flag {p : CdP} {mi : BitVec 64} {s : State} {P Q : Prop}
    [Decidable P] [Decidable Q] (h : Work p mi s) (hd : s.gpr .rdi = off p.B (inner p.w))
    (ha : s.gpr .rax = bit Q) (hF : word s.mem (off p.B (inner p.w)) (8 * sF) = bit P) :
    WP isa (.block andF) s (StepPost p s fun t => Work p mi t ∧
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

end VG.Proof.Ffdh.X86_64.CheckDomain
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def rangeRanges (w : Nat) : List (Nat × Nat) := [(slot w aTmp, 8 * w), (8 * sF, 8)]

theorem range_frame {p : CdP} {mi : BitVec 64} {s t : State} {regs : List Reg}
    (h : Work p mi s) (hd : s.gpr .rdi = off p.B (inner p.w))
    (hf : Frm (off p.B (inner p.w)) (rangeRanges p.w) s.mem t.mem) (k : Keep regs s t) :
    Work p mi t ∧ InScr p.B p.Z s.mem t.mem ∧
      (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧
      wv t.mem (off p.B (inner p.w)) (slot p.w aXm) p.w =
        wv s.mem (off p.B (inner p.w)) (slot p.w aXm) p.w := by
  have hT := slot_le (w := p.w) (show aTmp < 8 by decide)
  have hT0 := hdr_lt_slot p.w aTmp (show 16 < 32 by decide)
  have hF := hdr_lt_slot p.w 8 (show sF < 32 by decide)
  have hr : ∀ r ∈ rangeRanges p.w, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot p.w 8 := by
    simp only [rangeRanges, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only <;> unfold sF sFn at * <;> omega
  have hsep : ∀ {j}, j < 8 → aTmp ≠ j → ∀ r ∈ rangeRanges p.w,
      r.1 + r.2 ≤ slot p.w j ∨ slot p.w j + 8 * (p.w + 2) ≤ r.1 := fun {j} hj hne r he => by
    have hTJ := slot_sep (w := p.w) hne
    have hFJ := hdr_lt_slot p.w j (show sF < 32 by decide)
    simp only [rangeRanges, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp only <;> omega
  obtain ⟨hw, hi, hh⟩ := h.child hd hf hr (hsep (by decide) (by decide)) (hsep (by decide) (by decide)) k
  refine ⟨hw, hi, hh, hf.wv_eq (fun r he => ?_) ?_⟩
  · have := hsep (show aXm < 8 by decide) (by decide) r he
    omega
  · have := (h.mem.ctx hd).good.scr.nowrap
    have := slot_le (w := p.w) (show aXm < 8 by decide)
    omega

theorem component_range {p : CdP} {mi : BitVec 64} {s : State} {n : Nat}
    (h : Work p mi s) (hd : s.gpr .rdi = off p.B (inner p.w))
    (hx : wv s.mem (off p.B (inner p.w)) (slot p.w aXm) p.w = n) :
    WP isa (seqs (range aXm)) s (StepPost p s fun t => Work p mi t ∧
      t.gpr .rdi = off p.B (inner p.w) ∧
      t.gpr .rax = bit (1 < n ∧ 2 * (n / 2) + 1 < p.P) ∧
      word t.mem (off p.B (inner p.w)) (8 * sF) = t.gpr .rax ∧
      wv t.mem (off p.B (inner p.w)) (slot p.w aXm) p.w = n) := by
  have hk := h.base.k1
  have hk' := h.base.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega
  refine WP.mono (range_ok (h.mem.ctx hd).good (Nat.le_refl _) (by omega) (by omega)
    (show aXm < 8 by decide) (by decide) h.xv.one) fun t ⟨ha, hF, hf, k⟩ => ?_
  rw [hx, h.xv.n] at ha
  obtain ⟨hw, hi, hh, hx'⟩ := range_frame h hd hf k
  exact ⟨⟨hw, (k.gpr (by decide)).trans hd, ha, hF, hx'.trans hx⟩, hi, hh, k.mono (by decide)⟩

theorem generator_range {p : CdP} {mi : BitVec 64} {s : State}
    (h : Work p mi s) (hd : s.gpr .rdi = off p.B (inner p.w))
    (hx : wv s.mem (off p.B (inner p.w)) (slot p.w aXm) p.w = p.G) :
    WP isa (seqs (rangeTest aXm)) s (StepPost p s fun t => Work p mi t ∧
      t.gpr .rdi = off p.B (inner p.w) ∧ t.zf = some (!decide p.gr)) := by
  unfold rangeTest
  refine wp_seqs_append (a := range aXm) (by simp [range, gt1, ltArr, cmpArr]) (by simp)
    (WP.mono (component_range h hd hx) fun u ⟨⟨hw, hdi, ha, _, _⟩, hi, hh, k⟩ => ?_)
  simp only [seqs]
  refine WP.mono (test_bit_ok ha) fun t ⟨hz, hm, kk⟩ => ?_
  exact ⟨⟨hw.keep hm kk, (kk.gpr (by decide)).trans hdi, hz⟩,
    by rw [hm]; exact hi, (fun i hi => by rw [hm]; exact hh i hi), keep_trans k (kk.mono (by decide))⟩

theorem order_range {p : CdP} {mi : BitVec 64} {s : State}
    (h : Work p mi s) (hd : s.gpr .rdi = off p.B (inner p.w)) (hq : p.dl = 3 * p.k) :
    WP isa (seqs VG.Impl.Ffdh.X86_64.Domain.CheckDomain.qRange) s
      (StepPost p s fun t => Work p mi t ∧ t.gpr .rdi = off p.B (inner p.w) ∧
        t.zf = some (!decide p.qr)) := by
  unfold VG.Impl.Ffdh.X86_64.Domain.CheckDomain.qRange
  simp only [List.append_assoc]
  refine wp_seqs_append (a := VG.Impl.Rsa.X86_64.Crt.loadArr aXm sQ sK)
    (by simp [VG.Impl.Rsa.X86_64.Crt.loadArr]) (by simp [range, gt1, ltArr, cmpArr])
    (WP.mono (load_order h hd hq) fun u₁ S₁ => ?_)
  obtain ⟨hw₁, hd₁, hx₁⟩ := S₁.1
  refine wp_seqs_append (a := range aXm) (by simp [range, gt1, ltArr, cmpArr]) (by simp [isOdd])
    (WP.mono (component_range hw₁ hd₁ hx₁) fun u₂ S₂ => ?_)
  obtain ⟨hw₂, hd₂, ha₂, hF₂, hx₂⟩ := S₂.1
  have hk := hw₂.base.k1
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega
  refine wp_seqs_append (a := isOdd aXm) (by simp [isOdd]) (by simp)
    (WP.mono (isOdd_ok (hw₂.mem.ctx hd₂).good (Nat.le_refl _) (by omega) (show aXm < 8 by decide))
      fun u₃ ⟨ha₃, hm₃, k₃⟩ => ?_)
  rw [hx₂] at ha₃
  have hw₃ := hw₂.keep hm₃ k₃
  have hd₃ := (k₃.gpr (show Reg.rdi ∉ [Reg.rax, Reg.rbx] by decide)).trans hd₂
  have hF₃ : word u₃.mem (off p.B (inner p.w)) (8 * sF) = bit (1 < p.Q ∧ 2 * (p.Q / 2) + 1 < p.P) := by
    rw [hm₃]; exact hF₂.trans ha₂
  simp only [seqs]
  refine WP.seq (WP.mono (andF_flag hw₃ hd₃ ha₃ hF₃) fun u₄ S₄ => ?_)
  have ha₄ : u₄.gpr .rax = bit p.qr := by
    have he : ((1 < p.Q ∧ 2 * (p.Q / 2) + 1 < p.P) ∧ p.Q % 2 = 1) = p.qr := propext (by
      simp only [CdP.qr]; grind)
    simpa only [bit, he] using S₄.1.2.2
  refine WP.mono (test_bit_ok ha₄) fun t ⟨hz, hm, k⟩ => ?_
  have S₃ : StepPost p u₂ (fun _ => True) u₃ := ⟨trivial, by rw [hm₃]; exact InScr.refl _ _ _,
    (fun _ _ => by rw [hm₃]), k₃.mono (by decide)⟩
  have H := ((S₁.trans S₂).trans S₃).trans S₄
  exact ⟨⟨S₄.1.1.keep hm k, (k.gpr (by decide)).trans S₄.1.2.1, hz⟩,
    by rw [hm]; exact H.2.1, (fun i hi => by rw [hm]; exact H.2.2.1 i hi), keep_trans H.2.2.2 (k.mono (by decide))⟩

end VG.Proof.Ffdh.X86_64.CheckDomain
