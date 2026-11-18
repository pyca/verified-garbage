module

public import VerifiedGarbage.Impl.Ffdh.X86_64.CheckDomain
import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Ffdh.X86_64.Front
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Data
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Contract
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Setup
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Work
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import Mathlib.Data.Nat.Basic

/-! ### `Ffdh.X86_64.CheckDomain.Range`, which the modules that import this one used -/

section

/-! ### `Ffdh.X86_64.CheckDomain.Loads`, which this module and modules that import it used -/

section

/-! # FFDH domain validation on x86-64: load public components -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (loadArr)

/-- Loading a public component preserves the modulus workspace. -/
theorem load_component {p : CdP} {mi : BitVec 64} {s : State} {j : Nat} {bp : Addr} {bb : List Byte}
    (h : Work p mi s) (hd : s.gpr .rdi = off p.B (inner p.w)) (hj : j < 32)
    (hp : word s.mem p.B (8 * j) = bp) (hs : Src s p.B p.Z bp bb) (hl : bb.length = p.k) :
    WP isa (seqs (loadArr aXm j sK)) s (StepPost p s fun t => Work p mi t ∧
      t.gpr .rdi = off p.B (inner p.w) ∧
      wv t.mem (off p.B (inner p.w)) (slot p.w aXm) p.w = Spec.Rsa.os2ip bb) := by
  have hc := h.mem.ctx hd
  have hk := h.base.k1
  have hk' := h.base.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega_using []
  refine WP.mono (primeLoad_ok hc (by omega_using [hk, ew]) (Nat.le_refl _) (by omega_using [hk', ew]) (show aXm < 8 by decide)
    hj (show sK < 32 by decide) hp
    (by rw [hl]; exact h.base.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers])) hs
    (by rw [hl]; omega_using [hk]) (by rw [hl]; omega_using [hk']) (by rw [hl])) fun t ⟨hc', hx, ho, k⟩ => ?_
  have hf : Frm (off p.B (inner p.w)) [(slot p.w aXm, 8 * (p.w + 2))] s.mem t.mem :=
    Frm.of_outside ho (by simp)
  have hXm := slot_le (w := p.w) (show aXm < 8 by decide)
  have hXm0 := hdr_lt_slot p.w aXm (show 16 < 32 by decide)
  have hr : ∀ r ∈ [(slot p.w aXm, 8 * (p.w + 2))], 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot p.w 8 := by
    simp only [List.mem_singleton]; rintro r rfl
    exact ⟨by omega, hXm⟩
  have hsep : ∀ r ∈ [(slot p.w aXm, 8 * (p.w + 2))],
      (r.1 + r.2 ≤ slot p.w aN ∨ slot p.w aN + 8 * (p.w + 2) ≤ r.1) ∧
      (r.1 + r.2 ≤ slot p.w aOne ∨ slot p.w aOne + 8 * (p.w + 2) ≤ r.1) := fun r he => by
    rw [List.mem_singleton.mp he]
    exact arr_off p.w (show aXm ≠ aN by decide) (show aXm ≠ aOne by decide)
  obtain ⟨hw, hi, hh⟩ := h.child hd hf hr (fun r he => (hsep r he).1) (fun r he => (hsep r he).2) k
  exact ⟨⟨hw, hc'.rdi, hx⟩, hi, hh, k.mono (by decide)⟩

theorem load_generator {p : CdP} {mi : BitVec 64} {s : State}
    (h : Work p mi s) (hd : s.gpr .rdi = off p.B (inner p.w)) :
    WP isa (seqs (loadArr aXm sG sK)) s (StepPost p s fun t => Work p mi t ∧
      t.gpr .rdi = off p.B (inner p.w) ∧ wv t.mem (off p.B (inner p.w)) (slot p.w aXm) p.w = p.G) :=
  load_component h hd (by decide) h.g ((h.base.dom.drop p.k).take p.k) h.base.glen

theorem load_order {p : CdP} {mi : BitVec 64} {s : State}
    (h : Work p mi s) (hd : s.gpr .rdi = off p.B (inner p.w)) (hq : p.dl = 3 * p.k) :
    WP isa (seqs (loadArr aXm sQ sK)) s (StepPost p s fun t => Work p mi t ∧
      t.gpr .rdi = off p.B (inner p.w) ∧ wv t.mem (off p.B (inner p.w)) (slot p.w aXm) p.w = p.Q) :=
  load_component h hd (by decide) h.q ((h.base.dom.drop (2 * p.k)).take p.k) (h.base.qlen hq)

end VG.Proof.Ffdh.X86_64.CheckDomain

end

end

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
    rintro r (rfl | rfl) <;> simp only <;> unfold sF sFn at * <;> omega_arith
  have hsep : ∀ {j}, j < 8 → aTmp ≠ j → ∀ r ∈ rangeRanges p.w,
      r.1 + r.2 ≤ slot p.w j ∨ slot p.w j + 8 * (p.w + 2) ≤ r.1 := fun {j} hj hne r he => by
    have hTJ := slot_sep (w := p.w) hne
    have hFJ := hdr_lt_slot p.w j (show sF < 32 by decide)
    simp only [rangeRanges, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp only <;> omega_arith
  obtain ⟨hw, hi, hh⟩ := h.child hd hf hr (hsep (by decide) (by decide)) (hsep (by decide) (by decide)) k
  refine ⟨hw, hi, hh, hf.wv_eq (fun r he => ?_) ?_⟩
  · have := hsep (show aXm < 8 by decide) (by decide) r he
    omega_using [this]
  · have := (h.mem.ctx hd).good.scr.nowrap
    have := slot_le (w := p.w) (show aXm < 8 by decide)
    omega_arith

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
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega_using []
  refine WP.mono (range_ok (h.mem.ctx hd).good (Nat.le_refl _) (by omega_using [hk, ew]) (by omega_using [hk', ew])
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
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega_using []
  refine wp_seqs_append (a := isOdd aXm) (by simp [isOdd]) (by simp)
    (WP.mono (isOdd_ok (hw₂.mem.ctx hd₂).good (Nat.le_refl _) (by omega_using [hk, ew]) (show aXm < 8 by decide))
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

end

end

/-! ### `Ffdh.X86_64.CheckDomain.Context`, which this module and modules that import it used -/

section

/-! # FFDH domain validation on x86-64: input memory and sizes -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

structure CdCtx (s : State) : Prop where
  k1 : 64 ≤ (s.gpr .rdx).toNat
  k2 : (s.gpr .rdx).toNat ≤ 1024
  dl : (s.gpr .rsi).toNat = 2 * (s.gpr .rdx).toNat ∨ (s.gpr .rsi).toNat = 3 * (s.gpr .rdx).toNat
  hZ : 128 * (s.gpr .rdx).toNat + 256 ≤ (s.gpr .r8).toNat * 8
  scr : Scr s (s.gpr .rcx) ((s.gpr .r8).toNat * 8)
  dom : Src s (s.gpr .rcx) ((s.gpr .r8).toNat * 8) (s.gpr .rdi) (cdDom s)

theorem cdCtx_of {s : State} (h : cdPre s) : CdCtx s := by
  obtain ⟨hrd, hwr, dds, wD, wS, _, _, ⟨hk1, hk2⟩, hdl, hsl⟩ := h
  unfold Spec.Rsa.scratchWords at hsl
  exact ⟨hk1, hk2, hdl, by omega_using [hsl], Scr.of_mem (by rw [hwr]; simp) wS,
    src_of_region (by rw [hrd]; simp) (by omega_using []) dds⟩

def cdOf (s : State) : CdP :=
  ⟨s.gpr .rcx, (s.gpr .r8).toNat * 8, (s.gpr .rdx).toNat, (s.gpr .rsi).toNat,
    s.gpr .rdi, cdDom s, s.gpr .rsp⟩

end VG.Proof.Ffdh.X86_64.CheckDomain

end

end

/-! # FFDH domain validation on x86-64: save arguments and check p -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/CheckDomain/Entry.lean`, which only this module imported.
section

/-! # FFDH domain validation on x86-64: save the arguments and ABI registers -/

section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64.Crt (ws)
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

private def entryMem (s : State) (B : Addr) : Mem :=
  (((((((((s.mem.writeW (off B (8 * 0)) (s.gpr .rbx)).writeW (off B (8 * 1)) (s.gpr .rbp)).writeW
    (off B (8 * 2)) (s.gpr .r12)).writeW (off B (8 * 3)) (s.gpr .r13)).writeW
    (off B (8 * 4)) (s.gpr .r14)).writeW (off B (8 * 5)) (s.gpr .r15)).writeW
    (off B (8 * sDom)) (s.gpr .rdi)).writeW (off B (8 * sDomLen)) (s.gpr .rsi)).writeW
    (off B (8 * sK)) (s.gpr .rdx))

private theorem entryMem_facts (s : State) (B : Addr) :
    let m := entryMem s B
    word m B (8 * 0) = s.gpr .rbx ∧ word m B (8 * 1) = s.gpr .rbp ∧
    word m B (8 * 2) = s.gpr .r12 ∧ word m B (8 * 3) = s.gpr .r13 ∧
    word m B (8 * 4) = s.gpr .r14 ∧ word m B (8 * 5) = s.gpr .r15 ∧
    word m B (8 * sDom) = s.gpr .rdi ∧ word m B (8 * sDomLen) = s.gpr .rsi ∧
    word m B (8 * sK) = s.gpr .rdx ∧ Outside B 0 (8 * 19) s.mem m := by
  intro m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m entryMem
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

private theorem entry_eq : VG.Impl.Ffdh.X86_64.Domain.CheckDomain.entry =
    [.store (ws .rcx 0) .rbx, .store (ws .rcx 1) .rbp, .store (ws .rcx 2) .r12, .store (ws .rcx 3) .r13,
      .store (ws .rcx 4) .r14, .store (ws .rcx 5) .r15, .store (ws .rcx sDom) .rdi,
      .store (ws .rcx sDomLen) .rsi, .store (ws .rcx sK) .rdx, .mov .rdi (.reg .rcx)] := rfl

theorem cdEntry_ok {s : State} {B : Addr} (hB : s.gpr .rcx = B)
    (hw : ∀ i < 19, InRegions s.wr (off B (8 * i)) 8) :
    WP isa (.block VG.Impl.Ffdh.X86_64.Domain.CheckDomain.entry) s fun t => t.gpr .rdi = B ∧
      (∀ i < 6, word t.mem B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      Slots t.mem B [(sDom, s.gpr .rdi), (sDomLen, s.gpr .rsi), (sK, s.gpr .rdx)] ∧
      Outside B 0 (8 * 19) s.mem t.mem ∧ Keep [.rdi] s t := by
  rw [entry_eq]
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = entryMem s B)
    (by xrun [State.ea, ws, hB, hdrOff, hw 0 (by decide), hw 1 (by decide), hw 2 (by decide),
      hw 3 (by decide), hw 4 (by decide), hw 5 (by decide), hw sDom (by decide), hw sDomLen (by decide),
      hw sK (by decide)]; rfl) rfl)
    fun t ⟨⟨hdi, hm⟩, k⟩ => ?_
  obtain ⟨h0, h1, h2, h3, h4, h5, hD, hL, hK, ho⟩ := entryMem_facts s B
  rw [← hm] at h0 h1 h2 h3 h4 h5 hD hL hK ho
  refine ⟨hdi, ?_, ?_, ho, k⟩
  · intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact hD
    · exact hL
    · exact hK

end VG.Proof.Ffdh.X86_64.CheckDomain
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem entry_base {s : State} (c : CdCtx s) :
    WP isa (.block VG.Impl.Ffdh.X86_64.Domain.CheckDomain.entry) s fun t =>
      Base (cdOf s) t ∧ t.gpr .rdi = (cdOf s).B ∧ InScr (cdOf s).B (cdOf s).Z s.mem t.mem ∧
      (∀ i < 6, word t.mem (cdOf s).B (8 * i) = s.gpr (saved.getD i .rax)) ∧ Keep (.rdi :: mmRegs) s t := by
  have hZ := c.hZ
  have hk := c.k1
  refine WP.mono (cdEntry_ok rfl (fun i hi => c.scr.st (by omega_using [hZ, hi])))
    fun t ⟨hd, hs, hh, hf, k⟩ => ?_
  have hi : InScr (cdOf s).B (cdOf s).Z s.mem t.mem := InScr.of_outside hf (by dsimp only [cdOf]; omega_using [hZ])
  refine ⟨⟨c.k1, c.k2, c.dl, bytesAt_length _ _ _, c.hZ, c.scr.congr k.2.2, c.dom.congrK hi k,
    ?_⟩, hd, hi, hs, k.mono (by decide)⟩
  change Slots t.mem (s.gpr .rcx) (cdOf s).headers
  simp only [CdP.headers, cdOf, ofNat_toNat64]
  exact hh

theorem dom_base {p : CdP} {s : State} (h : Base p s) (hdi : s.gpr .rdi = p.B) :
    WP isa (.block domHead) s fun t => Base p t ∧ t.zf = some p.mv ∧ t.gpr .rdi = p.B ∧
      word t.mem p.B (8 * sG) = off p.dp p.k ∧ word t.mem p.B (8 * sQ) = off p.dp (2 * p.k) ∧
      InScr p.B p.Z s.mem t.mem ∧
      (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ Keep (.rdi :: mmRegs) s t := by
  have hZ := h.hZ
  have hk := h.k1
  refine WP.mono (domHead_ok h.scr hdi (by omega_using [hZ]) h.k1 h.k2
    (h.hdr (sDom, p.dp) (by simp [CdP.headers]))
    (h.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers])) (h.dom.take p.k) h.plen)
    fun t ⟨hz, hG, hQ, hf, hd, k⟩ => ?_
  have hi : InScr p.B p.Z s.mem t.mem := InScr.of_frm hf (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only <;> unfold sG sQ sFn at * <;> omega_using [hZ])
  have hh : ∀ i < 32, i ≠ sG → i ≠ sQ → word t.mem p.B (8 * i) = word s.mem p.B (8 * i) :=
    fun i hi hg hq => hf.word_eq (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl) <;> simp only <;> unfold sG sQ sFn at * <;> omega_arith) (by omega_using [hi])
  refine ⟨h.keep hi k ?_, hz, hd, hG, hQ, hi, ?_, k.mono (by decide)⟩
  · intro e he
    simp only [CdP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;>
      exact hh _ (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide)
  · intro i hi
    exact hh i (by omega_using [hi]) (by unfold sG sFn; omega_using [hi]) (by unfold sQ sFn; omega_using [hi])

end VG.Proof.Ffdh.X86_64.CheckDomain
