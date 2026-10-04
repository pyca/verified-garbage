import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.R2
import VerifiedGarbage.Proof.Bignum.X86_64.Exp

/-!
# `vg_rsa_private_crt` on x86-64: the fixes and the products

`primeFix`, in a prime's workspace, replaces the prime by 3 where the mask is
clear and computes its `-X⁻¹` and the number 1 (`primeFix_ok`);
`pqProduct` leaves `p q` in the modulus' accumulators (`pqProduct_ok`), and
the start of `finish` `m_q + h q` (`finishSum_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

/-! ## The fixes of a prime -/

/-- The low word of the fixed prime: the masked word or'ed with 3 where the
mask is clear. -/
theorem fixWord (c : Bool) (x : BitVec 64) :
    (mask c ^^^ BitVec.signExtend 64 (BitVec.ofInt 32 (-1))) &&& (3 : BitVec 64) ||| x &&& mask c =
      if c then x else 3 := by
  cases c
  · rw [mask_false, show x &&& (0 : BitVec 64) = 0 from BitVec.and_zero,
      show ∀ y : BitVec 64, y ||| (0 : BitVec 64) = y from fun _ => BitVec.or_zero]
    show _ = (3 : BitVec 64); decide
  · rw [mask_true, BitVec.and_allOnes, show (BitVec.allOnes 64 ^^^ BitVec.signExtend 64 (BitVec.ofInt 32 (-1))) &&&
      (3 : BitVec 64) = 0#64 by decide, BitVec.zero_or]; rfl

/-- The fix of the low word of `[rbx]`. -/
def fixLow : List Instr :=
  [.mov .rax (.reg .r15), .alu .xor .rax (.imm (BitVec.ofInt 32 (-1))), .alu .and .rax (.imm 3),
    .alu .or .rax (.mem (at0 .rbx)), .store (at0 .rbx) .rax, .mov .rbx (.reg .rax)]

/-- `-X⁻¹` into the header, and the operands of `setWord`. -/
def fixTail : List Instr := [.store (hdr sMinv) .r15, .mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)]

/-- The mask from the modulus' header into `sMaskX`. -/
def fixMask : List Instr :=
  [.mov .rax (.mem (hdr Crt.sLink)), .mov .rax (.mem (Crt.ws .rax sMask)), .store (hdr Crt.sMaskX) .rax]

theorem primeFix_eq : Crt.primeFix =
    ([.block fixMask] : List (Prog isa)) ++ Crt.maskArr aN ++
      ([.block (fixLow ++ minv ++ fixTail), setWord aOne .rcx] : List (Prog isa)) := rfl

/-- `primeFix`'s first step: the mask from the modulus' header. -/
theorem fixMask_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {c : Bool}
    (hc : SubCtx s B Z o w wx minv) (hM : word s.mem B (8 * sMask) = mask c) :
    WP isa (.block fixMask) s fun t =>
      t.mem = s.mem.writeW (off (off B o) (8 * Crt.sMaskX)) (mask c) ∧ Keep [.rax] s t := by
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have hg := hc.good
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off B o) (8 * i)) 8 := fun i hi' =>
    hg.scr.ld (by have := hdr_lt_slot wx 8 hi'; omega)
  have hln : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi' =>
    hc.scr.ld (by have := hdr_lt_slot w 8 hi'; omega)
  have hst : ∀ i < 32, InRegions s.wr (off (off B o) (8 * i)) 8 := fun i hi' =>
    hg.scr.st (by have := hdr_lt_slot wx 8 hi'; omega)
  refine WP.keep [.rax] (c := .block fixMask)
    (Q := fun t => t.mem = s.mem.writeW (off (off B o) (8 * Crt.sMaskX)) (mask c)) ?_ rfl
  unfold fixMask
  xrun [State.ea, hdr, Crt.ws, hc.rdi, hdrOff, hl Crt.sLink (by decide), hc.link,
    hln sMask (by decide), hM, hst Crt.sMaskX (by decide)]

/-- The fix of the low word of `[rbx]` (the masked `x`), into `rbx`. -/
theorem fixLow_ok {t : State} {G : Addr} {Zx d : Nat} {c : Bool} {x : BitVec 64} (hs : Scr t G Zx)
    (hbx : t.gpr .rbx = off G d) (h15 : t.gpr .r15 = mask c) (hd : d + 8 ≤ Zx)
    (hx : word t.mem G d = x &&& mask c) :
    WP isa (.block fixLow) t fun t' =>
      (t'.gpr .rbx = if c then x else 3) ∧ t'.mem = t.mem.writeW (off G d) (if c then x else 3) ∧
      Keep [.rax, .rbx] t t' := by
  refine WP.mono (WP.keep [.rax, .rbx] (Q := fun t' => (t'.gpr .rbx = if c then x else 3) ∧
    t'.mem = t.mem.writeW (off G d) (if c then x else 3)) ?_ rfl) fun t' ⟨⟨h1, h2⟩, k⟩ => ⟨h1, h2, k⟩
  unfold fixLow
  xrun [State.ea, at0, hbx, h15, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hs.ld hd, hs.st hd, hx, fixWord]

/-- In a prime's workspace (`c` the validity mask in the modulus' `sMask`):
the mask into `sMaskX`, `X := c ? X : 3`, `-X⁻¹` and the number 1. -/
theorem primeFix_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {c : Bool} {X : Nat}
    (hc : SubCtx s B Z o w wx minv) (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hM : word s.mem B (8 * sMask) = mask c) (hX : wv s.mem (off B o) (slot wx aN) wx = X)
    (hodd : c = true → X % 2 = 1) :
    WP isa (seqs Crt.primeFix) s fun t => ∃ minv', SubCtx t B Z o w wx minv' ∧
      wv t.mem (off B o) (slot wx aN) wx = (if c then X else 3) ∧
      ((word t.mem (off B o) (slot wx aN)).toNat * minv'.toNat + 1) % 2 ^ 64 = 0 ∧
      wv t.mem (off B o) (slot wx aOne) wx = 1 ∧ word t.mem (off B o) (8 * Crt.sMaskX) = mask c ∧
      Frm (off B o) [(slot wx aN, 8 * (wx + 2)), (slot wx aOne, 8 * (wx + 2)), (8 * Crt.sMaskX, 8), (8 * sMinv, 8)]
        s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have hGn : (off B o).toNat + slot wx 8 ≤ 2 ^ 64 := hc.good.scr.nowrap
  have sN := slot_le (w := wx) (show aN < 8 by decide)
  have sO := slot_le (w := wx) (show aOne < 8 by decide)
  have hN0 := hdr_lt_slot wx aN (show 31 < 32 by decide)
  have hO0 := hdr_lt_slot wx aOne (show 31 < 32 by decide)
  have sNO := slot_sep (w := wx) (show aN ≠ aOne by decide)
  have eMX : Crt.sMaskX = 24 := rfl
  have eMi : sMinv = 7 := rfl
  rw [primeFix_eq]
  unfold Crt.maskArr
  simp only [List.cons_append, List.nil_append, seqs]
  -- The mask.
  refine WP.seq (WP.mono (fixMask_ok hc hM) fun s₁ ⟨hm₁, k₁⟩ => ?_)
  have o₁ := writeW_outside s.mem (off B o) (d := 8 * Crt.sMaskX) (mask c) (by decide)
  rw [← hm₁] at o₁
  have f₁ : Frm (off B o) [(8 * Crt.sMaskX, 8)] s.mem s₁.mem := Frm.of_outside o₁ (by simp)
  have hc₁ := hc.of_frm f₁ (fun r hr => by rw [List.mem_singleton.mp hr, eMX]; omega) k₁.2.2 (k₁.gpr (by decide))
  have hMX₁ : word s₁.mem (off B o) (8 * Crt.sMaskX) = mask c := by rw [hm₁]; exact word_writeW_self _ _ _ _
  have hX₁ : wv s₁.mem (off B o) (slot wx aN) wx = X := by
    rw [o₁.wv (Or.inr (by omega)) (by omega)]; exact hX
  -- `X &&&= mask`.
  have hg₁ := hc₁.good
  have hl : ∀ i < 32, InRegions (s₁.rd ++ s₁.wr) (off (off B o) (8 * i)) 8 := fun i hi' =>
    hg₁.scr.ld (by have := hdr_lt_slot wx 8 hi'; omega)
  refine WP.seq (WP.mono (WP.keep [.r15, .r12, .rbx] (Q := fun t => t.gpr .r15 = mask c ∧
      t.gpr .r12 = BitVec.ofNat 64 wx ∧ t.gpr .rbx = off (off B o) (slot wx aN) ∧ t.mem = s₁.mem)
    (by xrun [State.ea, hdr, hg₁.rdi, hdrOff, hl Crt.sMaskX (by decide), hl (sArr aN) (by decide),
      hl sW (by decide), hMX₁, hg₁.hdr.harr aN (by decide), hg₁.hdr.hw]) rfl)
    fun s₂ ⟨⟨h15, h12, hbx, hm₂⟩, k₂⟩ => ?_)
  have hs₂ := hg₁.scr.congr k₂.2.2
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₂.mem → Keep [.r14] s₂ t → t.cf = s₂.cf →
      MaskInv s₂ (off B o) (slot wx 8) (slot wx aN) c 0 t := fun t h14 hm k _ =>
    ⟨hs₂.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := wx) (by omega) (by omega)
    (MaskInv s₂ (off B o) (slot wx 8) (slot wx aN) c) h0
    (fun i _ hi t hI => maskStep_ok hbx h15 h12 (by omega) (by omega) hi hI)) fun s₃ hI => ?_)
  -- The low word, `-X⁻¹` and the number 1.
  have k₃ := hI.keep
  have hbx₃ : s₃.gpr .rbx = off (off B o) (slot wx aN) := (k₃.gpr (by decide)).trans hbx
  have h15₃ : s₃.gpr .r15 = mask c := (k₃.gpr (by decide)).trans h15
  have hx₃ : word s₃.mem (off B o) (slot wx aN) = word s₁.mem (off B o) (slot wx aN) &&& mask c := by
    have := hI.done 0 (by omega); rw [Nat.mul_zero, Nat.add_zero, hm₂] at this; exact this
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (fixLow_ok hI.scr hbx₃ h15₃ (by omega) hx₃) fun s₄ ⟨hbx₄, hm₄, k₄⟩ => ?_
  have hodd₄ : (s₄.gpr .rbx).toNat % 2 = 1 := by
    rw [hbx₄]
    cases c
    · show (3 : BitVec 64).toNat % 2 = 1; decide
    · show (word s₁.mem (off B o) (slot wx aN)).toNat % 2 = 1
      rw [← wv_mod64 _ _ _ (show 1 ≤ wx by omega), hX₁, Nat.mod_mod_of_dvd _ (by decide)]; exact hodd rfl
  refine WP.mono (minv_ok s₄ hodd₄) fun s₅ ⟨hinv, k₅, hm₅⟩ => ?_
  rw [hbx₄] at hinv
  have hs₅ : Scr s₅ (off B o) (slot wx 8) := (hI.scr.congr k₄.2.2).congr k₅.2.2
  have hdi₅ : s₅.gpr .rdi = off B o :=
    (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans
      ((k₂.gpr (by decide)).trans hg₁.rdi)))
  refine WP.mono (WP.keep [.rdx, .rcx] (c := .block fixTail) (Q := fun t => t.gpr .rdx = 1 ∧
      t.gpr .rcx = BitVec.ofNat 64 0 ∧ t.mem = s₅.mem.writeW (off (off B o) (8 * sMinv)) (s₅.gpr .r15)) (by
    unfold fixTail
    xrun [State.ea, hdr, hdi₅, hdrOff, hs₅.st (d := 8 * sMinv) (by omega)]) rfl)
    fun s₆ ⟨⟨hdx₆, hcx₆, hm₆⟩, k₆⟩ => ?_
  -- What changed so far.
  have o₄ := writeW_outside s₃.mem (off B o) (d := slot wx aN) (if c then word s₁.mem (off B o) (slot wx aN) else 3)
    (by omega)
  rw [← hm₄] at o₄
  have o₆ := writeW_outside s₅.mem (off B o) (d := 8 * sMinv) (s₅.gpr .r15) (by decide)
  rw [← hm₆, hm₅] at o₆
  have o₃ := hI.out
  rw [hm₂] at o₃
  have f₁₄ : Frm (off B o) [(slot wx aN, 8 * (wx + 2))] s₁.mem s₄.mem :=
    (Frm.of_outside (o₃.mono (o' := slot wx aN) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega))
      (by simp)).trans
      (Frm.of_outside (o₄.mono (o' := slot wx aN) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega)) (by simp))
  have f₁₆ : Frm (off B o) ([(slot wx aN, 8 * (wx + 2))] ++ [(8 * sMinv, 8)]) s₁.mem s₆.mem :=
    f₁₄.append (Frm.of_outside o₆ (by simp))
  have hh₆ : ∀ i < 32, i ≠ sMinv → word s₆.mem (off B o) (8 * i) = word s₁.mem (off B o) (8 * i) :=
    fun i hi' hne => f₁₆.word_eq (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · omega
      · rw [eMi] at hne ⊢; omega) (by omega)
  have hH₆ : Hdr s₆.mem (off B o) wx (s₅.gpr .r15) :=
    ⟨(hh₆ _ (by decide) (by decide)).trans hc₁.hdr.hw, by rw [hm₆]; exact word_writeW_self _ _ _ _,
      fun j hj => (hh₆ _ (by unfold sArr; omega) (by unfold sArr; rw [eMi]; omega)).trans (hc₁.hdr.harr j hj)⟩
  have K₆ := ((((k₂.trans k₃).trans k₄).trans k₅).trans k₆)
  have hdi₆ : s₆.gpr .rdi = off B o := (K₆.gpr (by decide)).trans hg₁.rdi
  have h12₆ : s₆.gpr .r12 = BitVec.ofNat 64 wx :=
    ((((k₃.trans k₄).trans k₅).trans k₆).gpr (by decide)).trans h12
  refine WP.mono (setWord_ok (hs₅.congr k₆.2.2) hdi₆ hH₆ (Nat.le_refl _) h12₆ (by omega) (by omega)
    (o := aOne) (by decide) (ri := .rcx) (by decide) (i := 0) (by omega) hcx₆) fun t ⟨hone, ho₇, k₇⟩ => ?_
  have f₇ : Frm (off B o) [(slot wx aOne, 8 * (wx + 2))] s₆.mem t.mem := Frm.of_outside ho₇ (by simp)
  have f₄t : Frm (off B o) ([(8 * sMinv, 8)] ++ [(slot wx aOne, 8 * (wx + 2))]) s₄.mem t.mem :=
    (Frm.of_outside o₆ (by simp)).append f₇
  have f₁t := f₁₆.append f₇
  have F := f₁.append f₁t
  have hF : ∀ r ∈ [(8 * Crt.sMaskX, 8)] ++ ([(slot wx aN, 8 * (wx + 2))] ++ [(8 * sMinv, 8)] ++
      [(slot wx aOne, 8 * (wx + 2))]), 8 * 6 + 8 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8 := fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only [eMX, eMi] <;> omega
  have hFw : ∀ i < 32, i ≠ sMinv → i ≠ Crt.sMaskX → word t.mem (off B o) (8 * i) = word s.mem (off B o) (8 * i) :=
    fun i hi' h1 h2 => F.word_eq (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [eMi] at h1; rw [eMX] at h2
      rcases hr with rfl | rfl | rfl | rfl <;> simp only [eMX, eMi] <;> omega) (by omega)
  have hFb : ∀ i < 32, word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi' =>
    F.word_below (L := slot wx 8) (fun r hr => (hF r hr).2) (by omega) (by unfold slot hdrBytes at hi; omega)
      (by have := hdr_lt_slot w 8 hi'; omega)
  have K := (k₁.trans K₆).trans k₇
  have hN₄ : ∀ {d k : Nat}, slot wx aN ≤ d → d + 8 * k ≤ slot wx aN + 8 * (wx + 2) →
      wv t.mem (off B o) d k = wv s₄.mem (off B o) d k := fun h1 h2 =>
    f₄t.wv_eq (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [eMi] <;> omega) (by omega)
  have hw₀ : word t.mem (off B o) (slot wx aN) = if c then word s₁.mem (off B o) (slot wx aN) else 3 := by
    rw [f₄t.word_eq (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [eMi] <;> omega) (by omega), hm₄]
    exact word_writeW_self _ _ _ _
  have hup : ∀ i < wx, i ≠ 0 → word s₄.mem (off B o) (slot wx aN + 8 * i) =
      word s₁.mem (off B o) (slot wx aN + 8 * i) &&& mask c := fun i hi' hne => by
    rw [hm₄, (writeW_outside _ _ _ (by omega)).word (Or.inr (by omega)) (by omega), hI.done i hi', hm₂]
  refine ⟨s₅.gpr .r15, ⟨hc.scr.congr K.2.2, (K.gpr (by decide)).trans hc.rdi,
    Arrays.hdr (Arrays.of_outside (List.mem_singleton_self _) ho₇ (Nat.le_refl _) (Nat.le_refl _)) hH₆,
    (hFw _ (by decide) (by decide) (by decide)).trans hc.link, (hFb _ (by decide)).trans hc.nw,
    fun j hj => (hFb _ (by unfold sArr; omega)).trans (hc.narr j hj), hc.lo, hc.hi⟩, ?_, ?_, ?_, ?_, ?_,
    K.mono (by decide)⟩
  · rw [hN₄ (Nat.le_refl _) (by omega)]
    cases c
    · rw [wv_single _ _ _ (i := 0) wx (by omega) fun q hq hne => by
        rw [hup q hq hne, mask_false]; exact BitVec.and_zero, Nat.mul_zero, Nat.add_zero, hm₄, word_writeW_self]
      rfl
    · rw [← hX₁]
      refine wv_congr fun i hi' => ?_
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [Nat.mul_zero, Nat.add_zero, hm₄, word_writeW_self]; rfl
      · rw [hup i hi' (by omega), mask_true, BitVec.and_allOnes]
  · rw [hw₀]; exact hinv
  · rw [hone, hdx₆]; rfl
  · rw [f₁t.word_eq (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [eMX, eMi] <;> omega) (by omega)]
    exact hMX₁
  · exact F.mono fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp

/-! ## Products into the modulus' accumulators -/

theorem accs_le (w : Nat) : slot w aAcc + 8 * (2 * w + 2) ≤ slot w 8 := by
  have := slot_le (w := w) (show aTmp < 8 by decide)
  simp only [slot, aTmp, aAcc] at this ⊢; omega

/-- `zeroAccs`: the `2 w + 2` words from `aAcc` cleared. -/
theorem zeroAccs_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw' : w < 2 ^ 30) :
    WP isa (seqs Crt.zeroAccs) s fun t => (∀ k < 2 * w + 2, word t.mem B (slot w aAcc + 8 * k) = 0) ∧
      Outside B (slot w aAcc) (8 * (2 * w + 2)) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hA := accs_le w
  unfold Crt.zeroAccs
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r8, .rbx] (Q := fun t => t.gpr .r8 = off B (slot w aAcc) ∧
      t.gpr .rbx = BitVec.ofNat 64 w ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr aAcc) (by decide), hl sW (by decide),
      hg.hdr.harr aAcc (by decide), hg.hdr.hw]) rfl) fun s₁ ⟨⟨h8, hbx, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (zeroWin_ok (hg.scr.congr k₁.2.2) h8 hbx (by omega) (by omega))
    fun t ⟨hv, ho, k⟩ => ⟨hv, by rw [hm₁] at ho; exact ho, (k₁.trans k).mono (by decide)⟩

/-- The operands of `mulRows`: `[r11]` the array `ja` of `p`'s workspace
(`r10` its words), `[r9]` `q`'s `aN` (`r12` its words), `r8` the modulus'
accumulator. -/
def rowsHdr (ja : Nat) : List Instr :=
  [.mov .rax (.mem (hdr Crt.sWsP)), .mov .r11 (.mem (Crt.ws .rax (sArr ja))), .mov .r10 (.mem (Crt.ws .rax sW)),
    .mov .rax (.mem (hdr Crt.sWsQ)), .mov .r9 (.mem (Crt.ws .rax (sArr aN))), .mov .r12 (.mem (Crt.ws .rax sW)),
    .mov .r8 (.mem (hdr (sArr aAcc)))]

theorem rowsHdr_ok {s : State} {B : Addr} {Z w op oq wp wq ja : Nat} {A Q : Addr} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hacc : word s.mem B (8 * sArr aAcc) = off B (slot w aAcc))
    (hp : word s.mem B (8 * Crt.sWsP) = off B op) (hq : word s.mem B (8 * Crt.sWsQ) = off B oq)
    (hpw : word s.mem (off B op) (8 * sW) = BitVec.ofNat 64 wp)
    (hqw : word s.mem (off B oq) (8 * sW) = BitVec.ofNat 64 wq)
    (hpa : word s.mem (off B op) (8 * sArr ja) = A) (hqa : word s.mem (off B oq) (8 * sArr aN) = Q)
    (hja : ja < 8) (hlo : slot w 8 ≤ op) (hop : op + slot wp 8 + tabBytes wp ≤ oq) (hoq : oq + slot wq 8 + tabBytes wq ≤ Z) :
    WP isa (.block (rowsHdr ja)) s fun t =>
      t.gpr .r11 = A ∧ t.gpr .r10 = BitVec.ofNat 64 wp ∧ t.gpr .r9 = Q ∧ t.gpr .r12 = BitVec.ofNat 64 wq ∧
      t.gpr .r8 = off B (slot w aAcc) ∧ t.mem = s.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have h8p := hdr_lt_slot wp 8 (show 31 < 32 by decide)
  have h8q := hdr_lt_slot wq 8 (show 31 < 32 by decide)
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  have hlp : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off B op) (8 * i)) 8 := fun i hi =>
    (hs.sub (o := op) (n := slot wp 8) (by omega) (by omega)).ld (by omega)
  have hlq : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off B oq) (8 * i)) 8 := fun i hi =>
    (hs.sub (o := oq) (n := slot wq 8) (by omega) (by omega)).ld (by omega)
  refine WP.mono (WP.keep [.rax, .r11, .r10, .r9, .r12, .r8] (Q := fun t => t.gpr .r11 = A ∧
      t.gpr .r10 = BitVec.ofNat 64 wp ∧ t.gpr .r9 = Q ∧ t.gpr .r12 = BitVec.ofNat 64 wq ∧
      t.gpr .r8 = off B (slot w aAcc) ∧ t.mem = s.mem)
    (by
      unfold rowsHdr
      xrun [State.ea, hdr, Crt.ws, hdi, hdrOff, hl Crt.sWsP (by decide), hl Crt.sWsQ (by decide),
        hl (sArr aAcc) (by decide), hp, hq, hacc, hlp (sArr ja) (by unfold sArr; omega), hlp sW (by decide),
        hlq (sArr aN) (by decide), hlq sW (by decide), hpw, hqw, hpa, hqa]) rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, k.mono (by decide)⟩

/-- A word above a change, at an offset workspace. -/
theorem word_above {B : Addr} {a n : Nat} {m m' : Mem} (h : Outside B a n m m') {o d : Nat}
    (ho : a + n ≤ o) (hd : o + d + 8 ≤ 2 ^ 64) : word m' (off B o) d = word m (off B o) d := by
  rw [word_off, word_off]; exact h.word (Or.inr (by omega)) (by omega)

theorem pqProduct_eq :
    Crt.pqProduct = Crt.zeroAccs ++ ([.block (rowsHdr aN), Crt.mulRows] : List (Prog isa)) := rfl

/-- `p q` into the modulus' accumulators (`2 w + 2` words). -/
theorem pqProduct_ok {s : State} {B : Addr} {Z w op oq wp wq : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hw' : w < 2 ^ 29)
    (hp : word s.mem B (8 * Crt.sWsP) = off B op) (hq : word s.mem B (8 * Crt.sWsQ) = off B oq)
    (hpw : word s.mem (off B op) (8 * sW) = BitVec.ofNat 64 wp)
    (hqw : word s.mem (off B oq) (8 * sW) = BitVec.ofNat 64 wq)
    (hpa : word s.mem (off B op) (8 * sArr aN) = off B (op + slot wp aN))
    (hqa : word s.mem (off B oq) (8 * sArr aN) = off B (oq + slot wq aN))
    (hlo : slot w 8 ≤ op) (hop : op + slot wp 8 + tabBytes wp ≤ oq) (hoq : oq + slot wq 8 + tabBytes wq ≤ Z)
    (hwp : 1 ≤ wp) (hwp' : wp ≤ w) (hwq : 1 ≤ wq) (hwq' : wq ≤ w) :
    WP isa (seqs Crt.pqProduct) s fun t =>
      wv t.mem B (slot w aAcc) (2 * w + 2) = wv s.mem B (op + slot wp aN) wp * wv s.mem B (oq + slot wq aN) wq ∧
      Outside B (slot w aAcc) (8 * (2 * w + 2)) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hA := accs_le w
  have h8 := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have hpN := slot_le (w := wp) (show aN < 8 by decide)
  have hqN := slot_le (w := wq) (show aN < 8 by decide)
  have hpS := hdr_lt_slot wp 8 (show 31 < 32 by decide)
  have hqS := hdr_lt_slot wq 8 (show 31 < 32 by decide)
  have eW : sW = 6 := rfl
  have eN : sArr aN = 8 := rfl
  rw [pqProduct_eq]
  refine wp_seqs_append (by simp [Crt.zeroAccs]) (by simp)
    (WP.mono (zeroAccs_ok hg (by omega) (by omega)) fun s₁ ⟨hz₁, ho₁, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  have hh : ∀ i < 32, word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    ho₁.word (Or.inl (by have := hdr_lt_slot w aAcc hi; omega)) (by omega)
  simp only [seqs]
  refine WP.seq (WP.mono (rowsHdr_ok hs₁ ((k₁.gpr (by decide)).trans hg.rdi)
    ((hh _ (by decide)).trans (hg.hdr.harr aAcc (by decide))) ((hh _ (by decide)).trans hp)
    ((hh _ (by decide)).trans hq) ((word_above ho₁ (by omega) (by omega)).trans hpw)
    ((word_above ho₁ (by omega) (by omega)).trans hqw) ((word_above ho₁ (by omega) (by omega)).trans hpa)
    ((word_above ho₁ (by omega) (by omega)).trans hqa) (by decide) hlo hop hoq)
    fun s₂ ⟨h11, h10, h9, h12, h8, hm₂, k₂⟩ => ?_)
  have hz₂ : wv s₂.mem B (slot w aAcc) (wp + wq + 2) = 0 := by
    rw [hm₂]; exact wv_zero fun k hk => hz₁ k (by omega)
  refine WP.mono (mulRows_ok (hs₁.congr k₂.2.2) h11 h9 h10 h12 h8 hwp hwq (by omega) (by omega) (by omega)
    (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (by rw [hz₂]; exact Nat.two_pow_pos _))
    fun t ⟨hv, ho, k₃⟩ => ⟨?_, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · rw [show 2 * w + 2 = (wp + wq + 2) + (2 * w - wp - wq) by omega, wv_add, hv, hz₂,
      ho.wv (Or.inr (Nat.le_refl _)) (by omega), hm₂, wv_zero (n := 2 * w - wp - wq) fun k hk => by
        rw [Nat.add_assoc, ← Nat.mul_add]; exact hz₁ _ (by omega), Nat.mul_zero, Nat.add_zero, Nat.zero_add,
      ho₁.wv (Or.inr (by omega)) (by omega), ho₁.wv (Or.inr (by omega)) (by omega)]
  · rw [hm₂] at ho
    exact ho₁.trans (ho.mono (Nat.le_refl _) (by omega))

/-- `finish`'s copy of `m_q` (`q`'s `aY`) into the modulus' accumulator. -/
def finishCopy : List Instr :=
  [.mov .rax (.mem (hdr Crt.sWsQ)), .mov .rsi (.mem (Crt.ws .rax (sArr aY))), .mov .r12 (.mem (Crt.ws .rax sW)),
    .mov .rbx (.mem (hdr (sArr aAcc)))]

/-- The first steps of `finish`: `m_q + h q` into the modulus' accumulator. -/
def finishSum : List (Prog isa) :=
  Crt.zeroAccs ++ ([.block finishCopy, copyWords, .block (rowsHdr aY), Crt.mulRows] : List (Prog isa))

theorem finish_eq : Crt.finish = finishSum ++ Crt.finish.drop 6 := rfl

/-- `m_q + h q` (`m_q` in `q`'s `aY`, `h` in `p`'s) into the modulus'
accumulators (`2 w + 2` words). -/
theorem finishSum_ok {s : State} {B : Addr} {Z w op oq wp wq : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hw' : w < 2 ^ 29)
    (hp : word s.mem B (8 * Crt.sWsP) = off B op) (hq : word s.mem B (8 * Crt.sWsQ) = off B oq)
    (hpw : word s.mem (off B op) (8 * sW) = BitVec.ofNat 64 wp)
    (hqw : word s.mem (off B oq) (8 * sW) = BitVec.ofNat 64 wq)
    (hpy : word s.mem (off B op) (8 * sArr aY) = off B (op + slot wp aY))
    (hqy : word s.mem (off B oq) (8 * sArr aY) = off B (oq + slot wq aY))
    (hqa : word s.mem (off B oq) (8 * sArr aN) = off B (oq + slot wq aN))
    (hlo : slot w 8 ≤ op) (hop : op + slot wp 8 + tabBytes wp ≤ oq) (hoq : oq + slot wq 8 + tabBytes wq ≤ Z)
    (hwp : 1 ≤ wp) (hwp' : wp ≤ w) (hwq : 1 ≤ wq) (hwq' : wq ≤ w) :
    WP isa (seqs finishSum) s fun t =>
      wv t.mem B (slot w aAcc) (2 * w + 2) = wv s.mem B (oq + slot wq aY) wq +
        wv s.mem B (op + slot wp aY) wp * wv s.mem B (oq + slot wq aN) wq ∧
      Outside B (slot w aAcc) (8 * (2 * w + 2)) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hA := accs_le w
  have h8 := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have hpY := slot_le (w := wp) (show aY < 8 by decide)
  have hqY := slot_le (w := wq) (show aY < 8 by decide)
  have hqN := slot_le (w := wq) (show aN < 8 by decide)
  have hpS := hdr_lt_slot wp 8 (show 31 < 32 by decide)
  have hqS := hdr_lt_slot wq 8 (show 31 < 32 by decide)
  have eW : sW = 6 := rfl
  have eN : sArr aN = 8 := rfl
  have eY : sArr aY = 14 := rfl
  refine wp_seqs_append (by simp [Crt.zeroAccs]) (by simp)
    (WP.mono (zeroAccs_ok hg (by omega) (by omega)) fun s₁ ⟨hz₁, ho₁, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  have hh : ∀ i < 32, word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    ho₁.word (Or.inl (by have := hdr_lt_slot w aAcc hi; omega)) (by omega)
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hg.rdi
  have hl : ∀ i < 32, InRegions (s₁.rd ++ s₁.wr) (off B (8 * i)) 8 := fun i hi => hs₁.ld (by omega)
  have hlq : ∀ i < 32, InRegions (s₁.rd ++ s₁.wr) (off (off B oq) (8 * i)) 8 := fun i hi =>
    (hs₁.sub (o := oq) (n := slot wq 8) (by omega) (by omega)).ld (by omega)
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.rax, .rsi, .r12, .rbx] (Q := fun t =>
      t.gpr .rsi = off B (oq + slot wq aY) ∧ t.gpr .r12 = BitVec.ofNat 64 wq ∧
      t.gpr .rbx = off B (slot w aAcc) ∧ t.mem = s₁.mem)
    (by
      unfold finishCopy
      xrun [State.ea, hdr, Crt.ws, hdi₁, hdrOff, hl Crt.sWsQ (by decide), hl (sArr aAcc) (by decide),
        (hh _ (by decide)).trans hq, (hh _ (by decide)).trans (hg.hdr.harr aAcc (by decide)),
        hlq (sArr aY) (by decide), hlq sW (by decide), (word_above ho₁ (by omega) (by omega)).trans hqy,
        (word_above ho₁ (by omega) (by omega)).trans hqw]) rfl)
    fun s₂ ⟨⟨hsi, h12, hbx, hm₂⟩, k₂⟩ => ?_)
  have hs₂ := hs₁.congr k₂.2.2
  refine WP.seq (WP.mono (copyWords_ok hsi hbx h12 hwq (by omega) (by omega)
    (fun j hj => hs₂.ld (by omega)) (fun j hj => hs₂.st (by omega))
    (fun j hj b hb => by rw [ofs_off B (by omega)]; omega)) fun s₃ ⟨hc₃, _, ho₃, k₃⟩ => ?_)
  have hs₃ := hs₂.congr k₃.2.2
  rw [hm₂] at hc₃ ho₃
  have hh₃ : ∀ i < 32, word s₃.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    (ho₃.word (Or.inl (by have := hdr_lt_slot w aAcc hi; omega)) (by omega)).trans (hh i hi)
  have hab : ∀ {o d : Nat}, slot w 8 ≤ o → o + d + 8 ≤ 2 ^ 64 → word s₃.mem (off B o) d = word s.mem (off B o) d :=
    fun ho hd => (word_above ho₃ (by omega) hd).trans (word_above ho₁ (by omega) hd)
  refine WP.seq (WP.mono (rowsHdr_ok hs₃ ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans hdi₁))
    ((hh₃ _ (by decide)).trans (hg.hdr.harr aAcc (by decide))) ((hh₃ _ (by decide)).trans hp)
    ((hh₃ _ (by decide)).trans hq) ((hab (by omega) (by omega)).trans hpw)
    ((hab (by omega) (by omega)).trans hqw) ((hab (by omega) (by omega)).trans hpy)
    ((hab (by omega) (by omega)).trans hqa) (by decide) hlo hop hoq)
    fun s₄ ⟨h11, h10, h9, h12', h8', hm₄, k₄⟩ => ?_)
  have hmid : ∀ k < 2 * w + 2 - wq, word s₃.mem B (slot w aAcc + 8 * wq + 8 * k) = 0 := fun k hk => by
    rw [ho₃.word (Or.inr (by omega)) (by omega), Nat.add_assoc, ← Nat.mul_add]; exact hz₁ _ (by omega)
  have hwvab : ∀ {d k : Nat}, slot w 8 ≤ d → d + 8 * k ≤ Z → wv s₃.mem B d k = wv s.mem B d k :=
    fun hd hk => (ho₃.wv (Or.inr (by omega)) (by omega)).trans (ho₁.wv (Or.inr (by omega)) (by omega))
  have hz₄ : wv s₄.mem B (slot w aAcc) (wp + wq + 2) = wv s.mem B (oq + slot wq aY) wq := by
    rw [hm₄, show wp + wq + 2 = wq + (wp + 2) by omega, wv_add, wv_zero (n := wp + 2) fun k hk => hmid k (by omega),
      Nat.mul_zero, Nat.add_zero, hc₃, ho₁.wv (Or.inr (by omega)) (by omega)]
  have h0 : wv s₄.mem B (slot w aAcc) (wp + wq + 2) < 2 ^ (64 * (wq + 1)) := by
    rw [hz₄]
    exact Nat.lt_of_lt_of_le (wv_lt _ _ _ _) (Nat.pow_le_pow_right (by decide) (by omega))
  refine WP.mono (mulRows_ok (hs₃.congr k₄.2.2) h11 h9 h10 h12' h8' hwp hwq (by omega) (by omega) (by omega)
    (by omega) (Or.inr (by omega)) (Or.inr (by omega)) h0)
    fun t ⟨hv, ho, k₅⟩ => ⟨?_, ?_, ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by decide)⟩
  · rw [show 2 * w + 2 = (wp + wq + 2) + (2 * w - wp - wq) by omega, wv_add, hv, hz₄,
      ho.wv (Or.inr (Nat.le_refl _)) (by omega), hm₄, wv_zero (n := 2 * w - wp - wq) fun k hk => by
        rw [show slot w aAcc + 8 * (wp + wq + 2) + 8 * k = slot w aAcc + 8 * wq + 8 * (wp + 2 + k) by omega]
        exact hmid _ (by omega), Nat.mul_zero, Nat.add_zero,
      hwvab (by omega) (by omega), hwvab (by omega) (by omega)]
  · rw [hm₄] at ho
    exact (ho₁.trans (ho₃.mono (Nat.le_refl _) (by omega))).trans (ho.mono (Nat.le_refl _) (by omega))

end VG.Proof.Bignum.X86_64
