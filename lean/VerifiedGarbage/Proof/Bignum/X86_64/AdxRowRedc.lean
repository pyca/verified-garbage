import VerifiedGarbage.Proof.Bignum.X86_64.AdxRowRedcRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Edges

/-!
# Montgomery reduction by rows of eight-word blocks

`AdxRowRedc.redc` has `AdxRotate8.redc_ok`'s statement (`redc_ok`): its rows
are `AdxSquare.redcRow`'s with `AdxRowRedc.row` (`row_ok`) in place of
`AdxSquareWide.row`, and their invariant `AdxSquare.RedcInv`'s, but for its
value, which holds when `-m⁻¹` is right: memory and the registers are safe
whatever the header holds.
-/

namespace VG.Proof.Bignum.X86_64.AdxRowRedc

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Proof.Bignum.X86_64.AdxSquare (redcU wv_at_word redc_low digit_bound)

/-- A row: the window plus `u m` at its first word, the high carry moved up a
word; the first word cancelled when `-m⁻¹` is right. -/
theorem redcRow_ok {s : State} {B : Addr} {Z e w n : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (h8 : s.gpr .r8 = off B e)
    (h9 : s.gpr .r9 = off B (slot w aN)) (hbp : s.gpr .rbp = BitVec.ofNat 64 w)
    (hw1 : 0 < w) (hw8 : w % 8 = 0) (hw : w < 2 ^ 58) (hwn : w < n) (he : hdrBytes ≤ e)
    (heZ : e + 8 * n ≤ Z) (hsep : slot w aN + 8 * w ≤ e) :
    WP isa AdxRowRedc.redcRow s fun t =>
      wv t.mem B e n + 2 ^ (64 * w) * 2 ^ 64 * (t.gpr .r10).toNat =
        wv s.mem B e n + 2 ^ (64 * w) * (s.gpr .r10).toNat +
          (redcU (word s.mem B e) minv).toNat * wv s.mem B (slot w aN) w ∧
      (((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 → word t.mem B e = 0) ∧
      ((s.gpr .r10).toNat ≤ 1 → (t.gpr .r10).toNat ≤ 1) ∧
      Outside B e (8 * (w + 1)) s.mem t.mem ∧ t.gpr .r8 = off B (e + 8) ∧
      t.zf = some (decide (e + 8 = slot w aTmp)) ∧
      Keep [.rdx, .rax, .rsi, .r11, .r12, .r13, .r15, .rcx, .r14, .rbx, .r10, .r8] s t := by
  have hn := hs.nowrap
  have hN := slot_le (w := w) (show aN < 8 by decide)
  unfold AdxRowRedc.redcRow
  refine WP.seq (WP.mono (AdxSquare.redcHead_ok hs hdi hH h8 (by omega) hZ) fun s₁ ⟨hdx, hm₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (row_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans h8)
    ((k₁.gpr (by decide)).trans h9) ((k₁.gpr (by decide)).trans hbp) hw1 hw8 (by omega)
    (by omega) (by omega) (by omega)) fun s₂ ⟨hv, ho, h14, k₂⟩ => ?_)
  rw [hm₁, hdx] at hv
  rw [hm₁] at ho
  have k12 := k₁.trans k₂
  have top : word s₂.mem B (e + 8 * w) = word s.mem B (e + 8 * w) := ho.word (by omega) (by omega)
  have c10 : s₂.gpr .r10 = s.gpr .r10 := k12.gpr (by decide)
  refine WP.seq (WP.mono (AdxSquare.redcTail_ok (hs.congr k12.2.2) ((k12.gpr (by decide)).trans h8)
    h14 (by omega)) fun s₃ ⟨lo, hm₃, ht, hc, h8₃, k₃⟩ => ?_)
  rw [top, c10] at ht
  rw [c10] at hc
  have out₃ : Outside B (e + 8 * w) 8 s₂.mem s₃.mem := by
    rw [hm₃]; exact writeW_outside _ _ _ (by omega)
  have allout : Outside B e (8 * (w + 1)) s.mem s₃.mem :=
    (ho.mono (o' := e) (n' := 8 * (w + 1)) (Nat.le_refl _) (by omega)).trans
      (out₃.mono (o' := e) (n' := 8 * (w + 1)) (by omega) (by omega))
  have pre₃ : wv s₃.mem B e w = wv s₂.mem B e w := out₃.wv (by omega) (by omega)
  have top₃ : word s₃.mem B (e + 8 * w) = lo := by rw [hm₃, word_writeW_self]
  have high₃ : wv s₃.mem B (e + 8 * w + 8) (n - (w + 1)) =
      wv s.mem B (e + 8 * w + 8) (n - (w + 1)) := allout.wv (by omega) (by omega)
  have eq : wv s₃.mem B e n + 2 ^ (64 * w) * 2 ^ 64 * (s₃.gpr .r10).toNat =
      wv s.mem B e n + 2 ^ (64 * w) * (s.gpr .r10).toNat +
        (redcU (word s.mem B e) minv).toNat * wv s.mem B (slot w aN) w := by
    rw [wv_at_word _ _ _ _ _ hwn, wv_at_word s.mem _ _ _ _ hwn, pre₃, top₃, high₃]
    grind
  have k123 := k12.trans k₃
  refine WP.mono (VG.Proof.Bignum.X86_64.rowEnd_ok (hs.congr k123.2.2)
    ((k123.gpr (by decide)).trans hdi) (hH.of_outside allout he) hZ h8₃ (by omega))
    fun t ⟨hz, hm, h8', kt⟩ => ?_
  refine ⟨?_, fun hinv => ?_, ?_, ?_, h8', hz, (k123.trans kt).mono (by decide)⟩
  · rw [hm, kt.gpr (by decide)]; exact eq
  · rw [hm]
    exact (out₃.word (by omega) (by omega)).trans (redc_low hw1 hinv hv)
  · rw [kt.gpr (by decide)]; exact hc
  · rw [hm]; exact allout

/-- `AdxSquare.RedcInv`, its value for a right `-m⁻¹`. -/
structure RedcInv (s₀ : State) (B : Addr) (Z w : Nat) (mi : BitVec 64) (i : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rdx, .rax, .rsi, .r11, .r12, .r13, .r15, .rcx, .r14, .rbx, .r10, .r8] s₀ t
  r8 : t.gpr .r8 = off B (slot w aAcc + 16 + 8 * i)
  carry : (t.gpr .r10).toNat ≤ 1
  out : Outside B (slot w aAcc + 16) (16 * w) s₀.mem t.mem
  val : ((word s₀.mem B (slot w aN)).toNat * mi.toNat + 1) % 2 ^ 64 = 0 → ∃ q < 2 ^ (64 * i),
    2 ^ (64 * i) * (wv t.mem B (slot w aAcc + 16 + 8 * i) (2 * w - i) +
      2 ^ (64 * w) * (t.gpr .r10).toNat) =
      wv s₀.mem B (slot w aAcc + 16) (2 * w) + q * wv s₀.mem B (slot w aN) w

theorem redcStep_ok {s₀ t : State} {B : Addr} {Z w i : Nat} {minv : BitVec 64}
    (hdi : s₀.gpr .rdi = B) (hH : Hdr s₀.mem B w minv) (hZ : slot w 8 ≤ Z)
    (h9 : s₀.gpr .r9 = off B (slot w aN)) (hbp : s₀.gpr .rbp = BitVec.ofNat 64 w)
    (hw1 : 0 < w) (hw8 : w % 8 = 0) (hw : w < 2 ^ 58) (hi : i < w)
    (hI : RedcInv s₀ B Z w minv i t) :
    WP isa AdxRowRedc.redcRow t fun t' =>
      t'.zf = some (decide (i + 1 = w)) ∧ RedcInv s₀ B Z w minv (i + 1) t' := by
  have hn := hI.scr.nowrap
  have hA : slot w aAcc + 16 + 16 * w + 16 ≤ Z := by
    have := slot_le (w := w) (show aTmp < 8 by decide)
    unfold slot aAcc aTmp at *
    omega
  have hsep : slot w aN + 8 * (w + 2) ≤ slot w aAcc := by unfold slot aN aAcc; omega
  have hh : hdrBytes ≤ slot w aAcc + 16 := by unfold slot; omega
  have kp := hI.keep
  have hN : wv t.mem B (slot w aN) w = wv s₀.mem B (slot w aN) w := hI.out.wv (by omega) (by omega)
  have hN0 : word t.mem B (slot w aN) = word s₀.mem B (slot w aN) := hI.out.word (by omega) (by omega)
  refine WP.mono (redcRow_ok (n := 2 * w - i) hI.scr ((kp.gpr (by decide)).trans hdi)
    (hH.of_outside hI.out hh) hZ hI.r8 ((kp.gpr (by decide)).trans h9) ((kp.gpr (by decide)).trans hbp)
    hw1 hw8 hw (by omega) (by omega) (by omega) (by omega))
    fun t' ⟨hv, hlow, hc, ho, h8', hz, kt⟩ => ⟨?_, ?_⟩
  · rw [hz]
    congr 1
    exact decide_eq_decide.mpr (by unfold slot aAcc aTmp; omega)
  rw [hN] at hv
  rw [hN0] at hlow
  refine ⟨hI.scr.congr kt.2.2, (kp.trans kt).mono (by decide), ?_, hc hI.carry, ?_, ?_⟩
  · rw [h8']; congr 1
  · exact hI.out.trans (ho.mono (o' := slot w aAcc + 16) (n' := 16 * w) (by omega) (by omega))
  · intro hinv
    obtain ⟨q, hq, heq⟩ := hI.val hinv
    have low := hlow hinv
    have shifted : wv t'.mem B (slot w aAcc + 16 + 8 * i) (2 * w - i) =
        2 ^ 64 * wv t'.mem B (slot w aAcc + 16 + 8 * (i + 1)) (2 * w - (i + 1)) := by
      rw [show 2 * w - i = (2 * w - (i + 1)) + 1 by omega, wv_low, low,
        show slot w aAcc + 16 + 8 * i + 8 = slot w aAcc + 16 + 8 * (i + 1) by omega]
      simp
    rw [shifted] at hv
    refine ⟨q + 2 ^ (64 * i) * (redcU (word t.mem B (slot w aAcc + 16 + 8 * i)) minv).toNat, ?_, ?_⟩
    · rw [pow64_succ]
      exact digit_bound hq (BitVec.isLt _)
    · rw [pow64_succ]
      grind

/-- The rows, from a zero high carry. -/
theorem redcRows_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z)
    (h8 : s.gpr .r8 = off B (slot w aAcc + 16))
    (h9 : s.gpr .r9 = off B (slot w aN)) (hbp : s.gpr .rbp = BitVec.ofNat 64 w)
    (h10 : s.gpr .r10 = 0) (hw1 : 0 < w) (hw8 : w % 8 = 0) (hw : w < 2 ^ 58) :
    WP isa (.loop AdxRowRedc.redcRow .ne) s (RedcInv s B Z w minv w) := by
  refine wp_upto (a := 0) (N := w) (by omega) (RedcInv s B Z w minv)
    (fun i _ hi t h => redcStep_ok hdi hH hZ h9 hbp hw1 hw8 hw hi h) (fun _ h => h) ?_
  refine ⟨hs, Keep.refl _ _, by simpa using h8, by simp [h10], Outside.refl _ _ _ _, fun _ => ⟨0, by decide, ?_⟩⟩
  simp [h10]

/-- `AdxRotate8.redc_ok`'s statement. -/
theorem redc_ok {s : State} {B : Addr} {Z w n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hw : w = 8 * n) (hn : 0 < n) :
    WP isa AdxRowRedc.redc s fun t =>
      (((word s.mem B (slot w aN)).toNat * mi.toNat + 1) % 2 ^ 64 = 0 →
        ∃ q < 2 ^ (64 * w),
          2 ^ (64 * w) * wv t.mem B (slot w aTmp) (w + 2) =
            wv s.mem B (slot w aAcc + 16) (2 * w) + q * wv s.mem B (slot w aN) w) ∧
      Outside B (slot w aAcc) (16 * w + 32) s.mem t.mem ∧ Keep mmRegs s t := by
  have hbound := hs.nowrap
  have hA := slot_le (w := w) (show aTmp < 8 by decide)
  have hw58 : w < 2 ^ 58 := by
    have h8Z : slot w 8 ≤ 2 ^ 64 := by have := hs.nowrap; omega
    unfold slot at h8Z; omega
  have hAT : slot w aAcc + 16 + 8 * w = slot w aTmp := by unfold slot aAcc aTmp; omega
  unfold AdxRowRedc.redc
  refine WP.seq (WP.mono (AdxSquare.redcSetup_ok hs hdi hH hZ) fun s₁ ⟨h8, h9, hbp, h10, hm₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (redcRows_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans hdi)
    (hm₁ ▸ hH) hZ h8 h9 hbp h10 (by omega) (by omega) hw58) fun s₂ hI => ?_)
  have h8₂ := hI.r8
  rw [hAT] at h8₂
  have k12 := k₁.trans hI.keep
  refine WP.mono (AdxSquare.redcFinish_ok hI.scr h8₂ ((hI.keep.gpr (by decide)).trans hbp) (by omega))
    fun t ⟨hv, ho, kt⟩ => ?_
  have o₁ := hI.out
  rw [hm₁] at o₁
  refine ⟨fun hinv => ?_, ?_, (k12.trans kt).mono (by decide)⟩
  · obtain ⟨q, hq, heq⟩ := hI.val (by rw [hm₁]; exact hinv)
    rw [hAT, show 2 * w - w = w by omega, hm₁] at heq
    exact ⟨q, hq, by rw [hv]; exact heq⟩
  · exact (o₁.mono (o' := slot w aAcc) (n' := 16 * w + 32) (by omega) (by omega)).trans
      (ho.mono (o' := slot w aAcc) (n' := 16 * w + 32) (by omega) (by unfold slot aAcc aTmp at *; omega))

end VG.Proof.Bignum.X86_64.AdxRowRedc
