import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalStep
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8TileEdges

/-! ## AdxSquareRedcLoop -/
section

/-! The invariant of Montgomery reduction of an unreduced square. -/

namespace VG.Proof.Bignum.X86_64.AdxSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

structure RedcInv (s₀ : State) (B : Addr) (Z w : Nat) (i : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rdx, .rax, .rsi, .r11, .r12, .r13, .r15, .rcx, .r14, .rbx, .r10, .r8] s₀ t
  r8 : t.gpr .r8 = off B (slot w aAcc + 16 + 8 * i)
  carry : (t.gpr .r10).toNat ≤ 1
  out : Outside B (slot w aAcc + 16) (16 * w) s₀.mem t.mem
  val : ∃ q < 2 ^ (64 * i),
    2 ^ (64 * i) * (wv t.mem B (slot w aAcc + 16 + 8 * i) (2 * w - i) +
      2 ^ (64 * w) * (t.gpr .r10).toNat) =
      wv s₀.mem B (slot w aAcc + 16) (2 * w) + q * wv s₀.mem B (slot w aN) w

/-- A new radix digit extends the accumulated cancellation multiplier. -/
theorem digit_bound {q P u : Nat} (hq : q < P) (hu : u < 2 ^ 64) : q + P * u < P * 2 ^ 64 := by
  have h := Nat.mul_le_mul_left P (show u ≤ 2 ^ 64 - 1 by omega)
  rw [Nat.mul_sub, Nat.mul_one] at h
  omega

theorem redcStep_ok {s₀ t : State} {B : Addr} {Z w i : Nat} {minv : BitVec 64}
    (hdi : s₀.gpr .rdi = B) (hH : Hdr s₀.mem B w minv) (hZ : slot w 8 ≤ Z)
    (h9 : s₀.gpr .r9 = off B (slot w aN)) (hbp : s₀.gpr .rbp = BitVec.ofNat 64 w)
    (hw1 : 2 ≤ w) (hw : w < 2 ^ 31) (hi : i < w)
    (hinv : ((word s₀.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hI : RedcInv s₀ B Z w i t) :
    WP isa AdxSquare.redcRow t fun t' => t'.zf = some (decide (i + 1 = w)) ∧ RedcInv s₀ B Z w (i + 1) t' := by
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
  refine WP.mono (redcRow_ok (n := 2 * w - i) hI.scr ((kp.gpr (by decide)).trans hdi) (hH.of_outside hI.out hh) hZ hI.r8
    ((kp.gpr (by decide)).trans h9) ((kp.gpr (by decide)).trans hbp) hw1 hw (by omega) (by omega)
    (by omega) (by omega) (by rw [hN0]; exact hinv)) fun t' ⟨u, hu, hv, hc, ho, h8', hz, kt⟩ => ⟨?_, ?_⟩
  · rw [hz]
    congr 1
    exact decide_eq_decide.mpr (by unfold slot aAcc aTmp; omega)
  rw [hN, show slot w aAcc + 16 + 8 * i + 8 = slot w aAcc + 16 + 8 * (i + 1) by omega,
    show 2 * w - i - 1 = 2 * w - (i + 1) by omega] at hv
  refine ⟨hI.scr.congr kt.2.2, (kp.trans kt).mono (by decide), ?_, hc hI.carry, ?_, ?_⟩
  · rw [h8']; congr 1
  · exact hI.out.trans (ho.mono (o' := slot w aAcc + 16) (n' := 16 * w) (by omega) (by omega))
  · obtain ⟨q, hq, heq⟩ := hI.val
    refine ⟨q + 2 ^ (64 * i) * u, ?_, ?_⟩
    · rw [pow64_succ]
      exact digit_bound hq hu
    · rw [pow64_succ]
      grind

/-- Reduction's rows, starting with a zero high carry. -/
theorem redcRows_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z)
    (h8 : s.gpr .r8 = off B (slot w aAcc + 16))
    (h9 : s.gpr .r9 = off B (slot w aN)) (hbp : s.gpr .rbp = BitVec.ofNat 64 w)
    (h10 : s.gpr .r10 = 0) (hw1 : 2 ≤ w) (hw : w < 2 ^ 31)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0) :
    WP isa (.loop AdxSquare.redcRow .ne) s (RedcInv s B Z w w) := by
  refine wp_upto (a := 0) (N := w) (by omega) (RedcInv s B Z w)
    (fun i _ hi t h => redcStep_ok hdi hH hZ h9 hbp hw1 hw hi hinv h) (fun _ h => h) ?_
  refine ⟨hs, Keep.refl _ _, by simpa using h8, by simp [h10], Outside.refl _ _ _ _, 0, by decide, ?_⟩
  simp [h10]

end VG.Proof.Bignum.X86_64.AdxSquare

end

/-! ## AdxSquareRedc -/
section

/-! Montgomery reduction of the square, before its final subtraction. -/

namespace VG.Proof.Bignum.X86_64.AdxSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem redcSetup_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) :
    WP isa (.block AdxSquare.redcSetup) s fun t =>
      t.gpr .r8 = off B (slot w aAcc + 16) ∧ t.gpr .r9 = off B (slot w aN) ∧
      t.gpr .rbp = BitVec.ofNat 64 w ∧ t.gpr .r10 = 0 ∧ t.mem = s.mem ∧ Keep [.r8, .r9, .rbp, .r10] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  refine WP.mono (WP.keep [.r8, .r9, .rbp, .r10] (Q := fun t =>
      t.gpr .r8 = off B (slot w aAcc + 16) ∧ t.gpr .r9 = off B (slot w aN) ∧
      t.gpr .rbp = BitVec.ofNat 64 w ∧ t.gpr .r10 = 0 ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, k⟩
  unfold AdxSquare.redcSetup
  xrun [State.ea, hdr, hdi, hdrOff, hl (sArr aAcc) (by decide), hl (sArr aN) (by decide), hl sW (by decide),
    hH.harr aAcc (by decide), hH.harr aN (by decide), hH.hw, off_add16]

theorem redcFinish_ok {s : State} {B : Addr} {Z e w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B e) (hbp : s.gpr .rbp = BitVec.ofNat 64 w) (hZ : e + 8 * (w + 2) ≤ Z) :
    WP isa (.block AdxSquare.redcFinish) s fun t =>
      wv t.mem B e (w + 2) = wv s.mem B e w + 2 ^ (64 * w) * (s.gpr .r10).toNat ∧
      Outside B (e + 8 * w) 16 s.mem t.mem ∧ Keep [.rax] s t := by
  have hn := hs.nowrap
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.mem = (s.mem.writeW (off B (e + 8 * w)) (s.gpr .r10)).writeW (off B (e + 8 * w + 8)) (0 : BitVec 64)) ?_ rfl)
    fun t ⟨hm, kt⟩ => ?_
  · unfold AdxSquare.redcFinish
    xrun [State.ea, ix, addr0 h8 hbp, addr8 h8 hbp,
      hs.st (show e + 8 * w + 8 ≤ Z by omega), hs.st (show e + 8 * w + 8 + 8 ≤ Z by omega)]
    rfl
  · obtain ⟨hv, ho⟩ := write2 s.mem B (e + 8 * w) (s.gpr .r10) 0 (by omega)
    rw [← hm] at hv ho
    refine ⟨?_, ho, kt⟩
    rw [wv_add, hv, ho.wv (by omega) (by omega)]
    simp

/-- REDC's exact relation: the result times the Montgomery radix is the
input plus a multiple `q < R` of the modulus. -/
theorem redc_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hw1 : 2 ≤ w) (hw : w < 2 ^ 31)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0) :
    WP isa AdxSquare.redc s fun t =>
      (∃ q < 2 ^ (64 * w), 2 ^ (64 * w) * wv t.mem B (slot w aTmp) (w + 2) =
        wv s.mem B (slot w aAcc + 16) (2 * w) + q * wv s.mem B (slot w aN) w) ∧
      Outside B (slot w aAcc + 16) (8 * (2 * w + 2)) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have hA := slot_le (w := w) (show aTmp < 8 by decide)
  have hAT : slot w aAcc + 16 + 8 * w = slot w aTmp := by unfold slot aAcc aTmp; omega
  unfold AdxSquare.redc
  refine WP.seq (WP.mono (redcSetup_ok hs hdi hH hZ) fun s₁ ⟨h8, h9, hbp, h10, hm₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (redcRows_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans hdi)
    (hm₁ ▸ hH) hZ h8 h9 hbp h10 hw1 hw (by rw [hm₁]; exact hinv)) fun s₂ hI => ?_)
  have h8₂ := hI.r8
  rw [hAT] at h8₂
  have k12 := k₁.trans hI.keep
  refine WP.mono (redcFinish_ok hI.scr h8₂ ((hI.keep.gpr (by decide)).trans hbp) (by omega))
    fun t ⟨hv, ho, kt⟩ => ?_
  obtain ⟨q, hq, heq⟩ := hI.val
  rw [hAT, show 2 * w - w = w by omega, hm₁] at heq
  have o₁ := hI.out
  rw [hm₁] at o₁
  refine ⟨⟨q, hq, ?_⟩, ?_, (k12.trans kt).mono (by decide)⟩
  · rw [hv]; exact heq
  · exact (o₁.mono (o' := slot w aAcc + 16) (n' := 8 * (2 * w + 2)) (Nat.le_refl _) (by omega)).trans
      (ho.mono (o' := slot w aAcc + 16) (n' := 8 * (2 * w + 2)) (by omega) (by omega))

end VG.Proof.Bignum.X86_64.AdxSquare

end

/-! ## AdxRotate8Edges -/
section

/-! The initial pending carry and the final two padding words. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem setup_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w mi) (hZ : slot w 8 ≤ Z) :
    WP isa (.block AdxRotate8.setup) s fun t =>
      t.gpr .rcx = off B (slot w aAcc + 16) ∧ word t.mem B (slot w aAcc) = 0 ∧
      Outside B (slot w aAcc) 8 s.mem t.mem ∧ Keep [.rcx, .rax] s t := by
  have hn := hs.nowrap
  have hA := slot_le (w := w) (show aAcc < 8 by decide)
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * sArr aAcc)) 8 :=
    hs.ld (by have := hdr_lt_slot w 8 (show sArr aAcc < 32 by decide); omega)
  have back : off B (slot w aAcc + 16) + BitVec.ofInt 64 (-16) = off B (slot w aAcc) := by
    rw [show BitVec.ofInt 64 (-16) = 0 - BitVec.ofNat 64 16 from rfl,
      Offset.add_ofNat_add_neg B (show 16 ≤ slot w aAcc + 16 by omega), Nat.add_sub_cancel]
  refine WP.mono (WP.keep [.rcx, .rax] (Q := fun t =>
    t.gpr .rcx = off B (slot w aAcc + 16) ∧ t.mem = s.mem.writeW (off B (slot w aAcc)) (0 : BitVec 64)) ?_ rfl)
    fun t ⟨⟨hc, hm⟩, kt⟩ => ?_
  · unfold AdxRotate8.setup AdxRotate8.setupBases
    simp only [List.cons_append, List.nil_append]
    xrun [State.ea, hdr, AdxRotate8.tileCarry, hdi, hdrOff, hl, hH.harr aAcc (by decide),
      off_add16, back, hs.st (show slot w aAcc + 8 ≤ Z by omega)]
    rfl
  · rw [hm]
    exact ⟨hc, word_writeW_self _ _ _ _, writeW_outside _ _ _ (by omega), kt⟩

theorem finishSetup_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hc : s.gpr .rcx = off B (slot w aTmp)) :
    WP isa (.block AdxRotate8.finishSetup) s fun t =>
      t.gpr .r8 = off B (slot w aTmp) ∧ t.gpr .rbp = BitVec.ofNat 64 w ∧
      t.gpr .r10 = word s.mem B (slot w aTmp - 16) ∧ t.mem = s.mem ∧ Keep [.r8, .rbp, .r10] s t := by
  have hT := slot_le (w := w) (show aTmp < 8 by decide)
  have ht16 : 16 ≤ slot w aTmp := by unfold slot hdrBytes; omega
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * sW)) 8 :=
    hs.ld (by have := hdr_lt_slot w 8 (show sW < 32 by decide); omega)
  have back : off B (slot w aTmp) + BitVec.ofInt 64 (-16) = off B (slot w aTmp - 16) := by
    rw [show BitVec.ofInt 64 (-16) = 0 - BitVec.ofNat 64 16 from rfl]
    exact Offset.add_ofNat_add_neg B ht16
  refine WP.mono (WP.keep [.r8, .rbp, .r10] (Q := fun t =>
    t.gpr .r8 = off B (slot w aTmp) ∧ t.gpr .rbp = BitVec.ofNat 64 w ∧
      t.gpr .r10 = word s.mem B (slot w aTmp - 16) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, kt⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, kt⟩
  unfold AdxRotate8.finishSetup
  xrun [State.ea, hdr, AdxRotate8.tileCarry, hdi, hdrOff, hc, back, hl, hH.hw,
    hs.ld (show slot w aTmp - 16 + 8 ≤ Z by omega)]

theorem finish_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hc : s.gpr .rcx = off B (slot w aTmp)) :
    WP isa (.block AdxRotate8.finish) s fun t =>
      wv t.mem B (slot w aTmp) (w + 2) = wv s.mem B (slot w aTmp) w +
        2 ^ (64 * w) * (word s.mem B (slot w aTmp - 16)).toNat ∧
      Outside B (slot w aTmp + 8 * w) 16 s.mem t.mem ∧ Keep [.r8, .rbp, .r10, .rax] s t := by
  have hT := slot_le (w := w) (show aTmp < 8 by decide)
  change WP isa (.block (AdxRotate8.finishSetup ++ AdxSquare.redcFinish)) s _
  rw [WP.block_append_iff]
  refine WP.mono (finishSetup_ok hs hdi hH hZ hc) fun a ⟨h8, hp, hv, hm, ka⟩ => ?_
  refine WP.mono (AdxSquare.redcFinish_ok (hs.congr ka.2.2) h8 hp (by omega)) fun t ⟨vt, ot, kt⟩ => ?_
  rw [hm, hv] at vt
  rw [hm] at ot
  exact ⟨vt, ot, (ka.trans kt).mono (by simp)⟩
end VG.Proof.Bignum.X86_64.AdxRotate8

end
