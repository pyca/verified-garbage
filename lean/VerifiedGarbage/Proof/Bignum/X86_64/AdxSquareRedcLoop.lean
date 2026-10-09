import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcRow

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
