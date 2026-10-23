module
public import VerifiedGarbage.Impl.Bignum.AArch64.Square
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Bignum.Layout

import VerifiedGarbage.Proof.Bignum.AArch64.SquareRedcRow
import VerifiedGarbage.Proof.Bignum.AArch64.SquareRedcMath

/-! Fixed-count REDC keeps its frame for every inverse and its arithmetic for valid ones. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.Square
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure RedcInv (s₀ : State) (B : Addr) (Z w i : Nat) (minv : BitVec 64) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x8, .x13, .x14, .x16, .x17] s₀ t
  x8 : t.gpr .x8 = off B (slot w aAcc+16+8*i)
  x16 : 0 < i → t.gpr .x16 = off B (slot w aAcc+16+8*(i-1)+8*w)
  carry : (t.gpr .x5).toNat ≤ 1
  out : Outside B (slot w aAcc+16) (16*w) s₀.mem t.mem
  val : ((word s₀.mem B (slot w aN)).toNat*minv.toNat+1) % 2 ^ 64 = 0 →
    ∃ q < 2 ^ (64*i), 2 ^ (64*i)*
      (wv t.mem B (slot w aAcc+16+8*i) (2*w-i) + 2 ^ (64*w)*(t.gpr .x5).toNat) =
        wv s₀.mem B (slot w aAcc+16) (2*w) + q*wv s₀.mem B (slot w aN) w

theorem digit_bound {q P u : Nat} (hq : q < P) (hu : u < 2 ^ 64) : q+P*u < P*2 ^ 64 := by
  have h := Nat.mul_le_mul_left P (show u ≤ 2 ^ 64-1 by omega)
  rw [Nat.mul_sub, Nat.mul_one] at h
  omega

theorem redcStep_ok {s₀ t : State} {B : Addr} {Z w i : Nat} {minv : BitVec 64}
    (hZ : slot w 8 ≤ Z) (h10 : s₀.gpr .x10 = off B (slot w aN))
    (h12 : s₀.gpr .x12 = BitVec.ofNat 64 w) (h15 : s₀.gpr .x15 = minv)
    (h7 : s₀.gpr .x7 = 0) (hw1 : 2 ≤ w) (hw : w < 2 ^ 60) (hi : i < w)
    (hI : RedcInv s₀ B Z w i minv t) :
    WP isa VG.Impl.Bignum.AArch64.Square.redcRow t fun t' =>
      RedcInv s₀ B Z w (i+1) minv t' ∧ t'.gpr .x13 = t.gpr .x13 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have hA : slot w aAcc+16+16*w+16 ≤ Z := by
    have := slot_le (w := w) (show aTmp < 8 by decide)
    unfold slot aAcc aTmp at *; omega_arith
  have hsep : slot w aN+8*(w+2) ≤ slot w aAcc := by unfold slot aN aAcc; omega_arith
  have hN := hI.out.wv (d := slot w aN) (k := w) (by omega_arith) (by omega_arith)
  have hN0 := hI.out.word (d := slot w aN) (by omega_arith) (by omega_arith)
  have kp := hI.keep
  refine WP.mono (redcRow_analyze (n := 2*w-i) hI.scr hI.x8
    ((kp.gpr .x10 (by decide)).trans h10) ((kp.gpr .x12 (by decide)).trans h12)
    ((kp.gpr .x15 (by decide)).trans h15) ((kp.gpr .x7 (by decide)).trans h7)
    hw1 hw (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun t' ⟨u, hu, hv, hz, hc, ho, ht8, ht16, ht13, kt⟩ => ?_
  refine ⟨⟨hI.scr.congr kt.wr, (kp.trans kt).mono (by decide), ?_, ?_, hc hI.carry,
    hI.out.trans (ho.mono (o' := slot w aAcc+16) (n' := 16*w) (by omega_arith) (by omega_arith)), ?_⟩, ht13⟩
  · rw [ht8]; congr 1
  · intro _; rw [ht16]; congr 1
  · intro inv
    have invt : ((word t.mem B (slot w aN)).toNat*minv.toNat+1) % 2 ^ 64 = 0 := by
      rw [hN0]; exact inv
    have low := hz invt
    rw [show 2*w-i = (2*w-i-1)+1 by omega_arith, wv_low, low] at hv
    simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_add] at hv
    rw [hN, show slot w aAcc+16+8*i+8 = slot w aAcc+16+8*(i+1) by omega_arith,
      show 2*w-i-1 = 2*w-(i+1) by omega_arith] at hv
    obtain ⟨q, hq, heq⟩ := hI.val inv
    refine ⟨q+2 ^ (64*i)*u, ?_, ?_⟩
    · rw [pow64_succ]; exact digit_bound hq hu
    · rw [pow64_succ]
      grind

/-- The row loop is memory safe regardless of whether the inverse is correct. -/
theorem redcRows_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hZ : slot w 8 ≤ Z) (h8 : s.gpr .x8 = off B (slot w aAcc+16))
    (h10 : s.gpr .x10 = off B (slot w aN)) (h12 : s.gpr .x12 = BitVec.ofNat 64 w)
    (h15 : s.gpr .x15 = minv) (h7 : s.gpr .x7 = 0) (h5 : s.gpr .x5 = 0)
    (h13 : s.gpr .x13 = BitVec.ofNat 64 w) (hw1 : 2 ≤ w) (hw : w < 2 ^ 60) :
    WP isa (.loop VG.Impl.Bignum.AArch64.Square.redcRow (.nonzero .x .x13)) s
      (RedcInv s B Z w w minv) := by
  have h0 : RedcInv s B Z w 0 minv s := by
    refine ⟨hs, Keep.refl _ _, by simpa using h8, by omega, by simp [h5],
      Outside.refl _ _ _ _, ?_⟩
    intro _
    refine ⟨0, by decide, ?_⟩
    simp [h5]
  exact wp_countdown (N := w) (by omega) (by omega) (fun i => RedcInv s B Z w i minv)
    (fun i hi t hI _ => redcStep_ok hZ h10 h12 h15 h7 hw1 hw hi hI) h0 h13

end VG.Proof.Bignum.AArch64.Square
