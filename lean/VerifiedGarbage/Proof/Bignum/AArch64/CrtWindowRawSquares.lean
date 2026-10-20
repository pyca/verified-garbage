module
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable

import VerifiedGarbage.Proof.Bignum.CrtWindowRelation
import Mathlib.Data.Int.ModEq

/-! Montgomery scaling for arbitrary reduced accumulators, without a table-power assumption. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

theorem square_raw_ok (M : Mont) {s : State} {P : Addr} {w : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hw : 2 ≤ w) (hw' : w < 2 ^ 30)
    (hy : wv s.mem P (slot w aY) w < X) :
    WP isa (M.mm aY aY aY) s fun t => TableCtx t P w mi X Xc ∧
      wv t.mem P (slot w aY) w < X ∧
      wv t.mem P (slot w aY) w * 2 ^ (64 * w) % X =
        wv s.mem P (slot w aY) w * wv s.mem P (slot w aY) w % X ∧
      (∀ k < 32, word t.mem P (8 * k) = word s.mem P (8 * k)) ∧
      Frm P (crtWinRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (M.mm_ok (o := aY) (a := aY) (b := aY) hc.good (Nat.le_refl _) hw (by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
    (by rw [hc.n]; exact hy)) fun t ⟨_,ht,hm,ha,kt⟩ => ?_
  rw [hc.n] at ht hm
  have hf : Frm P (crtWinRanges w) s.mem t.mem := Frm.of_arrays ha (by simp [crtWinRanges])
  exact ⟨hc.of_win hf kt.wr (kt.gpr .x0 (by decide)),ht,hm,fun k hk => ha.hslot hk,hf,kt⟩

theorem squares_scaled_ok (M : Mont) (n : Nat) {s : State} {P : Addr} {w k A : Nat}
    {mi : BitVec 64} {X Xc : Nat} (hc : TableCtx s P w mi X Xc)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hy : wv s.mem P (slot w aY) w < X)
    (hv : wv s.mem P (slot w aY) w * (2 ^ (64 * w)) ^ k % X = A % X) :
    WP isa (seqs (List.replicate (n + 1) (M.mm aY aY aY))) s fun t =>
      TableCtx t P w mi X Xc ∧ wv t.mem P (slot w aY) w < X ∧
      wv t.mem P (slot w aY) w * (2 ^ (64 * w)) ^ (2 ^ (n + 1) * k + (2 ^ (n + 1) - 1)) % X =
        A ^ (2 ^ (n + 1)) % X ∧
      (∀ i < 32, word t.mem P (8 * i) = word s.mem P (8 * i)) ∧
      Frm P (crtWinRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  induction n generalizing s k A with
  | zero =>
    exact WP.mono (square_raw_ok M hc hw hw' hy) fun t ⟨ct,yt,ht,hh,hf,hk⟩ =>
      ⟨ct,yt,CrtWindowFive.square_scale ht hv,hh,hf,hk⟩
  | succ n ih =>
    show WP isa (.seq (M.mm aY aY aY) (seqs (List.replicate (n + 1) (M.mm aY aY aY)))) s _
    refine WP.seq (WP.mono (square_raw_ok M hc hw hw' hy) fun u ⟨cu,yu,hu,hhu,fu,ku⟩ => ?_)
    refine WP.mono (ih (k := 2 * k + 1) (A := A ^ 2) cu yu (CrtWindowFive.square_scale hu hv))
      fun t ⟨ct,yt,vt,hht,ft,kt⟩ => ?_
    refine ⟨ct,yt,?_,fun i hi => (hht i hi).trans (hhu i hi),fu.trans ft,(ku.trans kt).mono (by decide)⟩
    have hp : 0 < 2 ^ (n + 1) := Nat.two_pow_pos _
    have he : 2 ^ (n + 1) * (2 * k + 1) + (2 ^ (n + 1) - 1) =
        2 ^ (n + 1 + 1) * k + (2 ^ (n + 1 + 1) - 1) := by
      rw [Nat.pow_succ 2 (n + 1), Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc]
      omega
    rw [he] at vt
    have ep : (A ^ 2) ^ (2 ^ (n + 1)) = A ^ (2 ^ (n + 1 + 1)) := by
      rw [← Nat.pow_mul, Nat.mul_comm 2, ← Nat.pow_succ]
    rw [ep] at vt
    exact vt

end VG.Proof.Bignum.AArch64.WindowFive
