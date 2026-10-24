module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Basis
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Ring

/-! A public number of Montgomery squares advances a comb tooth by 2^rows. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep count_loop)

def squareRanges (w : Nat) : List (Nat × Nat) :=
 [(slot w 2,8*(w+2)),(slot w 3,8*(w+2)),(slot w 6,8*(w+2)),(8*sI,8)]

structure SquareInv (s0 : State) (p : Parameters) (E n j : Nat) (s : State) : Prop where
 power : Power p (E*2^j) s
 counter : Counter p.B (n-j) s
 frame : Frm p.B (squareRanges p.w) s0.mem s.mem
 keep : Keep mmRegs s0 s

theorem precomputeSquareStep (M : Mont) {s0 s : State} {p : Parameters} {E n j : Nat}
 (size : n<2^64) (inside : j<n) (h : SquareInv s0 p E n j s) :
 WP isa (.seq (M.mm 6 6 6) (.block [ldh .x3 sI,.subImm .x .x3 .x3 1,sth .x3 sI])) s fun t =>
 SquareInv s0 p E n (j+1) t ∧ ((t.gpr .x3).toNat≠0 ↔ j+1≠n) := by
 rw [WP.seq_iff]
 refine WP.mono (power_square M h.power) ?_
 rintro u ⟨power,arrays,rest⟩
 have counterU : Counter p.B (n-j) u := (arrays_header arrays (by decide)).trans h.counter
 refine WP.mono (decrement_control_ok power.good p.room (by decide : 16≤sI) (by decide : sI<32)
  (by omega) counterU) ?_
 rintro t ⟨good,counter,index,frame,keep⟩
 have powerT := power.after_header good frame (by decide : sI<32)
 have exponent : 2*(E*2^j)=E*2^(j+1) := by rw [Nat.pow_succ];ring
 rw [exponent] at powerT
 have remaining : n-j-1=n-(j+1) := by omega
 rw [remaining] at counter
 refine ⟨⟨powerT,counter,?_,((h.keep.trans rest).trans keep).mono (by simp [mmRegs])⟩,?_⟩
 · exact (h.frame.trans (Frm.of_arrays arrays (by simp [squareRanges]))).trans
    (Frm.of_outside frame (by simp [squareRanges]))
 · rw [index,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : n-j-1<2^64)]
   omega

theorem precomputeSquareLoop_ok (M : Mont) {s : State} {p : Parameters} {E n : Nat}
 (power : Power p E s) (counter : Counter p.B n s) (positive : 0<n) (size : n<2^64) :
 WP isa (.loop (.seq (M.mm 6 6 6) (.block [ldh .x3 sI,.subImm .x .x3 .x3 1,sth .x3 sI]))
  (.nonzero .x .x3)) s fun t =>
 Power p (E*2^n) t ∧ Counter p.B 0 t ∧ Frm p.B (squareRanges p.w) s.mem t.mem ∧ Keep mmRegs s t := by
 have init : SquareInv s p E n 0 s := by
  refine ⟨?_,?_,Frm.refl _ _ _,Keep.refl _ _⟩
  · simpa only [Nat.pow_zero,Nat.mul_one] using power
  · simpa only [Nat.sub_zero] using counter
 refine WP.mono (count_loop positive (SquareInv s p E n)
  (fun j hj s h => precomputeSquareStep M size hj h) init) ?_
 rintro t h
 exact ⟨h.power,by simpa only [Nat.sub_self] using h.counter,h.frame,h.keep⟩

end VG.Proof.Ffdh.AArch64.Cached
