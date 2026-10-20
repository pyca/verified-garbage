module
public import VerifiedGarbage.Impl.Rsa.AArch64.Folded
public import VerifiedGarbage.Proof.Bignum.AArch64.PdExp

import VerifiedGarbage.Proof.Bignum.AArch64.FoldedStep
import VerifiedGarbage.Proof.Framework.Contract

@[expose] public section

namespace VG.Proof.Bignum.AArch64.FoldedPublic
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure SquareInv (s₀ : State) (B : Addr) (Z w N X x : Nat) (mi : BitVec 64)
    (i : Nat) (s : State) : Prop where
  ctx : ExpCtx s B Z w mi N X
  reduced : wv s.mem B (slot w aY) w < N
  value : wv s.mem B (slot w aY) w % N = x^(2^i) * 2^(64*w) % N
  count : word s.mem B (8*sI) = BitVec.ofNat 64 (16-i)
  frame : Frm B (pExpRanges w) s₀.mem s.mem
  keep : Keep mmRegs s₀ s

theorem loopStep_ok (M : Mont) {s₀ s : State} {B : Addr} {Z w N X x i : Nat} {mi : BitVec 64}
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2^31)
    (hR : Nat.Coprime (2^(64*w)) N) (hi : i < 16)
    (h : SquareInv s₀ B Z w N X x mi i s) :
    WP isa (Folded.squareStep M.mm) s fun t =>
      ((t.gpr .x3).toNat ≠ 0 ↔ i+1 ≠ 16) ∧ SquareInv s₀ B Z w N X x mi (i+1) t := by
  refine WP.mono (squareStep_ok M h.ctx hZ hw hw' hR h.reduced h.value
    (by omega) (by omega) h.count) fun t ⟨ctx,lt,val,count,zf,frame,keep⟩ => ?_
  have hp : 2 * 2^i = 2^(i+1) := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [hp] at val
  refine ⟨?_,ctx,lt,val,?_,h.frame.trans frame,(h.keep.trans keep).mono (by decide)⟩
  · rw [zf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  · simpa only [Nat.sub_sub] using count

theorem squares_ok (M : Mont) {s : State} {B : Addr} {Z w N X x : Nat} {mi : BitVec 64}
    (hc : ExpCtx s B Z w mi N X) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2^31)
    (hR : Nat.Coprime (2^(64*w)) N)
    (hY : wv s.mem B (slot w aY) w < N)
    (hy : wv s.mem B (slot w aY) w % N = x * 2^(64*w) % N)
    (hcount : word s.mem B (8*sI) = 16) :
    WP isa (.loop (Folded.squareStep M.mm) (.nonzero .x .x3)) s
      (SquareInv s B Z w N X x mi 16) := by
  apply VG.Proof.MlKem.AArch64.count_loop (cr := .x3) (n := 16) (by decide)
    (SquareInv s B Z w N X x mi)
    (fun i hi t h => WP.mono (loopStep_ok M hZ hw hw' hR hi h) fun _ ⟨hr,hI⟩ => ⟨hI,hr⟩)
  exact ⟨hc,hY,by simpa only [Nat.pow_zero,Nat.pow_one] using hy,
    hcount,Frm.refl _ _ _,Keep.refl _ _⟩

end VG.Proof.Bignum.AArch64.FoldedPublic
