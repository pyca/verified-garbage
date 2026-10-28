module
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowShared
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
public import VerifiedGarbage.Proof.Bignum.AArch64.WindowRawTriangle

import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedStep

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowShared
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep count_loop)
open VG.Proof.Bignum.AArch64.WindowFive (TableCtx)

structure LoopInv (s : State) (P : Addr) (w : Nat) (mi : BitVec 64) (X Xc j : Nat) (t : State) : Prop where
  ctx : TableCtx t P w mi X Xc
  value : wv t.mem P (slot w aY) w * (2^(64*w))^(2^j-1) % X =
    (wv s.mem P (slot w aY) w)^(2^j) % X
  bit : word t.mem P (8*Crt.sBit) = BitVec.ofNat 64 (5-j)
  hdr : ∀ i < 32, i ≠ Crt.sBit → word t.mem P (8*i) = word s.mem P (8*i)
  frame : Frm P (crtWinRanges w) s.mem t.mem
  keep : Keep WindowRaw.regs s t

theorem loop_step {s t : State} {P : Addr} {w j : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hw : 16 ≤ w) (hw' : w < 2^30) (hmod : w % 8 = 0) (hj : j < 5)
    (hI : LoopInv s P w mi X Xc j t) :
    WP isa VG.Impl.Rsa.AArch64.WindowShared.step t fun u =>
      LoopInv s P w mi X Xc (j+1) u ∧ ((u.gpr .x3).toNat ≠ 0 ↔ j+1 ≠ 5) := by
  refine WP.mono (step_ok hI.ctx hw hw' hmod hj hI.bit hI.value)
    fun u ⟨cu,hu,hb,h3,hh,hf,hk⟩ => ⟨?_,?_⟩
  · refine ⟨cu,?_,hb,fun i hi hb' => (hh i hi hb').trans (hI.hdr i hi hb'),
      hI.frame.trans hf,(hI.keep.trans hk).mono (by decide)⟩
    have he : 2*(2^j-1)+1 = 2^(j+1)-1 := by
      have := Nat.two_pow_pos j
      rw [Nat.pow_succ]
      omega
    have ep : (wv s.mem P (slot w aY) w ^ (2^j))^2 =
        wv s.mem P (slot w aY) w ^ (2^(j+1)) := by
      rw [← Nat.pow_mul,← Nat.pow_succ]
    rw [he,ep] at hu
    exact hu
  · rw [h3,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 5-(j+1) < 2^64 by omega)]
    omega

theorem squares_ok {s : State} {P : Addr} {w : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hw : 16 ≤ w) (hw' : w < 2^30) (hmod : w % 8 = 0)
    (hb : word s.mem P (8*Crt.sBit) = BitVec.ofNat 64 5) :
    WP isa VG.Impl.Rsa.AArch64.WindowShared.squares s fun t =>
      TableCtx t P w mi X Xc ∧
      wv t.mem P (slot w aY) w * (2^(64*w))^31 % X =
        (wv s.mem P (slot w aY) w)^32 % X ∧
      (∀ i < 32, i ≠ Crt.sBit → word t.mem P (8*i) = word s.mem P (8*i)) ∧
      Frm P (crtWinRanges w) s.mem t.mem ∧ Keep WindowRaw.regs s t := by
  have h0 : LoopInv s P w mi X Xc 0 s :=
    ⟨hc,by simp,hb,fun _ _ _ => rfl,Frm.refl _ _ _,Keep.refl _ _⟩
  exact WP.mono (count_loop (n := 5) (by decide) (LoopInv s P w mi X Xc)
    (fun j hj t hi => loop_step hw hw' hmod hj hi) h0)
    fun _ hi => ⟨hi.ctx,hi.value,hi.hdr,hi.frame,hi.keep⟩

end VG.Proof.Bignum.AArch64.WindowShared
