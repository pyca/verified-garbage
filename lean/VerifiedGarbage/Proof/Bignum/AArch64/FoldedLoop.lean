module

public import VerifiedGarbage.Impl.Rsa.AArch64.Folded
public import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.AArch64.FoldedCounter
import VerifiedGarbage.Proof.Bignum.Math

/-! ### `Bignum.AArch64.FoldedStep`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Bignum.AArch64.FoldedPublic
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem squareStep_ok (M : Mont) {s : State} {B : Addr} {Z w N X x E n : Nat} {mi : BitVec 64}
    (hc : ExpCtx s B Z w mi N X) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2^31)
    (hR : Nat.Coprime (2^(64*w)) N)
    (hY : wv s.mem B (slot w aY) w < N)
    (hy : wv s.mem B (slot w aY) w % N = x^E * 2^(64*w) % N)
    (hn : 1 ≤ n) (hn' : n < 2^31)
    (hcount : word s.mem B (8*sI) = BitVec.ofNat 64 n) :
    WP isa (Folded.squareStep M.mm) s fun t =>
      ExpCtx t B Z w mi N X ∧ wv t.mem B (slot w aY) w < N ∧
      wv t.mem B (slot w aY) w % N = x^(2*E) * 2^(64*w) % N ∧
      word t.mem B (8*sI) = BitVec.ofNat 64 (n-1) ∧
      t.gpr .x3 = BitVec.ofNat 64 (n-1) ∧
      Frm B (pExpRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hbound : B.toNat + slot w 8 ≤ 2^64 := by have := hc.good.scr.nowrap; omega_using [hZ, this]
  unfold Folded.squareStep
  refine WP.seq (WP.mono (M.mm_ok hc.good hZ hw hw' (o := aY) (a := aY) (b := aY)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hc.inv (by rw [hc.n]; exact hY)) fun a ⟨ga,ya,ea,fa,ka⟩ => ?_)
  rw [hc.n] at ya ea
  have ca := hc.of_arrays ga hZ (by omega_using [hw]) fa
  have va := VG.Proof.Bignum.mont_sq hR hy ea
  have countA : word a.mem B (8*sI) = BitVec.ofNat 64 n := by
    rw [fa.hslot (by decide)]; exact hcount
  refine WP.mono (next_ok ga hZ hn hn' countA) fun t ⟨mt,zt,kt⟩ => ?_
  have yt : wv t.mem B (slot w aY) w = wv a.mem B (slot w aY) w := by
    rw [mt, hdrStore_wv (i := sI) (j := aY) _ _ _ (by decide) (by decide) hbound]
  refine ⟨ExpCtx.store ca hZ (i := sI) (by decide) (by decide) mt kt.wr
      ((kt.gpr .x0 (by decide)).trans ga.x0), yt ▸ ya, ?_, ?_, zt, ?_,
    (ka.trans kt).mono (by decide)⟩
  · rw [yt]; exact va
  · rw [mt, word_writeW_self]
  · refine (Frm.of_arrays fa (by simp [pExpRanges,pBitRanges,bitRanges])).trans ?_
    rw [mt]
    exact Frm.of_outside (writeW_outside a.mem B _ (d := 8*sI)
      (by have := ga.scr.nowrap; have := hdr_lt_slot w 8 (show sI < 32 by decide); omega_using [hbound, this]))
      (by simp [pExpRanges])

end VG.Proof.Bignum.AArch64.FoldedPublic

end

end

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
    (by omega_using [hi]) (by omega_using []) h.count) fun t ⟨ctx,lt,val,count,zf,frame,keep⟩ => ?_
  have hp : 2 * 2^i = 2^(i+1) := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [hp] at val
  refine ⟨?_,ctx,lt,val,?_,h.frame.trans frame,(h.keep.trans keep).mono (by decide)⟩
  · rw [zf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [])]
    omega_using [hi]
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
