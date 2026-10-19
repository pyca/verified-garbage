module
public import VerifiedGarbage.Impl.Rsa.AArch64.Folded
public import VerifiedGarbage.Proof.Bignum.AArch64.PdExp

import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section
namespace VG.Proof.Bignum.AArch64.FoldedPublic
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

theorem finishTest_ok {s : State} {B : Addr} {Z w : Nat} {mi v : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    (hv : word s.mem B (8*sStarted) = v) :
    WP isa (.block [ldh .x3 sStarted, .subImm .x .x3 .x3 2]) s fun t =>
      isa.eval (.zero .x .x3) t = some (decide (v = 2#64)) ∧ t.mem = s.mem ∧ Keep [.x3] s t := by
  have bound : 8*sStarted+8 ≤ Z := by have := hdr_lt_slot w 8 (show sStarted < 32 by decide); omega
  refine WP.mono (WP.keep [.x3] (Q := fun t =>
    t.gpr .x3 = v - 2#64 ∧ t.mem = s.mem)
    (by brun [hg.x0, hdr_enc (show sStarted < 32 by decide), hg.scr.ld bound, hv]) rfl rfl rfl)
    fun t ⟨⟨hr,hm⟩,hk⟩ => ⟨?_,hm,hk⟩
  rw [eval_zero, hr]
  congr 1
  apply decide_eq_decide.mpr
  change (v - 2#64 = 0#64) ↔ v = 2#64
  rw [BitVec.sub_eq_iff_eq_add, BitVec.zero_add]

theorem finish_fast_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    (hv : word s.mem B (8*sStarted) = 2) :
    WP isa (Folded.finishFused M.mm) s fun t => t.mem = s.mem ∧ Keep [.x3] s t := by
  unfold Folded.finishFused
  refine WP.seq (WP.mono (finishTest_ok hg hZ hv) fun t ⟨ht,hm,hk⟩ => ?_)
  exact WP.ite true ht (fun _ => WP.block_nil ⟨hm,hk⟩) (by simp)

theorem finish_slow_ok (M : Mont) {s : State} {B : Addr} {Z w N X x E : Nat} {mi : BitVec 64}
    (hc : ExpCtx s B Z w mi N X) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2^31)
    (hR : Nat.Coprime (2^(64*w)) N) (hN : 1 < N)
    (hone : wv s.mem B (slot w aOne) w = 1) (hy : YSt s.mem B w N x E) :
    WP isa (Folded.finishFused M.mm) s fun t =>
      Good t B Z w mi ∧ wv t.mem B (slot w aY) w = x^E % N ∧
      Frm B (finRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Folded.finishFused
  refine WP.seq (WP.mono (finishTest_ok hc.good hZ hy.started) fun a ⟨ht,hm,ka⟩ => ?_)
  have hz : isa.eval (.zero .x .x3) a = some false := by
    rw [ht]
    by_cases he : E = 0 <;> simp only [he, ite_true, ite_false] <;> rfl
  refine WP.ite false hz (by simp) (fun _ => ?_)
  have ca := hc.mem hm ka (by decide)
  refine WP.mono (pFinish_ok (M := M) (x := x) (E := E) ca hZ hw hw' hR hN
    (by rw [hm]; exact hone) (by rw [hm]; exact hy)) fun t ⟨gt,yt,ft,kt⟩ => ?_
  rw [hm] at ft
  exact ⟨gt,yt,ft,(ka.trans kt).mono (by decide)⟩

end VG.Proof.Bignum.AArch64.FoldedPublic
