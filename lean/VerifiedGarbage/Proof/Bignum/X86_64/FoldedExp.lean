import VerifiedGarbage.Proof.Bignum.X86_64.FoldedLoop
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedPublic
import VerifiedGarbage.Proof.Bignum.X86_64.PdExp

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem input_preserved {B : Addr} {w : Nat} {m m' : Mem}
    (h : Frm B (pExpRanges w) m m') (hb : B.toNat + slot w 8 ≤ 2^64) :
    wv m' B (slot w aX) w = wv m B (slot w aX) w := by
  apply h.wv_eq
  · intro r hr
    simp only [pExpRanges,pBitRanges,bitRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [slot,hdrBytes,sI,sV,sBit,Precomputed.sStarted,sFn,aX,aAcc,aTmp,aY] <;> omega
  · have := slot_le (w := w) (show aX < 8 by decide); omega

theorem exp65537_factor_ok (M : Mont) {s : State} {B : Addr} {Z w N X x u : Nat} {mi : BitVec 64}
    (hc : ExpCtx s B Z w mi N X) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2^31)
    (hR : Nat.Coprime (2^(64*w)) N) (hX : X < N)
    (hx : X % N = x * 2^(64*w) % N)
    (hinput : wv s.mem B (slot w aX) w = u) :
    WP isa (Folded.exp65537 M.mm) s fun t =>
      Good t B Z w mi ∧ wv t.mem B (slot w aY) w = x^65536 * u % N ∧
      Frm B (pExpRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hb : B.toNat + slot w 8 ≤ 2^64 := by have := hc.good.scr.nowrap; omega
  unfold Folded.exp65537
  simp only [seqs]
  refine WP.seq (WP.mono (start_ok hc hZ (by omega) hw')
    fun a ⟨ca,ya,_,fa,ka⟩ => ?_)
  refine WP.seq (WP.mono (init_ok ca.good hZ) fun b ⟨mb,kb⟩ => ?_)
  have cb := ExpCtx.store ca hZ (i := sI) (by decide) (by decide) mb kb.2.2
    ((kb.gpr (by decide)).trans ca.good.rdi)
  have yb : wv b.mem B (slot w aY) w = X := by
    rw [mb,hdrStore_wv (i := sI) (j := aY) _ _ _ (by decide) (by decide) hb]; exact ya
  have countB : word b.mem B (8*sI) = 16 := by rw [mb,word_writeW_self]
  have fb : Frm B (pExpRanges w) a.mem b.mem := by
    rw [mb]
    exact Frm.of_outside (writeW_outside a.mem B (16 : BitVec 64) (d := 8*sI)
      (by have := hdr_lt_slot w 8 (show sI < 32 by decide); omega)) (by simp [pExpRanges])
  have fab : Frm B (pExpRanges w) s.mem b.mem :=
    (fa.mono (by simp [startRanges,pExpRanges,pBitRanges,bitRanges])).trans fb
  refine WP.seq (WP.mono (squares_ok M cb hZ hw hw' hR (by rw [yb]; exact hX)
    (by rw [yb]; exact hx) countB) fun c ic => ?_)
  have fc : Frm B (pExpRanges w) b.mem c.mem :=
    ic.frame.mono (by simp [expRanges,pExpRanges,pBitRanges,bitRanges])
  have fall := fab.trans fc
  have xc : wv c.mem B (slot w aX) w = u := (input_preserved fall hb).trans hinput
  refine WP.mono (final_factor_ok M ic.ctx.good hZ hw hw' ic.ctx.n ic.ctx.inv hR xc
    ic.reduced ic.value) fun t ⟨gt,yt,ft,kt⟩ => ?_
  rw [show (2 : Nat)^16 = 65536 by decide] at yt
  exact ⟨gt,yt,fall.trans (Frm.of_arrays ft (by simp [pExpRanges,pBitRanges,bitRanges])),
    (((ka.trans kb).trans ic.keep).trans kt).mono (by decide)⟩

end VG.Proof.Bignum.X86_64.FoldedPublic
