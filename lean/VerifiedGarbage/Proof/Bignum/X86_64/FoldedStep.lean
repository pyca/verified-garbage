import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCounter

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

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
      t.zf = some (decide (n-1 = 0)) ∧
      Frm B (expRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hbound : B.toNat + slot w 8 ≤ 2^64 := by have := hc.good.scr.nowrap; omega
  unfold Folded.squareStep
  refine WP.seq (WP.mono (M.mm_ok hc.good hZ hw hw' (o := aY) (a := aY) (b := aY)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hc.inv (by rw [hc.n]; exact hY)) fun a ⟨ga,ya,ea,fa,ka⟩ => ?_)
  rw [hc.n] at ya ea
  have ca := hc.of_arrays ga hZ (by omega) fa
  have va := VG.Proof.Bignum.mont_sq hR hy ea
  have countA : word a.mem B (8*sI) = BitVec.ofNat 64 n := by
    rw [fa.hslot (by decide)]; exact hcount
  refine WP.mono (next_ok ga hZ hn hn' countA) fun t ⟨mt,zt,kt⟩ => ?_
  have yt : wv t.mem B (slot w aY) w = wv a.mem B (slot w aY) w := by
    rw [mt, hdrStore_wv (i := sI) (j := aY) _ _ _ (by decide) (by decide) hbound]
  refine ⟨ExpCtx.store ca hZ (i := sI) (by decide) (by decide) mt kt.2.2
      ((kt.gpr (by decide)).trans ga.rdi), yt ▸ ya, ?_, ?_, zt, ?_,
    (ka.trans kt).mono (by decide)⟩
  · rw [yt]; exact va
  · rw [mt, word_writeW_self]
  · refine (Frm.of_arrays fa (by simp [expRanges,bitRanges])).trans ?_
    rw [mt]
    exact Frm.of_outside (writeW_outside a.mem B _ (d := 8*sI)
      (by have := ga.scr.nowrap; have := hdr_lt_slot w 8 (show sI < 32 by decide); omega))
      (by simp [expRanges])

end VG.Proof.Bignum.X86_64.FoldedPublic
