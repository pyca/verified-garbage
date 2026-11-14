module
public import VerifiedGarbage.Impl.Rsa.AArch64.Folded
public import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
import VerifiedGarbage.Proof.Bignum.AArch64.FoldedExp
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Bignum.FoldedPublic
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! ### `Bignum.AArch64.FoldedPublic`, which only this module used -/

section

/-! The last public-exponent multiplication also leaves Montgomery form. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.FoldedPublic
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- Keep the reduced accumulator on the right: the input need not be reduced,
including when an invalid signature will subsequently be masked out. -/
theorem final_factor_ok (M : Mont) {s : State} {B : Addr} {Z w N x u e : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2^31)
    (hN : wv s.mem B (slot w aN) w = N)
    (hi : ((word s.mem B (slot w aN)).toNat * mi.toNat + 1) % 2^64 = 0)
    (hR : Nat.Coprime (2^(64*w)) N)
    (hX : wv s.mem B (slot w aX) w = u)
    (hY : wv s.mem B (slot w aY) w < N)
    (hc : wv s.mem B (slot w aY) w % N = x^e * 2^(64*w) % N) :
    WP isa (M.mm aY aX aY) s fun t =>
      Good t B Z w mi ∧ wv t.mem B (slot w aY) w = x^e * u % N ∧
      Arrays B w [aAcc,aTmp,aY] s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (M.mm_ok hg hZ hw hw' (o := aY) (a := aX) (b := aY)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hi (by rw [hN]; exact hY)) fun t ⟨ht,lt,eq,frame,keep⟩ => ?_
  rw [hN] at lt eq
  rw [hX, Nat.mul_comm u] at eq
  have result := VG.Proof.Bignum.mont_final_factor hR hc eq
  rw [Nat.mod_eq_of_lt lt] at result
  exact ⟨ht,result,frame,keep⟩

end VG.Proof.Bignum.AArch64.FoldedPublic

end

end


@[expose] public section
namespace VG.Proof.Bignum.AArch64.FoldedPublic
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Precomputed
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem mark_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) :
    WP isa (.block [movi .x3 2, sth .x3 sStarted]) s fun t =>
      t.mem = s.mem.writeW (off B (8*sStarted)) (2 : BitVec 64) ∧ Keep [.x3] s t := by
  have bound : 8*sStarted+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sStarted < 32 by decide)
    omega_using [hZ, this]
  exact WP.keep [.x3] (by brun [hg.x0, hdr_enc (show sStarted < 32 by decide), hg.scr.st bound]; rfl)
    rfl rfl rfl

/-- The complete fixed-exponent path. The ordinary input remains unrestricted,
while every square and the final product retain a canonical second operand. -/
theorem fixedLoop_ok (M : Mont) {s : State} {B : Addr} {Z w N X x u : Nat} {mi : BitVec 64}
    (hc : ExpCtx s B Z w mi N X) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2^31)
    (hR : Nat.Coprime (2^(64*w)) N) (hX : X < N)
    (hx : X % N = x * 2^(64*w) % N)
    (hu : wv s.mem B (slot w aX) w = u) :
    WP isa (Folded.fixedLoop M.mm) s fun t =>
      ExpCtx t B Z w mi N X ∧ wv t.mem B (slot w aY) w = x^65536 * u % N ∧
      word t.mem B (8*sStarted) = 2 ∧
      Frm B (pExpRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hb : B.toNat + slot w 8 ≤ 2^64 := by have := hc.good.scr.nowrap; omega_using [hZ, this]
  change WP isa (seqs ([start, .block [movi .x3 16, sth .x3 sI],
    .loop (Folded.squareStep M.mm) (.nonzero .x .x3)] ++
    [M.mm aY aX aY, .block [movi .x3 2, sth .x3 sStarted]])) s _
  apply wp_seqs_append (by simp) (by simp)
  refine WP.mono (exp65536_ok M hc hZ hw hw' hR hX hx) fun a ⟨ca, ya, va, fa, ka⟩ => ?_
  have ua : wv a.mem B (slot w aX) w = u := (input_preserved fa hb).trans hu
  change WP isa (.seq (M.mm aY aX aY) (.block [movi .x3 2, sth .x3 sStarted])) a _
  refine WP.seq (WP.mono (final_factor_ok M ca.good hZ hw hw' ca.n ca.inv hR ua ya va)
    fun b ⟨gb, yb, fb, kb⟩ => ?_)
  have cb := ca.of_arrays gb hZ (by omega_using [hw]) fb
  refine WP.mono (mark_ok gb hZ) fun t ⟨hm, kt⟩ => ?_
  refine ⟨ExpCtx.store cb hZ (i := sStarted) (by decide) (by decide) hm kt.wr
    ((kt.gpr .x0 (by decide)).trans gb.x0), ?_, ?_, ?_, ((ka.trans kb).trans kt).mono (by decide)⟩
  · rw [hm, hdrStore_wv (i := sStarted) (j := aY) _ _ _ (by decide) (by decide) hb]; exact yb
  · rw [hm, word_writeW_self]
  · refine (fa.trans (Frm.of_arrays fb (by simp [pExpRanges,pBitRanges,bitRanges]))).trans ?_
    rw [hm]
    exact Frm.of_outside (writeW_outside b.mem B (2 : BitVec 64) (d := 8*sStarted)
      (by have := hdr_lt_slot w 8 (show sStarted < 32 by decide); omega_using [hb, this]))
      (by simp [pExpRanges,pBitRanges,bitRanges])

end VG.Proof.Bignum.AArch64.FoldedPublic
