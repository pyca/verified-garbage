module

public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcGuard
public import VerifiedGarbage.Impl.Bignum.AArch64.SquareEightCall
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCallMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcGuard
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcMont

@[expose] public section

namespace VG.Proof.Bignum.AArch64.ProductDispatch
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero ne_zero_iff eval_zero eq_zero_iff)
open VG.Proof.Bignum.AArch64.BlockedRedc

theorem guarded_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw1 : 2 ≤ w) (hw : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp)
    (hoN : o ≠ aN) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv s.mem B (slot w b) w < wv s.mem B (slot w aN) w) :
    WP isa (.seq (.block guard)
      (.ite (.nonzero .x .x3) (.ite (.zero .x .x4)
        (VG.Impl.Bignum.AArch64.ProductEight.multiply o a b)
        (VG.Impl.Bignum.AArch64.SquareEightCall.mm o a b))
        (VG.Impl.Bignum.AArch64.SquareEightCall.mm o a b))) s fun t =>
      Good t B Z w minv ∧ wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.seq (WP.mono (guard_ok hg.scr hg.x0 hg.hdr hZ (by omega))
    fun u ⟨⟨hm, h3, h4⟩, ku⟩ => ?_)
  have hgu : Good u B Z w minv :=
    ⟨hg.scr.congr ku.wr, (ku.gpr .x0 (by decide)).trans hg.x0, hm ▸ hg.hdr⟩
  have invu : ((word u.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hm]; exact hinv
  have au : wv u.mem B (slot w b) w < wv u.mem B (slot w aN) w := by rw [hm]; exact hB
  have hSlow := WP.mono (Mont.calledSquareEight.ok hgu hZ hw1 hw ho ha hb ho1 ho2 ha1 ha2 hb1 hb2 invu au)
    fun t ⟨hgt, ht, hv, hf, kt⟩ =>
      (show Good t B Z w minv ∧ wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
        wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
          wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
        Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t from by
        rw [hm] at ht hv hf
        exact ⟨hgt, ht, hv, hf, (ku.trans kt).mono (by decide)⟩)
  have hdiv : w / 16 < 2 ^ 64 := by omega
  have hrem : w % 8 < 2 ^ 64 := by omega
  by_cases hfast : 16 ≤ w
  · refine WP.ite true (by rw [eval_nonzero, h3, ne_zero_iff, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hdiv, decide_eq_true (show w / 16 ≠ 0 by omega)]) (fun _ => ?_) (by simp)
    by_cases hmod : w % 8 = 0
    · refine WP.ite true (by rw [eval_zero, h4, hmod]; rfl) (fun _ => ?_) (by simp)
      refine WP.mono (ProductMont.multiply_ok hgu.scr hgu.x0 hgu.hdr hZ hfast hw hmod
        ho ha hb ho1 ho2 hoN ha1 ha2 hb1 hb2 invu au) fun t ⟨ht, hv, hf, kt⟩ => ?_
      rw [hm] at ht hv hf
      exact ⟨⟨hg.scr.congr (kt.wr.trans ku.wr), ((ku.trans kt).gpr .x0 (by decide)).trans hg.x0,
        hf.hdr hg.hdr⟩, ht, hv, hf, (ku.trans kt).mono (by decide)⟩
    · exact WP.ite false (by rw [eval_zero, h4, eq_zero_iff, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hrem, decide_eq_false hmod]) (by simp) (fun _ => hSlow)
  · exact WP.ite false (by rw [eval_nonzero, h3, show w / 16 = 0 by omega]; rfl)
      (by simp) (fun _ => hSlow)

end VG.Proof.Bignum.AArch64.ProductDispatch
