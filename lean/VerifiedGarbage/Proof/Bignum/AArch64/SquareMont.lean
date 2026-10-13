module

public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCorrect
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Omega
meta import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.Omega

/-! The optimized implementation satisfies the unchanged Montgomery interface. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.Square
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero ne_zero_iff)

theorem guarded_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw1 : 2 ≤ w) (hw : w < 2 ^ 31)
    {o a : Nat} (ho : o < 8) (ha : a < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat*minv.toNat+1) % 2 ^ 64 = 0)
    (hA : wv s.mem B (slot w a) w < wv s.mem B (slot w aN) w) :
    WP isa (.seq (.block VG.Impl.Bignum.AArch64.Square.guard)
      (.ite (.nonzero .x .x3) (VG.Impl.Bignum.AArch64.Square.square o a) (Public.basicMm o a a))) s fun t =>
      Good t B Z w minv ∧ wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w*2 ^ (64*w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w*wv s.mem B (slot w a) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.seq (WP.mono (guard_ok hg.scr hg.x0 hg.hdr hZ (by omega))
    fun u ⟨⟨hm, _, h3⟩, ku⟩ => ?_)
  have hgu : Good u B Z w minv :=
    ⟨hg.scr.congr ku.wr, (ku.gpr .x0 (by decide)).trans hg.x0, hm ▸ hg.hdr⟩
  have invu : ((word u.mem B (slot w aN)).toNat*minv.toNat+1) % 2 ^ 64 = 0 := by rw [hm]; exact hinv
  have au : wv u.mem B (slot w a) w < wv u.mem B (slot w aN) w := by rw [hm]; exact hA
  have hdiv : w/8 < 2 ^ 64 := by omega
  by_cases hfast : 8 ≤ w
  · have hn : w/8 ≠ 0 := by omega
    refine WP.ite true (by rw [eval_nonzero, h3, ne_zero_iff, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hdiv, decide_eq_true hn]) (fun _ => ?_) (by simp)
    refine WP.mono (square_ok hgu.scr hgu.x0 hgu.hdr hZ hw1 hw ho ha ho1 ho2 ha1 ha2 invu au)
      fun t ⟨ht, hv, hf, kt⟩ => ?_
    rw [hm] at ht hv hf
    exact ⟨⟨hg.scr.congr (kt.wr.trans ku.wr), ((ku.trans kt).gpr .x0 (by decide)).trans hg.x0,
      hf.hdr hg.hdr⟩, ht, hv, hf, (ku.trans kt).mono (by decide)⟩
  · have hn : w/8 = 0 := by omega
    refine WP.ite false (by rw [eval_nonzero, h3, hn]; rfl) (by simp) (fun _ => ?_)
    refine WP.mono (Mont.basic.mm_ok hgu hZ hw1 hw ho ha ha ho1 ho2 ha1 ha1 invu au ha2 ha2)
      fun t ⟨hg', ht, hv, hf, kt⟩ => ?_
    rw [hm] at ht hv hf
    exact ⟨hg', ht, hv, hf, (ku.trans kt).mono (by decide)⟩

end VG.Proof.Bignum.AArch64.Square

namespace VG.Proof.Bignum.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum

def Mont.square : Mont where
  mm := VG.Impl.Bignum.AArch64.Square.montMul
  ok := by
    intro s B Z w minv hg hz hw hw' o a b ho ha hb d1 d2 d3 d4 d5 d6 hinv hB
    by_cases heq : a = b
    · subst b
      simpa only [VG.Impl.Bignum.AArch64.Square.montMul, ite_eq_left rfl, ite_true] using
        (Square.guarded_ok hg hz hw hw' ho ha d1 d2 d3 d4 hinv hB)
    · simpa only [VG.Impl.Bignum.AArch64.Square.montMul, ite_eq_right heq, Mont.basic] using
        (Mont.basic.ok hg hz hw hw' ho ha hb d1 d2 d3 d4 d5 d6 hinv hB)
  ct := by
    intro o a b h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    all_goals
      unfold VG.Impl.Bignum.AArch64.Square.montMul
      first
      | rw [ite_eq_left rfl]
        exact Square.guarded_ct (by decide) (by decide) (by decide) (by decide)
          (by simp [MmUse]) (by taint_decide) (by taint_decide)
      | rw [ite_eq_right (by decide)]
        exact Mont.basic.ct (by simp [MmUse])

end VG.Proof.Bignum.AArch64
