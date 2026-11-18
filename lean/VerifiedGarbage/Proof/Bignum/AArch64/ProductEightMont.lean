module

public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCallMont
public import VerifiedGarbage.Impl.Bignum.AArch64.ProductDispatch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCallMont
meta import VerifiedGarbage.Impl.Bignum.AArch64.ProductDispatch
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtSetup
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCT
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtSetup
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcMont
public import VerifiedGarbage.Impl.Bignum.AArch64.SquareEightCall
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
meta import VerifiedGarbage.Impl.Bignum.AArch64.SquareEightCall
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect

/-! ### `Bignum.AArch64.ProductEightGuard`, which this module and modules that import it used -/

section

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
  refine WP.seq (WP.mono (guard_ok hg.scr hg.x0 hg.hdr hZ (by omega_using [hw]))
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
  have hdiv : w / 16 < 2 ^ 64 := by omega_using [hw]
  have hrem : w % 8 < 2 ^ 64 := by omega_using []
  by_cases hfast : 16 ≤ w
  · refine WP.ite true (by rw [eval_nonzero, h3, ne_zero_iff, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hdiv, decide_eq_true (show w / 16 ≠ 0 by omega_using [hfast])]) (fun _ => ?_) (by simp)
    by_cases hmod : w % 8 = 0
    · refine WP.ite true (by rw [eval_zero, h4, hmod]; rfl) (fun _ => ?_) (by simp)
      refine WP.mono (ProductMont.multiply_ok hgu.scr hgu.x0 hgu.hdr hZ hfast hw hmod
        ho ha hb ho1 ho2 hoN ha1 ha2 hb1 hb2 invu au) fun t ⟨ht, hv, hf, kt⟩ => ?_
      rw [hm] at ht hv hf
      exact ⟨⟨hg.scr.congr (kt.wr.trans ku.wr), ((ku.trans kt).gpr .x0 (by decide)).trans hg.x0,
        hf.hdr hg.hdr⟩, ht, hv, hf, (ku.trans kt).mono (by decide)⟩
    · exact WP.ite false (by rw [eval_zero, h4, eq_zero_iff, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hrem, decide_eq_false hmod]) (by simp) (fun _ => hSlow)
  · exact WP.ite false (by rw [eval_nonzero, h3, show w / 16 = 0 by omega_using [hfast]]; rfl)
      (by simp) (fun _ => hSlow)

end VG.Proof.Bignum.AArch64.ProductDispatch

end

end

/-! ### `Bignum.AArch64.ProductEightGuardCT`, which this module and modules that import it used -/

section

@[expose] public section
namespace VG.Proof.Bignum.AArch64.ProductDispatch
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.Bignum.AArch64.BlockedRedc
open VG.Proof.Bignum.AArch64.ProductEight (preparation finishRaw)
open VG.Proof.MlKem.AArch64 (eval_nonzero eval_zero)

theorem guarded_ct {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp)
    (hb1 : b ≠ Public.aAcc) (hb2 : b ≠ Public.aTmp) (hu : MmUse o a b)
    {hs hp hh hf he hv : VG.Taint.Hint VG.AArch64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.Square.squareSetup a)) hs).isSome = true)
    (hP : (taint.check (Taint.ofRegs [.x0, .x8, .x12, .x7]) (preparation a) hp).isSome = true)
    (hH : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.ProductEight.rowSetup a b)) hh).isSome = true)
    (hF : (taint.check (Taint.ofRegs [.x0]) (.block (finishRaw a)) hf).isSome = true)
    (hE : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.Square.finishBases o)) he).isSome = true)
    (hV : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x16 (sArr o)]) hv).isSome = true) :
    RelCT isa (Two GoodW) (VG.Impl.Bignum.AArch64.ProductDispatch.guarded o a b)
      (fun _ _ => True) := by
  unfold VG.Impl.Bignum.AArch64.ProductDispatch.guarded
  refine RelCT.seq (two_piece _ pins_goodW (by taint_decide) guard_ctx) ?_
  refine two_ite (Φ := GuardCtx) ?_ ?_ ?_
  · intro L s t hs ht
    rw [eval_nonzero, eval_nonzero, hs.width, ht.width]
  · refine two_ite ?_ ?_ ?_
    · intro L s t hs ht
      rw [eval_zero, eval_zero, hs.1.rem, ht.1.rem]
    · exact two_map id (fun _ _ h => ⟨h.1.1.good, guard_width h.1.1 h.1.2,
        guard_rem h.1.1 h.2⟩) (ProductEight.multiply_ct ho ha hb ha1 ha2 hb1 hb2 hS hP hH hF hE hV)
    · exact two_map id (fun _ _ h => h.1.1.good) (Mont.calledSquareEight.ct hu)
  · exact two_map id (fun _ _ h => h.1.good) (Mont.calledSquareEight.ct hu)

end VG.Proof.Bignum.AArch64.ProductDispatch

end

end

@[expose] public section
namespace VG.Proof.Bignum.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum

/-- The existing Montgomery contract with eight-limb non-square products.
The shared five-bit CRT window uses this interface; other callers retain
their existing multiplication. -/
def Mont.productEight : Mont where
  mm := VG.Impl.Bignum.AArch64.ProductDispatch.mm
  ok := by
    intro s B Z w minv hg hz hw hw' o a b ho ha hb d1 d2 d3 d4 d5 d6 hinv hB
    by_cases heq : a ≠ b ∧ o ≠ aN
    · unfold VG.Impl.Bignum.AArch64.ProductDispatch.mm
      rw [ite_eq_left heq]
      exact ProductDispatch.guarded_ok hg hz hw hw' ho ha hb d1 d2 heq.2 d3 d4 d5 d6 hinv hB
    · simpa only [VG.Impl.Bignum.AArch64.ProductDispatch.mm, ite_eq_right heq, Mont.calledSquareEight] using
        (Mont.calledSquareEight.ok hg hz hw hw' ho ha hb d1 d2 d3 d4 d5 d6 hinv hB)
  ct := by
    have slow (o a b : Nat) (h : MmUse o a b) :
        RelCT isa (Two GoodW) (VG.Impl.Bignum.AArch64.SquareEightCall.mm o a b) (fun _ _ => True) :=
      Mont.calledSquareEight.ct (o := o) (a := a) (b := b) h
    intro o a b h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    all_goals
      unfold VG.Impl.Bignum.AArch64.ProductDispatch.mm
      first
      | rw [ite_eq_left (by decide)]
        exact ProductDispatch.guarded_ct (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by simp [MmUse])
          (by taint_decide) (by taint_decide) (by taint_decide)
          (by taint_decide) (by taint_decide) (by taint_decide)
      | rw [ite_eq_right (by decide)]
        exact slow _ _ _ (by simp [MmUse])

end VG.Proof.Bignum.AArch64
