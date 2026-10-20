module

public import VerifiedGarbage.Proof.Bignum.AArch64.WindowHelperContract
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRawCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareHelper
import Mathlib.Data.Int.ModEq

/-! Memory and arithmetic context for the callable window. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowHelper
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Spec.Rsa.Mont (numAt wOf wordAt arrAt aM minvWord)
open SquareHelper (numAt_eq)

theorem window_bytes (w : Nat) : slot w 8 + CrtWindowFive.tabBytes32 w = arrAt w 40 := by
  unfold slot hdrBytes CrtWindowFive.tabBytes32 arrAt Spec.Rsa.Mont.hdrBytes
  omega

/-- The contract implies the existing raw window's complete precondition. -/
theorem fn_context {s : State} (h : fnContract.pre s) :
    WindowFive.RawWindowPre
      ⟨s.gpr .x0, (s.gpr .x1).toNat * 8, 0, 0, wOf s.mem (s.gpr .x0)⟩ s := by
  obtain ⟨hr,hw,hn,hl,hi,hy,hd,ht⟩ := h
  obtain ⟨hl,h30,h40,hptr⟩ := hl
  have hs : (SquareHelper.fnContract 6).pre s := ⟨hr,hw,hn,hl,hi,hy⟩
  obtain ⟨g,h8,h2,_⟩ := SquareHelper.fn_good hs
  let P := s.gpr .x0
  let w := wOf s.mem P
  have hs8 := g.scr.sub (o := 0) (n := slot w 8) (by simpa using h8)
    (by unfold slot hdrBytes; omega)
  have hbig : slot w 8 + CrtWindowFive.tabBytes32 w ≤ (s.gpr .x1).toNat * 8 := by
    rw [window_bytes, Nat.mul_comm]
    exact h40
  have hsT := g.scr.sub (o := 0) (n := slot w 8 + CrtWindowFive.tabBytes32 w)
    (by simpa using hbig) (by unfold slot hdrBytes; omega)
  have gc : WindowFive.TableCtx s P w (wordAt s.mem P minvWord)
      (numAt s.mem P w aM) (wv s.mem P (slot w Crt.aXc) w) := by
    refine ⟨⟨?_,g.x0,g.hdr⟩,?_,?_,hi,rfl⟩
    · simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hs8
    · simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hsT
    · exact (numAt_eq _ _ _ _).symm
  have tab : CrtWindowFive.CTab s.mem P w (numAt s.mem P w aM) False 0 := by
    refine ⟨hptr,?_,fun h => h.elim⟩
    intro j hj
    rw [← numAt_eq]; exact ht j hj
  refine ⟨wordAt s.mem P minvWord, numAt s.mem P w aM,
    wv s.mem P (slot w Crt.aXc) w, Spec.Rsa.MontWindow.digit s.mem P,?_,?_,?_,h2,h30,hd,?_⟩
  · simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using gc
  · simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using tab
  · simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero, ← numAt_eq, Public.aY, w, P] using hy
  · simp [Spec.Rsa.MontWindow.digit, Spec.Rsa.MontWindow.digitWord,
      Crt.sNib, sFn, wordAt, word, off, P]

end VG.Proof.Bignum.AArch64.WindowHelper
