module
public import VerifiedGarbage.Impl.Bignum.AArch64.WindowSparse
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightTile

import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseHoles
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowSparse
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

private theorem zero_top (m : Mem) (B : Addr) (e n : Nat)
    (h : word m B (e+8*n) = 0) : wv m B e (n+1) = wv m B e n := by
  rw [wv,h,show (0 : BitVec 64).toNat = 0 from rfl,Nat.mul_zero,Nat.add_zero]

/-- A tile overwrites all sixteen words, so the previous contents are irrelevant. -/
theorem tile_ok {s : State} {B : Addr} {Z eA eT : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eA) (h16 : s.gpr .x16 = off B eT)
    (h7 : s.gpr .x7 = 0) (hA : eA+64 ≤ Z) (hT : eT+128 ≤ Z)
    (hsep : eA+64 ≤ eT ∨ eT+128 ≤ eA) :
    WP isa (.block (VG.Impl.Bignum.AArch64.WindowSparse.holes ++ SquareEight.code)) s fun t =>
      wv t.mem B eT 16 = Square.crossValue s.mem B eA 8 ∧
      Outside B eT 128 s.mem t.mem ∧ Keep SquareEight.codeRegs s t := by
  have hn := hs.nowrap
  apply WP.block_append
  refine WP.mono (holes_ok hs h16 h7 hT) fun u ⟨hz,hh,ho,ku⟩ => ?_
  refine WP.mono (SquareEight.code_ok (hs.congr ku.wr)
    ((ku.gpr _ (by decide)).trans h8) ((ku.gpr _ (by decide)).trans h16)
    hA (by omega) ((ku.gpr _ (by decide)).trans h7) (by simp [wv,hz]))
    fun t ⟨hv,ht,kt⟩ => ?_
  have high : word t.mem B (eT+120) = 0 := (ht.word (by omega) (by omega)).trans hh
  have inp : Square.crossValue u.mem B eA 8 = Square.crossValue s.mem B eA 8 := by
    apply Square.crossValue_congr
    intro j hj
    exact ho.word (by omega) (by omega)
  refine ⟨?_,ho.trans (ht.mono (by omega) (by omega)),(ku.trans kt).mono (by decide)⟩
  exact (zero_top t.mem B eT 15 (by simpa only [show 8*15=120 from rfl] using high)).trans
    (hv.trans inp)

/-- Extending the initialized prefix by one overwritten tile needs no whole-buffer clear. -/
theorem prefix_ok {s : State} {B : Addr} {Z eA eT i : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eA)
    (h16 : s.gpr .x16 = off B (eT+128*i)) (h7 : s.gpr .x7 = 0)
    (hA : eA+64 ≤ Z) (hT : eT+128*(i+1) ≤ Z)
    (hsep : eA+64 ≤ eT ∨ eT+128*(i+1) ≤ eA) :
    WP isa (.block (VG.Impl.Bignum.AArch64.WindowSparse.holes ++ SquareEight.code)) s fun t =>
      wv t.mem B eT (16*(i+1)) = wv s.mem B eT (16*i) +
        2^(64*(16*i))*Square.crossValue s.mem B eA 8 ∧
      Outside B eT (128*(i+1)) s.mem t.mem ∧ Keep SquareEight.codeRegs s t := by
  have hn := hs.nowrap
  refine WP.mono (tile_ok hs h8 h16 h7 hA (by omega) (by omega)) fun t ⟨hv,ho,kt⟩ => ?_
  refine ⟨?_,ho.mono (by omega) (by omega),kt⟩
  rw [show 16*(i+1) = 16*i+16 by omega,wv_add,
    ho.wv (d := eT) (k := 16*i) (by omega) (by omega),show eT+8*(16*i)=eT+128*i by omega,hv]

end VG.Proof.Bignum.AArch64.WindowSparse
