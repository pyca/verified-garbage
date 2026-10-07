import VerifiedGarbage.Proof.Weierstrass.X86_64.PointTransfer

/-! Exact field values after the public odd-table store. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64

theorem nafTableFields_ok {K : WinCfg} {base : Addr} {size j m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hn : K.M.n=4)
    (hy : K.R.y=K.R.x+32) (hz : K.R.z=K.R.x+64)
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv K.M base size m Sl V E s)
    (hj : j<8) (hc : s.gpr .rbx=BitVec.ofNat 64 j)
    (ht : K.tbl<2^31) (hT : K.tbl+768≤size)
    (hD : ∀ x∈jacCoords (K.tblPt (j+1)), Sl x)
    (hQ : ∀ x∈jacCoords K.R, x∈V)
    (hSep : K.R.x+96≤K.tbl ∨ K.tbl+768≤K.R.x) :
    WP isa (.block (Naf.tableStore K)) s fun t =>
      ProgKeep K.M base (jacCoords (K.tblPt (j+1))) s t ∧
      Inv K.M base size m Sl (jacCoords (K.tblPt (j+1))++V)
        (pointTransferEnv E (K.tblPt (j+1)) K.R) t := by
  have hrz := hL.le K.R.z (hI.sl _ (hQ _ (by simp [jacCoords])))
  rw [hn,hz] at hrz
  refine WP.mono (nafTableStore_ok hI.scr hj hc ht hT (by omega) hSep)
    fun t ⟨hv,hk,ho⟩ => hI.transferPointFields hL hn ?_ ?_ hD hQ ?_ ?_ ?_ hk ?_
  · simp only [WinCfg.tblPt,hn]
  · simp only [WinCfg.tblPt,hn]
  · simpa only [hn,WinCfg.tblPt,Nat.add_sub_cancel,Nat.mul_zero,Nat.add_zero,
      show 24*4=96 from rfl] using hv 0 (by decide)
  · simpa only [hn,hy,WinCfg.tblPt,Nat.add_sub_cancel,Nat.mul_one,
      show 24*4=96 from rfl,show 8*4=32 from rfl] using hv 1 (by decide)
  · simpa only [hn,hz,WinCfg.tblPt,Nat.add_sub_cancel,
      show 24*4=96 from rfl,show 16*4=64 from rfl,show 32*2=64 from rfl] using hv 2 (by decide)
  · simpa only [WinCfg.tblPt,hn,Nat.add_sub_cancel,show 24*4=96 from rfl] using ho

end VG.Proof.Weierstrass.X86_64
