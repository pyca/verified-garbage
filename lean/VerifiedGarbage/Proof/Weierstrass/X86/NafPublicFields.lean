import VerifiedGarbage.Proof.Weierstrass.X86.PointTransfer

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem nafPublicFields_ok {F : Spec.Weierstrass.Mont.Modulus} {K : WinCfg} {base : Addr} {size a wk : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAcc : WkOk F K.M C.p size wk Sl) (hn : K.M.n=4)
    (hy : K.E.y=K.E.x+32) (hz : K.E.z=K.E.x+64)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s)
    (h8 : s.gpr .ebx=BitVec.ofNat 32 a) (ha : 1≤a) (ha' : a≤15)
    (hT : K.tbl+768≤size)
    (hD : ∀ x∈jacCoords K.E, Sl x)
    (hQ : ∀ x∈jacCoords (K.tblPt ((a-1)/2+1)), x∈V)
    (hSep : K.E.x+96≤K.tbl ∨ K.tbl+768≤K.E.x)
    :
    WP isa (.block (Naf.publicEntry K)) s fun t =>
      ProgKeep K.M base wk (jacCoords K.E) s t ∧
      Inv K.M base size C.p Sl (jacCoords K.E++V)
        (pointTransferEnv E K.E (K.tblPt ((a-1)/2+1))) t := by
  have hdz := hL.le K.E.z (hD _ (by simp [jacCoords]))
  rw [hn,hz] at hdz
  refine WP.mono (nafPublicEntry_ok hI.scr ha ha' h8 hT (by omega) hSep)
    fun t ⟨hv,hk,ho⟩ => hI.transferPointFields hL hAcc (by rw [hn]; exact hy) (by rw [hn]; exact hz) hD hQ ?_ ?_ ?_ hk (by simpa only [hn] using ho)
  · simpa only [hn,WinCfg.tblPt,Nat.add_sub_cancel,Nat.mul_zero,Nat.add_zero,
      show 24*4=96 from rfl] using hv 0 (by decide)
  · simpa only [hn,hy,WinCfg.tblPt,Nat.add_sub_cancel,Nat.mul_one,
      show 24*4=96 from rfl,show 8*4=32 from rfl] using hv 1 (by decide)
  · simpa only [hn,hz,WinCfg.tblPt,Nat.add_sub_cancel,
      show 24*4=96 from rfl,show 16*4=64 from rfl,show 32*2=64 from rfl] using hv 2 (by decide)

end VG.Proof.Weierstrass.X86
