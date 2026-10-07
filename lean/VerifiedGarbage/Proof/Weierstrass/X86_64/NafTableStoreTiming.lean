import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableFields
import VerifiedGarbage.Proof.Weierstrass.X86_64.RegFieldTiming

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64

theorem nafTableStore_relCT {K : WinCfg} {base : Addr} {size j m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hn : K.M.n=4)
    (hy : K.R.y=K.R.x+32) (hz : K.R.z=K.R.x+64)
    {V : List Nat} {E : Nat → Fin m} (hj : j<8)
    (ht : K.tbl<2^31) (hT : K.tbl+768≤size)
    (hD : ∀ x∈jacCoords (K.tblPt (j+1)), Sl x)
    (hQ : ∀ x∈jacCoords K.R, x∈V)
    (hSep : K.R.x+96≤K.tbl ∨ K.tbl+768≤K.R.x)
    (hc : RegCT [.rdi,.rbx] (.block (Naf.tableStore K))) :
    RelCT isa (fun s t => FieldPair K.M base size m Sl V E s t ∧
      s.gpr .rbx=BitVec.ofNat 64 j ∧ t.gpr .rbx=BitVec.ofNat 64 j)
      (.block (Naf.tableStore K))
      (fun s t => FieldPair K.M base size m Sl (jacCoords (K.tblPt (j+1))++V)
        (pointTransferEnv E (K.tblPt (j+1)) K.R) s t ∧
        s.gpr .rbx=BitVec.ofNat 64 j ∧ t.gpr .rbx=BitVec.ofNat 64 j) := by
  apply regFieldProgram_relCT hc
  · intro s t hp hs ht
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact hp.1.scr.rdi.trans hp.2.scr.rdi.symm
    · exact hs.trans ht.symm
  · intro s hi hbx
    exact WP.mono (nafTableFields_ok hL hn hy hz hi hj hbx ht hT hD hQ hSep)
      (fun _ ⟨hk,it⟩ => ⟨it,(hk.gpr _ (by rw [hn]; decide)).trans hbx⟩)

end VG.Proof.Weierstrass.X86_64
