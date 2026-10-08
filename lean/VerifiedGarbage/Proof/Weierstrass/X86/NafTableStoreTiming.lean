import VerifiedGarbage.Proof.Weierstrass.X86.NafTableFields
import VerifiedGarbage.Proof.Weierstrass.X86.RegFieldTiming

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Proof.Mont VG.Proof.Mont.X86

theorem nafTableStore_relCT {FM : Spec.Weierstrass.Mont.Modulus} {wk : Nat}
    {K : WinCfg} {base : Addr} {size j m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hW : WkOk FM K.M m size wk Sl) (hn : K.M.n=4)
    (hy : K.R.y=K.R.x+32) (hz : K.R.z=K.R.x+64)
    {V : List Nat} {E : Nat → Fin m} (hj : j<8) (hT : K.tbl+768≤size)
    (hD : ∀ x∈jacCoords (K.tblPt (j+1)),Sl x)
    (hQ : ∀ x∈jacCoords K.R,x∈V) (hSep : K.R.x+96≤K.tbl ∨ K.tbl+768≤K.R.x)
    (hc : RegCT [.edi,.esi] (.block (Naf.tableStore K))) :
    RelCT isa (FieldPair K.M base size m Sl V E (BitVec.ofNat 32 j)) (.block (Naf.tableStore K))
      (FieldPair K.M base size m Sl (jacCoords (K.tblPt (j+1))++V)
        (pointTransferEnv E (K.tblPt (j+1)) K.R) (BitVec.ofNat 32 j)) := by
  have h := regFieldProgram_relCT (M:=K.M) (base:=base) (size:=size) (m:=m)
    (Sl:=Sl) (V:=V) (E:=E) (counter:=BitVec.ofNat 32 j) (counter':=BitVec.ofNat 32 j) (Pre:=fun _ => True) (Post:=fun _ => True) hc
    (fun s t hp _ _ => hp.pub.agree (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · exact hp.pub.edi
      · exact hp.count₁.trans hp.count₂.symm))
    (fun s hi ct _ => WP.mono (nafTableFields_ok hL hW hn hy hz hi hj ct hT hD hQ hSep)
      (fun t ⟨kt,it⟩ => ⟨Keeps.mono ⟨kt.gpr,kt.rd,kt.wr⟩ (by decide),it,
        (kt.gpr _ (by decide)).trans ct,trivial⟩))
  exact h.mono (fun _ _ hp => ⟨hp,trivial,trivial⟩) (fun _ _ hp => hp.1)

end VG.Proof.Weierstrass.X86
