import VerifiedGarbage.Proof.Weierstrass.X86.NafPublicFields
import VerifiedGarbage.Proof.Weierstrass.X86.RegFieldTiming

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem nafPublic_relCT {counter : BitVec 32} {F : Spec.Weierstrass.Mont.Modulus}
    {K : WinCfg} {base : Addr} {size wk a : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hW : WkOk F K.M C.p size wk Sl) (hn : K.M.n=4)
    (hy : K.E.y=K.E.x+32) (hz : K.E.z=K.E.x+64)
    {V : List Nat} {E : Nat → Fe C} (ha : 1≤a) (ha15 : a≤15) (hT : K.tbl+768≤size)
    (hD : ∀ x∈jacCoords K.E,Sl x)
    (hQ : ∀ x∈jacCoords (K.tblPt ((a-1)/2+1)),x∈V)
    (hSep : K.E.x+96≤K.tbl ∨ K.tbl+768≤K.E.x)
    (hc : RegCT [.edi,.ebx] (.block (Naf.publicEntry K))) :
    RelCT isa (fun s t => FieldPair K.M base size C.p Sl V E counter s t ∧
      s.gpr .ebx=BitVec.ofNat 32 a ∧ t.gpr .ebx=BitVec.ofNat 32 a)
      (.block (Naf.publicEntry K))
      (FieldPair K.M base size C.p Sl (jacCoords K.E++V)
        (pointTransferEnv E K.E (K.tblPt ((a-1)/2+1))) counter) := by
  have h := regFieldProgram_relCT (M:=K.M) (base:=base) (size:=size) (m:=C.p)
    (Sl:=Sl) (V:=V) (E:=E) (counter:=counter) (counter':=counter)
    (Pre:=fun s => s.gpr .ebx=BitVec.ofNat 32 a) (Post:=fun _ => True) hc
    (fun s t hp hs ht => hp.pub.agree (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · exact hp.pub.edi
      · exact hs.trans ht.symm))
    (fun s hi ct h8 => WP.mono (nafPublicFields_ok hL hW hn hy hz hi h8 ha ha15 hT hD hQ hSep)
      (fun t ⟨kt,it⟩ => ⟨Keeps.mono ⟨kt.gpr,kt.rd,kt.wr⟩ (by decide),it,
        (kt.gpr _ (by decide)).trans ct,trivial⟩))
  exact h.mono (fun _ _ hp => hp) (fun _ _ hp => hp.1)

end VG.Proof.Weierstrass.X86
