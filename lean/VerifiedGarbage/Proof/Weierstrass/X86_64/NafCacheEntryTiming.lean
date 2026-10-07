import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCacheEntryFields
import VerifiedGarbage.Proof.Weierstrass.X86_64.RegFieldTiming

/-! A signed peer lookup has shared field results when its public digit agrees. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64

theorem nafSignedCachedEntry_relCT {K : WinCfg} {base : Addr} {size tbl dst m : Nat}
    [NeZero m] {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fin m}
    (hL : Lay K.M size Sl) (hn : K.M.n=4 ∨ K.M.n=6 ∨ K.M.n=9) (hm : UnitMod m (2^(64*K.M.n)))
    {b : BitVec 8}
    (ha : 1≤nafMagnitude b) (ha' : nafMagnitude b≤15) (hodd : nafMagnitude b%2=1)
    (hy : K.E.y=K.E.x+8*K.M.n) (hz : K.E.z=K.E.x+16*K.M.n)
    (hp : K.tbl<2^31) (hc : tbl<2^31)
    (hP : K.tbl+192*K.M.n≤size) (hC : tbl+128*K.M.n≤size)
    (hD : ∀ x∈cachedSlots K.M.n K.E dst,Sl x)
    (hQ : ∀ x∈cachedSlots K.M.n (K.tblPt ((nafMagnitude b-1)/2+1))
      (tbl+16*K.M.n*((nafMagnitude b-1)/2)),x∈V)
    (hEP : K.E.x+24*K.M.n≤K.tbl ∨ K.tbl+192*K.M.n≤K.E.x)
    (hEC : K.E.x+24*K.M.n≤tbl ∨ tbl+128*K.M.n≤K.E.x)
    (hDC : dst+16*K.M.n≤tbl ∨ tbl+128*K.M.n≤dst)
    (hDE : dst+16*K.M.n≤K.E.x ∨ K.E.x+24*K.M.n≤dst)
    (hZero : K.zero∈V) (heZero : E K.zero=0) (hApart : K.zero∉cachedSlots K.M.n K.E dst)
    (hct : RegCT [.rdi,.r8] (Naf.signedCachedEntry K tbl dst)) :
    RelCT isa (fun s t => FieldPair K.M base size m Sl V E s t ∧
      s.gpr .r8=b.setWidth 64 ∧ t.gpr .r8=b.setWidth 64)
      (Naf.signedCachedEntry K tbl dst)
      (FieldPair K.M base size m Sl (cachedSlots K.M.n K.E dst++V) (cachedEntryEnv K E tbl dst b)) := by
  have h := regFieldProgram_relCT (M:=K.M) (base:=base) (size:=size) (m:=m)
    (Sl:=Sl) (V:=V) (E:=E) (Pre:=fun s => s.gpr .r8=b.setWidth 64)
    (Post:=fun _ => True) hct (fun s t p ds dt => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · exact p.1.scr.rdi.trans p.2.scr.rdi.symm
      · exact ds.trans dt.symm)) (fun s hi ds =>
        WP.mono (nafSignedCachedFields_ok hL hn hm hi ha ha' hodd ds hy hz hp hc hP hC
          hD hQ hEP hEC hDC hDE hZero heZero hApart) (fun _ ht => ⟨ht.2,trivial⟩))
  exact h.mono (fun _ _ ht => ht) (fun _ _ ht => ht.1)

end VG.Proof.Weierstrass.X86_64
