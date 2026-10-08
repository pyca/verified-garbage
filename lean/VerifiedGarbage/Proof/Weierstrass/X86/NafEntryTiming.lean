import VerifiedGarbage.Proof.Weierstrass.X86.NafSignedTiming
import VerifiedGarbage.Proof.Weierstrass.X86.NafEntry

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem nafEntry_relCT {counter : BitVec 32} {F : Spec.Weierstrass.Mont.Modulus}
    {K : WinCfg} {C : Curve} {base : Addr} {size wk : Nat} {E : Nat → Fe C} {b : BitVec 8}
    (hL : NafLay K size) (hW : WkOk F K.M C.p size wk (·∈nafSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n)))
    (hmag : 1≤nafMagnitude b) (hmag15 : nafMagnitude b≤15) (hc : NafEntryChecks K F) :
    RelCT isa (fun s t => FieldPair K.M base size C.p (·∈nafSlots K) (nafLive K) E counter s t ∧
      s.gpr .ebx=b.setWidth 32 ∧ t.gpr .ebx=b.setWidth 32)
      (Naf.signedEntry K F)
      (fun s t => ∃ E',FieldPair K.M base size C.p (·∈nafSlots K)
        (jacCoords K.E++nafLive K) E' counter s t) := by
  have hw : ∀ x∈jacCoords K.E,x∈winOther K := by
    intro x hx
    simp only [jacCoords,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have hd : ∀ x∈jacCoords K.E,x∈nafSlots K := fun x hx => nafOther_slots K x (hw x hx)
  have sep : K.E.x+96≤K.tbl ∨ K.tbl+768≤K.E.x := by
    have hx := hL.tbl K.E.x (List.mem_append_right _ (hw _ (by simp [jacCoords])))
    have hz := hL.tbl K.E.z (List.mem_append_right _ (hw _ (by simp [jacCoords])))
    rw [hL.exz] at hz
    omega
  exact nafSigned_relCT hL.lay hW hm (by simp [nafLive,nafTableLive,winRo]) hc
    (nafPublic_relCT hL.lay hW hL.n hL.exy hL.exz hmag hmag15
      (by have := hL.table_le; omega) hd
      (nafLive_table K hL.n (by omega) (by omega)) sep hc.lookup) hd

end VG.Proof.Weierstrass.X86
