import VerifiedGarbage.Proof.Weierstrass.X86.NafEntryTiming
import VerifiedGarbage.Proof.Weierstrass.X86.NafArithmeticTiming
import VerifiedGarbage.Proof.Weierstrass.X86.NafDigit

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

structure NafDigitChecks (K : WinCfg) (F : Spec.Weierstrass.Mont.Modulus) : Prop where
  read : RegCT [.edi,.esi] (.block (Naf.digitRead K))
  entry : NafEntryChecks K F
  add : JacAddChecks K F K.R K.E K.D
  copy : ScratchCT (.block (copyPt K.M.n K.R K.D))

theorem nafDigit_fields_relCT {F : Spec.Weierstrass.Mont.Modulus}
    {K : WinCfg} {C : Curve} {base : Addr} {size wk k j : Nat} {E : Nat → Fe C}
    (hL : NafLay K size) (hJ : K.J=65) (hW : WkOk F K.M C.p size wk (·∈nafSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hOne : K.one<C.p) (hj : j<257)
    (hc : NafDigitChecks K F) :
    RelCT isa (fun s t => FieldPair K.M base size C.p (·∈nafSlots K) (nafLive K) E (BitVec.ofNat 32 j) s t ∧
      s.mem (off base (K.bits+j))=Naf5.byte k j ∧ t.mem (off base (K.bits+j))=Naf5.byte k j)
      (Naf.digit K F)
      (fun s t => ∃ E',FieldPair K.M base size C.p (·∈nafSlots K) (nafLive K) E' (BitVec.ofNat 32 j) s t) := by
  have rd := keepsField_relCT (counter:=BitVec.ofNat 32 j) (counter':=BitVec.ofNat 32 j)
    (M:=K.M) (base:=base) (size:=size) (m:=C.p) (Sl:=(·∈nafSlots K)) (V:=nafLive K) (E:=E)
    (Pre:=fun s => s.mem (off base (K.bits+j))=Naf5.byte k j)
    (Post:=fun s => s.gpr .ebx=(Naf5.byte k j).setWidth 32 ∧ s.zf=some (decide (Naf5.byte k j=0)))
    (ws:=[.ecx,.ebx]) (by decide) hc.read
    (fun _ _ hp _ _ => hp.pub.agree (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · exact hp.pub.edi
      · exact hp.count₁.trans hp.count₂.symm))
    (fun _ hi ct hb => WP.mono (nafRead_ok hi.scr (by have:=hL.bits; omega) ct hb)
      (fun _ ⟨eb,zf,hk⟩ => ⟨(hk.1 _ (by decide)).trans ct,⟨eb,zf⟩,hk⟩))
  rw [Naf.digit]
  apply RelCT.seq rd
  apply RelCT.ite
  · intro s t ⟨_,ps,pt⟩; exact ps.2.trans pt.2.symm
  · intro s t ts tt u v ⟨⟨hp,_,_⟩,_⟩ es et
    cases es with
    | block es =>
      cases es
      cases et with
      | block et =>
        cases et
        exact ⟨rfl,_,hp⟩
  · intro s t ts tt u v ⟨⟨hp,ps,pt⟩,he⟩ es et
    have hn := of_decide_eq_false (Option.some.inj (ps.2.symm.trans he))
    have hm0 : Naf5.magnitude k j≠0 := fun hz => hn ((Naf5.byte_zero_iff k j).mpr hz)
    have entry := nafEntry_relCT (base:=base) (E:=E) (counter:=BitVec.ofNat 32 j) hL hW hm
      (b:=Naf5.byte k j) (by rw [nafMagnitude_byte]; omega)
      (by rw [nafMagnitude_byte]; exact Naf5.magnitude_le k j) hc.entry
    have add := RelCT.exists_ (fun E' => nafAdd_relCT (base:=base) (E:=E')
      (counter:=BitVec.ofNat 32 j) hL hJ hW hm hOne hc.add hc.copy)
    exact entry.seq add _ _ _ _ _ _ ⟨hp,ps.1,pt.1⟩ es et

end VG.Proof.Weierstrass.X86
