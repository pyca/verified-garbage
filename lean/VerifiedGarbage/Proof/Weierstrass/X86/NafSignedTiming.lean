import VerifiedGarbage.Proof.Weierstrass.X86.NafLoadTiming
import VerifiedGarbage.Proof.Weierstrass.X86.NafDigitRead
import VerifiedGarbage.Proof.Framework.RelCTAssoc

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Proof.Mont VG.Proof.Mont.X86

structure NafEntryChecks (K : WinCfg) (F : Spec.Weierstrass.Mont.Modulus) : Prop where
  lookup : RegCT [.edi,.ebx] (.block (Naf.publicEntry K))
  sign : RegCT [.ebx] (.block [.alu .cmp .ebx (.imm 128)])
  abs : RegCT [.ebx] (.block [.mov .eax (.imm 256),.alu .sub .eax (.reg .ebx),.mov .ebx (.reg .eax)])
  neg : ScratchCT (opCode F (.sub K.E.y K.zero K.E.y))

theorem nafSigned_relCT {counter : BitVec 32} {F : Spec.Weierstrass.Mont.Modulus}
    {K : WinCfg} {base : Addr} {size m wk : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hW : WkOk F K.M m size wk Sl)
    (hm : UnitMod m (2^(64*K.M.n))) {V : List Nat} {E E' : Nat → Fin m} {b : BitVec 8}
    (hZero : K.zero∈V) (hc : NafEntryChecks K F)
    (hLookup : RelCT isa (fun s t => FieldPair K.M base size m Sl V E counter s t ∧
      s.gpr .ebx=BitVec.ofNat 32 (nafMagnitude b) ∧ t.gpr .ebx=BitVec.ofNat 32 (nafMagnitude b))
      (.block (Naf.publicEntry K)) (FieldPair K.M base size m Sl (jacCoords K.E++V) E' counter))
    (hD : ∀ x∈jacCoords K.E,Sl x) :
    RelCT isa (fun s t => FieldPair K.M base size m Sl V E counter s t ∧
      s.gpr .ebx=b.setWidth 32 ∧ t.gpr .ebx=b.setWidth 32)
      (Naf.signedEntry K F)
      (fun s t => ∃ E'',FieldPair K.M base size m Sl (jacCoords K.E++V) E'' counter s t) := by
  have sign := keepsField_relCT (counter:=counter) (counter':=counter)
    (M:=K.M) (base:=base) (size:=size) (m:=m) (Sl:=Sl) (V:=V) (E:=E)
    (Pre:=fun s => s.gpr .ebx=b.setWidth 32)
    (Post:=fun s => s.cf=some (decide (b.toNat<128)) ∧ s.gpr .ebx=b.setWidth 32)
    (ws:=[]) (by simp) hc.sign
    (fun _ _ hp ps pt => hp.pub.agree (by
      intro r hr; rw [List.mem_singleton.mp hr]; exact ps.trans pt.symm))
    (fun s _ ct h8 => WP.mono (nafDigitSign_ok s h8) (fun t ⟨cf,kt⟩ =>
      ⟨(kt.1 _ (by simp)).trans ct,⟨cf,(kt.1 _ (by simp)).trans h8⟩,kt⟩))
  rw [Naf.signedEntry]
  apply RelCT.seq sign
  apply RelCT.ite
  · intro s t ⟨_,ps,pt⟩; exact ps.1.trans pt.1.symm
  · refine hLookup.mono (P':=fun (s t : State) =>
        (FieldPair K.M base size m Sl V E counter s t ∧
          (s.cf=some (decide (b.toNat<128)) ∧ s.gpr .ebx=b.setWidth 32) ∧
          (t.cf=some (decide (b.toNat<128)) ∧ t.gpr .ebx=b.setWidth 32)) ∧ eval .b s=some true)
        (Q':=fun s t => ∃ E'',FieldPair K.M base size m Sl (jacCoords K.E++V) E'' counter s t)
        (fun s t ⟨⟨hp,ps,pt⟩,he⟩ => ?_) (fun _ _ hp => ⟨_,hp⟩)
    have hb := of_decide_eq_true (Option.some.inj (ps.1.symm.trans he))
    have e : b.setWidth 32=BitVec.ofNat 32 (nafMagnitude b) := by
      rw [nafMagnitude,ite_eq_left hb]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    exact ⟨hp,ps.2.trans e,pt.2.trans e⟩
  · have abs := keepsField_relCT (counter:=counter) (counter':=counter)
      (M:=K.M) (base:=base) (size:=size) (m:=m) (Sl:=Sl) (V:=V) (E:=E)
      (Pre:=fun s => s.gpr .ebx=b.setWidth 32)
      (Post:=fun s => s.gpr .ebx=BitVec.ofNat 32 (256-b.toNat))
      (ws:=[.eax,.ebx]) (by decide) hc.abs
      (fun _ _ hp ps pt => hp.pub.agree (by
        intro r hr; rw [List.mem_singleton.mp hr]; exact ps.trans pt.symm))
      (fun s _ ct h8 => WP.mono (nafAbs_ok s h8) (fun t ⟨ha,kt⟩ =>
        ⟨(kt.1 _ (by decide)).trans ct,ha,kt⟩))
    have neg : RelCT isa (FieldPair K.M base size m Sl (jacCoords K.E++V) E' counter)
        (opCode F (.sub K.E.y K.zero K.E.y))
        (fun s t => ∃ E'',FieldPair K.M base size m Sl (jacCoords K.E++V) E'' counter s t) := by
      have op := fieldProgram_relCT (counter:=counter) (base:=base) hc.neg
        (fun s (hi : Inv K.M base size m Sl (jacCoords K.E++V) E' s) =>
          WP.mono (fop_ok hL hW hm hi (op:=.sub K.E.y K.zero K.E.y) (by
            intro x hx
            simp only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
            rcases hx with rfl|rfl|rfl
            · exact hD _ (by simp [jacCoords])
            · exact hi.sl _ (List.mem_append_right _ hZero)
            · exact hD _ (by simp [jacCoords])) (by
              simp [FOp.ins,jacCoords,hZero])) (fun t ⟨kt,it⟩ =>
                ⟨⟨kt.gpr,kt.rd,kt.wr⟩,it.sub (fun _ hx => List.mem_cons_of_mem _ hx)⟩))
      exact op.mono (fun _ _ hp => hp) (fun _ _ hp => ⟨_,hp⟩)
    intro s t ts tt u v ⟨⟨hp,ps,pt⟩,he⟩ es et
    have hb := of_decide_eq_false (Option.some.inj (ps.1.symm.trans he))
    have lookup := hLookup.mono (P':=fun (s t : State) => FieldPair K.M base size m Sl V E counter s t ∧
      s.gpr .ebx=BitVec.ofNat 32 (256-b.toNat) ∧ t.gpr .ebx=BitVec.ofNat 32 (256-b.toNat))
      (fun _ _ ⟨h,ps,pt⟩ => by rw [nafMagnitude,ite_eq_right hb]; exact ⟨h,ps,pt⟩)
      (fun _ _ hp => hp)
    exact ((RelCT.block_append (abs.seq lookup)).seq neg) _ _ _ _ _ _ ⟨hp,ps.2,pt.2⟩ es et

end VG.Proof.Weierstrass.X86
