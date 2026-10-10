import VerifiedGarbage.Proof.Weierstrass.X86.NafPublicFields
import VerifiedGarbage.Proof.Weierstrass.X86.RegFieldTiming
import VerifiedGarbage.Proof.Weierstrass.X86.NafDigitRead
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Weierstrass.X86.NafEntry
import VerifiedGarbage.Proof.Weierstrass.X86.NafArithmeticTiming
import VerifiedGarbage.Proof.Weierstrass.X86.NafFinish

/-! ## `NafLoadTiming` -/

section

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

end

/-! ## `NafSignedTiming` -/

section

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

end

/-! ## `NafEntryTiming` -/

section

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

end

/-! ## `NafDigitTiming` -/

section

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

end

/-! ## `NafRunTiming` -/

section

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

def NafRunPair (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C)
    (β : Nat → BitVec 8) (e : Nat) (counter : BitVec 32) (s t : State) : Prop :=
  (∃ E,FieldPair K.M base size C.p (·∈nafSlots K) (nafLive K) E counter s t) ∧
    NafCore K C base size P β e s ∧ NafCore K C base size P β e t

theorem nafDigit_relCT {F : Spec.Weierstrass.Mont.Modulus}
    {K : WinCfg} {C : Curve} {base : Addr} {size wk k j : Nat} {P : Point C}
    (hL : NafLay K size) (hJ : K.J=65) (hW : WkOk F K.M C.p size wk (·∈nafSlots K))
    (hBitsWk : K.bits+260≤wk) (hm : UnitMod C.p (2^(64*K.M.n)))
    (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p) (hj : j<257) (hP : onCurve C P=true)
    (hc : NafDigitChecks K F) :
    RelCT isa (NafRunPair K C base size P (Naf5.byte k) (2*Naf5.residual k (j+1)) (BitVec.ofNat 32 j))
      (Naf.digit K F)
      (NafRunPair K C base size P (Naf5.byte k) (Naf5.residual k j) (BitVec.ofNat 32 j)) := by
  have raw : RelCT isa (NafRunPair K C base size P (Naf5.byte k) (2*Naf5.residual k (j+1)) (BitVec.ofNat 32 j))
      (Naf.digit K F)
      (fun s t => ∃ E,FieldPair K.M base size C.p (·∈nafSlots K) (nafLive K) E (BitVec.ofNat 32 j) s t) := by
    intro s t ts tt u v ⟨⟨E,h⟩,cs,ct⟩ es et
    exact nafDigit_fields_relCT hL hJ hW hm hOne hj hc _ _ _ _ _ _
      ⟨h,cs.stable.bits j hj,ct.stable.bits j hj⟩ es et
  exact raw.wp (fun s t ⟨⟨_,h⟩,cs,ct⟩ =>
    ⟨WP.mono (nafDigit_ok hL hJ hW hBitsWk hm hC ha hOne hj hP cs h.count₁) (fun _ h => h.2),
     WP.mono (nafDigit_ok hL hJ hW hBitsWk hm hC ha hOne hj hP ct h.count₂) (fun _ h => h.2)⟩)

theorem nafDoubleCore_relCT {counter : BitVec 32} {F : Spec.Weierstrass.Mont.Modulus}
    {K : WinCfg} {C : Curve} {base : Addr} {size wk e : Nat} {P : Point C} {β : Nat → BitVec 8}
    (hL : NafLay K size) (hJ : K.J=65) (hW : WkOk F K.M C.p size wk (·∈nafSlots K))
    (hBitsWk : K.bits+260≤wk) (hm : UnitMod C.p (2^(64*K.M.n)))
    (hC : Law C) (ha : AM3 C) (hP : onCurve C P=true)
    (hd : ScratchCT (fprog F (dblJMul K.S K.R K.D)))
    (hcp : ScratchCT (.block (copyPt K.M.n K.R K.D))) :
    RelCT isa (NafRunPair K C base size P β e counter)
      (.seq (fprog F (dblJMul K.S K.R K.D)) (.block (copyPt 4 K.R K.D)))
      (NafRunPair K C base size P β (2*e) counter) := by
  have raw := (RelCT.exists_ (fun E => nafDouble_relCT (E:=E) (counter:=counter)
    (base:=base) hL hW hm hd hcp)).mono
    (P':=NafRunPair K C base size P β e counter) (fun _ _ h => h.1) (fun _ _ h => h)
  exact raw.wp (fun _ _ ⟨_,cs,ct⟩ =>
    ⟨WP.mono (nafDoubleCore_ok hL hW hBitsWk hJ hm hC ha hP cs) (fun _ h => h.2),
     WP.mono (nafDoubleCore_ok hL hW hBitsWk hJ hm hC ha hP ct) (fun _ h => h.2)⟩)

end VG.Proof.Weierstrass.X86

end

/-! ## `NafCounterTiming` -/

section

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem nafRun_keeps_relCT {counter counter' : BitVec 32} {K : WinCfg} {C : Curve}
    {base : Addr} {size e : Nat} {P : Point C} {β : Nat → BitVec 8}
    {code : Prog isa} {Post : State → Prop} {ws : List Reg}
    (hws : ∀ r∈ws,r∈powClob) (hc : RegCT [.esi] code)
    (hw : ∀ s,s.gpr .esi=counter → WP isa code s
      (fun t => t.gpr .esi=counter' ∧ Post t ∧ CKeeps ws s t)) :
    RelCT isa (NafRunPair K C base size P β e counter) code
      (fun s t => NafRunPair K C base size P β e counter' s t ∧ Post s ∧ Post t) := by
  have hd : Reg.edi∉ws := fun h => by have := hws _ h; contradiction
  have hs : Reg.esp∉ws := fun h => by have := hws _ h; contradiction
  intro s t ts tt u v ⟨⟨E,h⟩,cs,ct⟩ es et
  have raw := keepsField_relCT (M:=K.M) (base:=base) (size:=size) (m:=C.p)
    (Sl:=(·∈nafSlots K)) (V:=nafLive K) (E:=E) (Pre:=fun _ => True) hws hc
    (fun _ _ hp _ _ => hp.pub.agree (by
      intro r hr; rw [List.mem_singleton.mp hr]; exact hp.count₁.trans hp.count₂.symm))
    (fun s _ co _ => hw s co)
  obtain ⟨ht,hp,ps,pt⟩ := raw _ _ _ _ _ _ ⟨h,trivial,trivial⟩ es et
  obtain ⟨_,u',eu,_,_,ku⟩ := hw s h.count₁
  obtain ⟨_,v',ev,_,_,kv⟩ := hw t h.count₂
  obtain ⟨-,rfl⟩ := Exec.det es eu
  obtain ⟨-,rfl⟩ := Exec.det et ev
  exact ⟨ht,⟨⟨_,hp⟩,cs.of_keeps ku hd hs,ct.of_keeps kv hd hs⟩,ps,pt⟩

end VG.Proof.Weierstrass.X86

end

/-! ## `NafStepTiming` -/

section

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

structure NafStepChecks (K : WinCfg) (F : Spec.Weierstrass.Mont.Modulus) : Prop where
  digit : NafDigitChecks K F
  double : ScratchCT (fprog F (dblJMul K.S K.R K.D))
  dec : RegCT [.esi] (.block [.alu .sub .esi (.imm 1)])
  test : RegCT [.esi] (.block [.alu .test .esi (.reg .esi)])

theorem nafStep_relCT {F : Spec.Weierstrass.Mont.Modulus}
    {K : WinCfg} {C : Curve} {base : Addr} {size wk k j : Nat} {P : Point C}
    (hL : NafLay K size) (hJ : K.J=65) (hW : WkOk F K.M C.p size wk (·∈nafSlots K))
    (hBitsWk : K.bits+260≤wk) (hm : UnitMod C.p (2^(64*K.M.n)))
    (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p) (hj : j<256) (hP : onCurve C P=true)
    (hc : NafStepChecks K F) :
    RelCT isa (NafRunPair K C base size P (Naf5.byte k) (Naf5.residual k (j+1)) (BitVec.ofNat 32 (j+1)))
      (Naf.windowStep K F)
      (fun s t => NafRunPair K C base size P (Naf5.byte k) (Naf5.residual k j) (BitVec.ofNat 32 j) s t ∧
        s.zf=some (decide (j=0)) ∧ t.zf=some (decide (j=0))) := by
  have dec := nafRun_keeps_relCT (K:=K) (C:=C) (base:=base) (size:=size) (P:=P)
    (β:=Naf5.byte k) (e:=Naf5.residual k (j+1)) (counter:=BitVec.ofNat 32 (j+1))
    (counter':=BitVec.ofNat 32 j) (Post:=fun _ => True) (ws:=[.esi]) (by decide) hc.dec
    (fun _ ct => wp_decCounter (by omega) ct (fun _ cn kn mn => WP.block_nil
      ⟨by simpa only [Nat.add_sub_cancel] using cn,trivial,kn.1,mn,kn.2⟩))
  rw [Naf.windowStep]
  apply RelCT.seq (dec.mono (fun _ _ h => h) (fun _ _ h => h.1))
  apply RelCT.assoc
  apply RelCT.seq (nafDoubleCore_relCT hL hJ hW hBitsWk hm hC ha hP hc.double hc.digit.copy)
  apply RelCT.seq (nafDigit_relCT hL hJ hW hBitsWk hm hC ha hOne (by omega) hP hc.digit)
  exact nafRun_keeps_relCT (ws:=[]) (by simp) hc.test (fun _ ct =>
    wp_testCounter (by omega) ct (fun _ ft zt => WP.block_nil
      ⟨(congrFun ft.gpr .esi).trans ct,zt,(fun r _ => congrFun ft.gpr r),ft.mem,ft.rd,ft.wr⟩))

end VG.Proof.Weierstrass.X86

end

/-! ## `NafLoopTiming` -/

section

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem nafLoop_relCT {F : Spec.Weierstrass.Mont.Modulus}
    {K : WinCfg} {C : Curve} {base : Addr} {size wk k : Nat} {P : Point C}
    (hL : NafLay K size) (hJ : K.J=65) (hW : WkOk F K.M C.p size wk (·∈nafSlots K))
    (hBitsWk : K.bits+260≤wk) (hm : UnitMod C.p (2^(64*K.M.n)))
    (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p) (hP : onCurve C P=true)
    (hc : NafStepChecks K F) :
    RelCT isa (NafRunPair K C base size P (Naf5.byte k) (Naf5.residual k 256) 256)
      (.loop (Naf.windowStep K F) .ne)
      (NafRunPair K C base size P (Naf5.byte k) k 0) := by
  let I := fun j s t => 1≤j ∧ j≤256 ∧
    NafRunPair K C base size P (Naf5.byte k) (Naf5.residual k j) (BitVec.ofNat 32 j) s t
  have step : ∀ j,RelCT isa (I j) (Naf.windowStep K F) (fun s t =>
      eval .ne s=eval .ne t ∧
      (eval .ne s=some false → NafRunPair K C base size P (Naf5.byte k) k 0 s t) ∧
      (eval .ne s=some true → ∃ n<j,I n s t)) := by
    intro j
    by_cases hj : 1≤j
    · by_cases hj256 : j≤256
      · refine (nafStep_relCT hL hJ hW hBitsWk hm hC ha hOne (j:=j-1) (by omega) hP hc).mono
          (P':=I j) (fun _ _ h => by simpa only [Nat.sub_add_cancel hj] using h.2.2) ?_
        intro s t ⟨hp,cs,ct⟩
        have es : eval .ne s=some (!decide (j-1=0)) := by simp only [eval,cs,Option.map_some]
        have et : eval .ne t=some (!decide (j-1=0)) := by simp only [eval,ct,Option.map_some]
        refine ⟨es.trans et.symm,fun he => ?_,fun he => ?_⟩
        · have hz : j-1=0 := by
            have := Option.some.inj (es.symm.trans he)
            simpa using this
          rw [hz] at hp
          exact hp
        · have hz : j-1≠0 := by
            have := Option.some.inj (es.symm.trans he)
            simpa using this
          exact ⟨j-1,by omega,by omega,by omega,hp⟩
      · exact RelCT.of_false (fun _ _ h => hj256 h.2.1)
    · exact RelCT.of_false (fun _ _ h => hj h.1)
  exact (RelCT.loop I step 256).mono (fun _ _ h => ⟨by decide,by decide,h⟩) (fun _ _ h => h)

theorem nafRun_relCT {F : Spec.Weierstrass.Mont.Modulus}
    {K : WinCfg} {C : Curve} {base : Addr} {size wk k : Nat} {P : Point C}
    (hL : NafLay K size) (hJ : K.J=65) (hW : WkOk F K.M C.p size wk (·∈nafSlots K))
    (hBitsWk : K.bits+260≤wk) (hm : UnitMod C.p (2^(64*K.M.n)))
    (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p) (hk : k<2^256) (hP : onCurve C P=true)
    (hc : NafStepChecks K F) :
    RelCT isa (NafRunPair K C base size P (Naf5.byte k) 0 256)
      (.seq (Naf.digit K F) (.loop (Naf.windowStep K F) .ne))
      (NafRunPair K C base size P (Naf5.byte k) k 0) := by
  have hd := nafDigit_relCT (base:=base) (k:=k) (j:=256) hL hJ hW hBitsWk hm hC ha hOne (by decide) hP hc.digit
  rw [Naf5.residual_zero257 hk,Nat.mul_zero] at hd
  exact hd.seq (nafLoop_relCT hL hJ hW hBitsWk hm hC ha hOne hP hc)

end VG.Proof.Weierstrass.X86

end
