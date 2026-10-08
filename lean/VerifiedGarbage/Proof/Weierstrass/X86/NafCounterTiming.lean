import VerifiedGarbage.Proof.Weierstrass.X86.NafRunTiming

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
