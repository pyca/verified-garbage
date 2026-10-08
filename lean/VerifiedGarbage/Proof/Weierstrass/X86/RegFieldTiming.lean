import VerifiedGarbage.Proof.Weierstrass.X86.FieldTiming

/-! Public lookup addresses and counters alongside equal field environments. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Proof.Mont VG.Proof.Mont.X86

abbrev RegCT (rs : List Reg) (c : Prog isa) : Prop :=
  ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (nafτ rs)) c

theorem regFieldProgram_relCT {counter counter' : BitVec 32}
    {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V W : List Nat} {E E' : Nat → Fin m} {c : Prog isa}
    {Pre Post : State → Prop} {rs : List Reg} (hc : RegCT rs c)
    (hp : ∀ s t,FieldPair M base size m Sl V E counter s t → Pre s → Pre t →
      VG.X86.Taint.Agree (nafτ rs) s t)
    (hw : ∀ s,Inv M base size m Sl V E s → s.gpr .esi=counter → Pre s →
      WP isa c s (fun t => Keeps powClob s t ∧ Inv M base size m Sl W E' t ∧
        t.gpr .esi=counter' ∧ Post t)) :
    RelCT isa (fun s t => FieldPair M base size m Sl V E counter s t ∧ Pre s ∧ Pre t) c
      (fun s t => FieldPair M base size m Sl W E' counter' s t ∧ Post s ∧ Post t) := by
  intro s t ts tt u v ⟨h,ps,pt⟩ es et
  have tr := hc _ _ _ _ _ _ trivial trivial (hp s t h ps pt) es et
  obtain ⟨_,u',eu,ku,iu,cu,pu⟩ := hw s h.left h.count₁ ps
  obtain ⟨_,v',ev,kv,iv,cv,pv⟩ := hw t h.right h.count₂ pt
  obtain ⟨-,rfl⟩ := Exec.det es eu
  obtain ⟨-,rfl⟩ := Exec.det et ev
  exact ⟨tr,⟨iu,iv,h.pub.keep ku kv (by decide) (by decide),cu,cv⟩,pu,pv⟩

theorem keepsField_relCT {counter counter' : BitVec 32}
    {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fin m} {c : Prog isa}
    {Pre Post : State → Prop} {rs ws : List Reg}
    (hws : ∀ r∈ws,r∈powClob) (hc : RegCT rs c)
    (hp : ∀ s t,FieldPair M base size m Sl V E counter s t → Pre s → Pre t →
      VG.X86.Taint.Agree (nafτ rs) s t)
    (hw : ∀ s,Inv M base size m Sl V E s → s.gpr .esi=counter → Pre s →
      WP isa c s (fun t => t.gpr .esi=counter' ∧ Post t ∧ CKeeps ws s t)) :
    RelCT isa (fun s t => FieldPair M base size m Sl V E counter s t ∧ Pre s ∧ Pre t) c
      (fun s t => FieldPair M base size m Sl V E counter' s t ∧ Post s ∧ Post t) :=
  regFieldProgram_relCT hc hp (fun s hi ct pre => WP.mono (hw s hi ct pre)
    (fun _ ⟨ct,post,hk⟩ => ⟨hk.regs.mono hws,
      hi.of_keeps hk (fun h => by have := hws _ h; contradiction)
        (fun h => by have := hws _ h; contradiction),ct,post⟩))

end VG.Proof.Weierstrass.X86
