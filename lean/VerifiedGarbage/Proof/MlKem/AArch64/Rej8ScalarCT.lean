module

public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Public
meta import VerifiedGarbage.Impl.MlKem.AArch64.Sample
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT

/-! # Scalar tails branch only on candidates derived from the public seed -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem
open VG.Impl.MlKem.AArch64

def scalarTail (w16 : Bool := false) : Prog isa := .ite (.zero .x .x4) (.block [])
  (.seq (.block (sampleAccept .x11 w16)) (.ite (.zero .x .x4) (.block []) (.block (sampleAccept .x12 w16))))

theorem chunk_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x2])) (.block sampleChunk) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x2]) (fun _ _ _ _ h => h) (by taint_decide)

theorem scalarTail_ct (w16 : Bool) : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x3,.x4,.x9,.x11,.x12])) (scalarTail w16) := by
  unfold scalarTail
  cases w16 <;> exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x3,.x4,.x9,.x11,.x12])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem scalarBody_relCT {w16 : Bool} {initial : List Zq} {N t : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ u₀ : State} (ps : EnvW w16 N B bP aP s₀) (pu : EnvW w16 N B bP aP u₀)
    (hsp : s₀.sp=u₀.sp) (ht : t<N) :
    RelCT isa (fun s u => Scalar.InvW w16 initial N B bP aP s₀ t s ∧ Scalar.InvW w16 initial N B bP aP u₀ t u)
      (sampleBody w16) (fun s u => Scalar.InvW w16 initial N B bP aP s₀ (t+1) s ∧
        Scalar.InvW w16 initial N B bP aP u₀ (t+1) u) := by
  intro s u tr ur s' u' hp es eu
  have hpub := inv_public hp.1 hp.2 hsp
  have trace : tr=ur := by
    cases es with
    | @seq _ _ _ a _ tr₁ tr₂ ep er =>
      cases eu with
      | @seq _ _ _ b _ ur₁ ur₂ fp fr =>
        have htr := chunk_ct s u tr₁ ur₁ a b trivial trivial
          ⟨hpub.1,fun r hr => by
            have hr' : r=.x2 := by simpa only [Taint.ofRegs,RegSet.mem_ofList,List.mem_singleton] using hr
            subst r; exact hpub.2 .x2 (by simp)⟩ ep fp
        obtain ⟨_,a',epa,ha,ka,_,_,va,wa⟩ := Scalar.chunk_ok ps.toLPreW ht hp.1
        obtain ⟨_,b',fpb,hb,kb,_,_,vb,wb⟩ := Scalar.chunk_ok pu.toLPreW ht hp.2
        obtain ⟨_,rfl⟩ := Exec.det ep epa
        obtain ⟨_,rfl⟩ := Exec.det fp fpb
        have hrest := scalarTail_ct w16 a b tr₂ ur₂ s' u' trivial trivial
          ⟨ka.sp.trans (hpub.1.trans kb.sp.symm),fun r hr => by
            have hr' : r=.x3 ∨ r=.x4 ∨ r=.x9 ∨ r=.x11 ∨ r=.x12 := by
              simpa only [Taint.ofRegs,RegSet.mem_ofList,List.mem_cons,List.not_mem_nil,or_false] using hr
            rcases hr' with rfl|rfl|rfl|rfl|rfl
            · rw [ha.x3,hb.x3]
            · exact BitVec.eq_of_toNat_eq (ha.x4.trans hb.x4.symm)
            · exact BitVec.eq_of_toNat_eq (ha.x9.trans hb.x9.symm)
            · exact BitVec.eq_of_toNat_eq (va.trans vb.symm)
            · exact BitVec.eq_of_toNat_eq (wa.trans wb.symm)⟩ er fr
        rw [htr,hrest]
  obtain ⟨_,a,ea,ha,_⟩ := Scalar.body_ok ps.toLPreW ht hp.1
  obtain ⟨_,b,eb,hb,_⟩ := Scalar.body_ok pu.toLPreW ht hp.2
  obtain ⟨_,rfl⟩ := Exec.det es ea
  obtain ⟨_,rfl⟩ := Exec.det eu eb
  exact ⟨trace,ha,hb⟩

end VG.Proof.MlKem.AArch64.Rej8
