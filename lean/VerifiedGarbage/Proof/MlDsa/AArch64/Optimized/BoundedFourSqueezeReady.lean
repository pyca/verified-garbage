import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSqueezePast

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

theorem squeezeLayout_covers (c : SqueezeCfg) {j : Nat} (hj : j<2) :
    ∀r∈c.stepWrites j,∃t∈c.writes,Region.Sub r t := by
  intro r hr
  simp only [SqueezeCfg.stepWrites,pairWrites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
  have hout (i : Nat) : Region.Sub (rateR (c.at i j)) ⟨c.out i,272⟩ :=
    Offset.sub_base _ (by omega)
  rcases hr with ((rfl|rfl|rfl)|(rfl|rfl|rfl))|rfl
  · exact ⟨pairR c.p,by simp [SqueezeCfg.writes],fun _ h=>h⟩
  · exact ⟨⟨c.out 0,272⟩,by simp [SqueezeCfg.out,SqueezeCfg.writes],hout 0⟩
  · exact ⟨⟨c.out 1,272⟩,by simp [SqueezeCfg.out,SqueezeCfg.writes],hout 1⟩
  · exact ⟨pairR c.q,by simp [SqueezeCfg.writes],fun _ h=>h⟩
  · exact ⟨⟨c.out 2,272⟩,by simp [SqueezeCfg.out,SqueezeCfg.writes],hout 2⟩
  · exact ⟨⟨c.out 3,272⟩,by simp [SqueezeCfg.out,SqueezeCfg.writes],hout 3⟩
  · exact ⟨X2.callR c.w,by simp [SqueezeCfg.writes],fun _ h=>h⟩

theorem squeezeLayout_call {s : State} {b : Addr} {off d : Nat} (hd : d+400≤3024)
    (hw : ∀o n,o+n≤8192→InRegions s.wr (b+BitVec.ofNat 64 o) n) :
    Covers [pairR (b+BitVec.ofNat 64 d),X2.callR (squeezeCfg b off).w] s.wr := by
  refine Covers.of_forall fun r hr => ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact Covers.one (hw d 400 (by omega))
  · exact Covers.one (hw 3024 136 (by decide))

theorem squeezeLayout_ok {s : State} {b : Addr} {off : Nat} (ho : off≤272) (hb : s.gpr .x19=b)
    (hw : ∀o n,o+n≤8192→InRegions s.wr (b+BitVec.ofNat 64 o) n) :
    SqueezeLayout s (squeezeCfg b off) :=
  ⟨fun _ hj=>squeezeLayout_left ho hj hw,fun _ hj=>squeezeLayout_right ho hj hw,
    fun _ hj=>squeezeLayout_apart b ho hj,
    fun _ hi _ _ hkj hj=>squeezeLayout_past b ho hi hkj hj,
    fun _ hj=>squeezeLayout_covers _ hj,by rw [hb]; rfl,
    fun _ hj=>squeezeLayout_scratch b ho hj,
    by have h := squeezeLayout_call (off := off) (d := 0) (by decide) hw
       rwa [BitVec.add_zero] at h,
    squeezeLayout_call (off := off) (d := 400) (by decide) hw⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
