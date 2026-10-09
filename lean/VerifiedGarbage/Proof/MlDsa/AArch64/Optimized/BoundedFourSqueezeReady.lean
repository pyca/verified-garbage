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
  rcases hr with (rfl|rfl|rfl)|(rfl|rfl|rfl)
  · exact ⟨pairR c.p,by simp [SqueezeCfg.writes],fun _ h=>h⟩
  · exact ⟨⟨c.out 0,272⟩,by simp [SqueezeCfg.out,SqueezeCfg.writes],hout 0⟩
  · exact ⟨⟨c.out 1,272⟩,by simp [SqueezeCfg.out,SqueezeCfg.writes],hout 1⟩
  · exact ⟨pairR c.q,by simp [SqueezeCfg.writes],fun _ h=>h⟩
  · exact ⟨⟨c.out 2,272⟩,by simp [SqueezeCfg.out,SqueezeCfg.writes],hout 2⟩
  · exact ⟨⟨c.out 3,272⟩,by simp [SqueezeCfg.out,SqueezeCfg.writes],hout 3⟩

theorem squeezeLayout_ok {s : State} {b : Addr} {off : Nat} (ho : off≤272)
    (hw : ∀o n,o+n≤8192→InRegions s.wr (b+BitVec.ofNat 64 o) n) :
    SqueezeLayout s (squeezeCfg b off) :=
  ⟨fun _ hj=>squeezeLayout_left ho hj hw,fun _ hj=>squeezeLayout_right ho hj hw,
    fun _ hj=>squeezeLayout_apart b ho hj,
    fun _ hi _ _ hkj hj=>squeezeLayout_past b ho hi hkj hj,
    fun _ hj=>squeezeLayout_covers _ hj⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
