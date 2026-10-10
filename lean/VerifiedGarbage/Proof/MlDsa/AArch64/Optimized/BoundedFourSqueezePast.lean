import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSqueezeApart

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

theorem squeezeLayout_past (b : Addr) {off i k j : Nat} (ho : off≤272) (hi : i<4)
    (hkj : k<j) (hj : j<2) :
    ∀r∈(squeezeCfg b off).stepWrites j,
      (rateR ((squeezeCfg b off).at i k)).Disjoint r := by
  intro r hr
  rw [squeezeCfg_at b off hi k]
  simp only [SqueezeCfg.stepWrites,pairWrites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with ((rfl|rfl|rfl)|(rfl|rfl|rfl))|rfl
  · have h := Offset.disjoint b (d := 840+544*i+off+136*k) (n := 136)
      (e := 0) (k := 400) (by omega) (by omega) (by omega)
    simpa only [pairR,rateR,SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,
      ite_true,ite_false,BitVec.add_assoc,←BitVec.ofNat_add,BitVec.add_zero] using h
  · have h := Offset.disjoint b (d := 840+544*i+off+136*k) (n := 136)
      (e := 840+off+136*j) (k := 136) (by omega) (by omega) (by omega)
    simpa only [pairR,rateR,SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,
      ite_true,ite_false,BitVec.add_assoc,←BitVec.ofNat_add,BitVec.add_zero] using h
  · have h := Offset.disjoint b (d := 840+544*i+off+136*k) (n := 136)
      (e := 1384+off+136*j) (k := 136) (by omega) (by omega) (by omega)
    simpa only [pairR,rateR,SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,
      ite_true,ite_false,BitVec.add_assoc,←BitVec.ofNat_add,BitVec.add_zero] using h
  · have h := Offset.disjoint b (d := 840+544*i+off+136*k) (n := 136)
      (e := 400) (k := 400) (by omega) (by omega) (by omega)
    simpa only [pairR,rateR,SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,
      ite_true,ite_false,BitVec.add_assoc,←BitVec.ofNat_add,BitVec.add_zero] using h
  · have h := Offset.disjoint b (d := 840+544*i+off+136*k) (n := 136)
      (e := 1928+off+136*j) (k := 136) (by omega) (by omega) (by omega)
    simpa only [pairR,rateR,SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,
      ite_true,ite_false,BitVec.add_assoc,←BitVec.ofNat_add,BitVec.add_zero] using h
  · have h := Offset.disjoint b (d := 840+544*i+off+136*k) (n := 136)
      (e := 2472+off+136*j) (k := 136) (by omega) (by omega) (by omega)
    simpa only [pairR,rateR,SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,
      ite_true,ite_false,BitVec.add_assoc,←BitVec.ofNat_add,BitVec.add_zero] using h
  · exact Offset.disjoint b (d := 840+544*i+off+136*k) (n := 136)
      (e := Impl.MlDsa.AArch64.Optimized.BoundedFour.oX2) (k := 136)
      (by simp only [Impl.MlDsa.AArch64.Optimized.BoundedFour.oX2]; omega) (by omega) (by decide)

/-- The pairs' writes miss `vg_keccak_f1600_x2`'s working space. -/
theorem squeezeLayout_scratch (b : Addr) {off j : Nat} (ho : off≤272) (hj : j<2) :
    ∀r∈pairWrites (squeezeCfg b off).p ((squeezeCfg b off).at 0 j) ((squeezeCfg b off).at 1 j)++
      pairWrites (squeezeCfg b off).q ((squeezeCfg b off).at 2 j) ((squeezeCfg b off).at 3 j),
      r.Disjoint (X2.callR (squeezeCfg b off).w) := by
  intro r hr
  rw [squeezeCfg_at b off (by decide : 0<4),squeezeCfg_at b off (by decide : 1<4),
    squeezeCfg_at b off (by decide : 2<4),squeezeCfg_at b off (by decide : 3<4)] at hr
  simp only [pairWrites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
  have hw : X2.callR (squeezeCfg b off).w = ⟨b+BitVec.ofNat 64 3024,136⟩ := rfl
  rw [hw]
  have hrate (d : Nat) (hd : d+136≤3024) :
      Region.Disjoint (rateR (b+BitVec.ofNat 64 d)) ⟨b+BitVec.ofNat 64 3024,136⟩ :=
    Offset.disjoint b (d := d) (n := 136) (e := 3024) (k := 136) (by omega) (by omega) (by decide)
  rcases hr with (rfl|rfl|rfl)|(rfl|rfl|rfl)
  · have h := Offset.disjoint b (d := 0) (n := 400) (e := 3024) (k := 136) (by decide) (by decide) (by decide)
    simpa only [pairR,squeezeCfg,BitVec.add_zero] using h
  · exact hrate _ (by omega)
  · exact hrate _ (by omega)
  · exact Offset.disjoint b (d := 400) (n := 400) (e := 3024) (k := 136) (by decide) (by decide) (by decide)
  · exact hrate _ (by omega)
  · exact hrate _ (by omega)

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
