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
  rcases hr with (rfl|rfl|rfl)|(rfl|rfl|rfl)
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

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
