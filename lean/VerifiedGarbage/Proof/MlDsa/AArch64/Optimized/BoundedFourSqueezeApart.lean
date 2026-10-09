import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSqueezeLayout

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

theorem squeezeLayout_apart (b : Addr) {off j : Nat} (ho : off≤272) (hj : j<2) :
    ∀r∈pairWrites (squeezeCfg b off).p ((squeezeCfg b off).at 0 j) ((squeezeCfg b off).at 1 j),
    ∀t∈pairWrites (squeezeCfg b off).q ((squeezeCfg b off).at 2 j) ((squeezeCfg b off).at 3 j),r.Disjoint t := by
  intro r hr t ht
  simp only [pairWrites,List.mem_cons,List.not_mem_nil,or_false] at hr ht
  rcases hr with rfl|rfl|rfl <;> rcases ht with rfl|rfl|rfl
  · have h := Offset.disjoint b (d := 0) (n := 400) (e := 400) (k := 400)
      (by omega) (by omega) (by omega)
    simpa only [pairR,rateR,SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,
      ite_true,ite_false,BitVec.add_assoc,←BitVec.ofNat_add,BitVec.add_zero] using h
  · have h := Offset.disjoint b (d := 0) (n := 400) (e := 1928+off+136*j) (k := 136)
      (by omega) (by omega) (by omega)
    simpa only [pairR,rateR,SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,
      ite_true,ite_false,BitVec.add_assoc,←BitVec.ofNat_add,BitVec.add_zero] using h
  · have h := Offset.disjoint b (d := 0) (n := 400) (e := 2472+off+136*j) (k := 136)
      (by omega) (by omega) (by omega)
    simpa only [pairR,rateR,SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,
      ite_true,ite_false,BitVec.add_assoc,←BitVec.ofNat_add,BitVec.add_zero] using h
  · have h := Offset.disjoint b (d := 840+off+136*j) (n := 136) (e := 400) (k := 400)
      (by omega) (by omega) (by omega)
    simpa only [pairR,rateR,SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,
      ite_true,ite_false,BitVec.add_assoc,←BitVec.ofNat_add,BitVec.add_zero] using h
  · have h := Offset.disjoint b (d := 840+off+136*j) (n := 136) (e := 1928+off+136*j) (k := 136)
      (by omega) (by omega) (by omega)
    simpa only [pairR,rateR,SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,
      ite_true,ite_false,BitVec.add_assoc,←BitVec.ofNat_add,BitVec.add_zero] using h
  · have h := Offset.disjoint b (d := 840+off+136*j) (n := 136) (e := 2472+off+136*j) (k := 136)
      (by omega) (by omega) (by omega)
    simpa only [pairR,rateR,SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,
      ite_true,ite_false,BitVec.add_assoc,←BitVec.ofNat_add,BitVec.add_zero] using h
  · have h := Offset.disjoint b (d := 1384+off+136*j) (n := 136) (e := 400) (k := 400)
      (by omega) (by omega) (by omega)
    simpa only [pairR,rateR,SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,
      ite_true,ite_false,BitVec.add_assoc,←BitVec.ofNat_add,BitVec.add_zero] using h
  · have h := Offset.disjoint b (d := 1384+off+136*j) (n := 136) (e := 1928+off+136*j) (k := 136)
      (by omega) (by omega) (by omega)
    simpa only [pairR,rateR,SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,
      ite_true,ite_false,BitVec.add_assoc,←BitVec.ofNat_add,BitVec.add_zero] using h
  · have h := Offset.disjoint b (d := 1384+off+136*j) (n := 136) (e := 2472+off+136*j) (k := 136)
      (by omega) (by omega) (by omega)
    simpa only [pairR,rateR,SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,
      ite_true,ite_false,BitVec.add_assoc,←BitVec.ofNat_add,BitVec.add_zero] using h

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
