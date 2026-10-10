import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSqueezeReady

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

def squeezeAllRegs : List Reg := [.x0,.x1,.x16,.x17,.x6,.x7,.x22,.x23,.x24,.x25,.x26,.x27,.x28]

structure SqueezePost (s t : State) (b : Addr) (off : Nat) (A : Nat→Spec.Sha3.State) : Prop where
 keep : RegKeep squeezeAllRegs s t
 frame : Frame (squeezeCfg b off).writes s.mem t.mem
 first : PairAt t.mem b (Resident.permuted (A 0) 2) (Resident.permuted (A 1) 2)
 second : PairAt t.mem (b+400#64) (Resident.permuted (A 2) 2) (Resident.permuted (A 3) 2)
 streams : ∀i<4,Stream136 t.mem ((squeezeCfg b off).out i) 2 (A i)

theorem squeezeTwo_ok (sha3 : Bool) {s : State} {b : Addr} {off : Nat} {A : Nat→Spec.Sha3.State}
    (ho : off≤272) (hb : s.gpr .x19=b)
    (hP : PairAt s.mem b (A 0) (A 1)) (hQ : PairAt s.mem (b+400#64) (A 2) (A 3))
    (hw : ∀o n,o+n≤8192→InRegions s.wr (b+BitVec.ofNat 64 o) n) :
    WP isa (Impl.MlDsa.AArch64.Optimized.BoundedFour.squeezeTwo sha3 off) s fun t=>
      SqueezePost s t b off A := by
  unfold Impl.MlDsa.AArch64.Optimized.BoundedFour.squeezeTwo
  refine WP.seq (WP.mono (squeezeArgs_ok s ho) fun u ⟨⟨⟨h22,h23,h24,h25,h26,h27,h28,hm⟩,hk⟩,_⟩=>?_)
  rw [hb] at h22 h23 h24 h25 h26 h27
  have hi : SqueezeInv u u (squeezeCfg b off) A 0 := by
    refine ⟨by decide,RegKeep.refl _ _,Frame.refl _ _,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [hm]; exact hP
    · rw [hm]; exact hQ
    · intro i hi; exact stream136_zero _ _ _
    · exact h22
    · exact h23
    · simpa only [SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,ite_true,
        Nat.mul_zero,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using h24
    · simpa only [SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,ite_true,ite_false,
        Nat.mul_zero,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using h25
    · simpa only [SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,ite_true,ite_false,
        Nat.mul_zero,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using h26
    · simpa only [SqueezeCfg.at,SqueezeCfg.out,squeezeCfg,Nat.reduceEqDiff,ite_false,
        Nat.mul_zero,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using h27
    · exact h28
  have hl : SqueezeLayout u (squeezeCfg b off) := squeezeLayout_ok ho
    (by rw [hk.gpr .x19 (by decide),hb]) (fun o n hn=>by
    rw [hk.wr]; exact hw o n hn)
  refine WP.mono (squeezeLoop_ok sha3 hl hi (by decide)) fun t ht=>?_
  have hr : RegKeep [.x22,.x23,.x24,.x25,.x26,.x27,.x28] s u := ⟨hk.gpr,hk.rd,hk.wr,hk.sp⟩
  refine ⟨(hr.trans ht.keep).mono (by decide),?_,ht.first,ht.second,ht.streams⟩
  rw [←hm]; exact ht.frame

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
