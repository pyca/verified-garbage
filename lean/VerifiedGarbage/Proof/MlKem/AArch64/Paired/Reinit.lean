module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.InitCall
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.InitCore
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Block

/-! # Paired-noise prologue, including the register record -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon
open Noise (savedR Saved saves_ok)

theorem reinit_ok {s : State} {p seed : Addr} {ss sb a b k : Nat}
    (hss : ss < 65536) (hsb : sb+32≤32768) (h8 : sb%8=0)
    (hp : s.gpr .x28+BitVec.ofNat 64 ss=p)
    (ha : s.gpr .x28+BitVec.ofNat 64 sb=seed)
    (hin : ∀j<4, InRegions (s.rd++s.wr) (seed+BitVec.ofNat 64 (8*j)) 8)
    (hwr : ∀j<25, InRegions s.wr (wordAddr p j) 16)
    (hap : (Region.mk seed 32).Disjoint (pairR p)) :
    WP isa (.block (ptrTo .x2 .x28 ss ++
      ([mov .x19 .x2] : List Instr) ++ Impl.MlKem.AArch64.Paired.initCore sb a b k ++
      ([.addImm .x .x20 .x19 400,.addImm .x .x21 .x19 904,.movz .x .x22 3 0,.movz .x .x22 5 0] : List Instr))) s fun t =>
      Keep initRegs s t ∧ Frame [pairR p] s.mem t.mem ∧
      t.gpr .x19=p ∧ t.gpr .x20=p+400 ∧ t.gpr .x21=p+904 ∧ t.gpr .x22=5 ∧
      PairAt t.mem p (seedState s.mem seed a k) (seedState s.mem seed b k) := by
  rw [List.append_assoc,List.append_assoc]
  refine wp_ptrTo (by decide) hss fun u hu eu => ?_
  refine wp_mov fun w hw ew => ?_
  change WP isa (.block (Impl.MlKem.AArch64.Paired.initCore sb a b k ++
    ([.addImm .x .x20 .x19 400,.addImm .x .x21 .x19 904,.movz .x .x22 3 0,.movz .x .x22 5 0] : List Instr))) w _
  rw [WP.block_append_iff]
  refine WP.mono (WP.preservedV (initCore_ok hsb h8
    (by rw [ew,eu]; exact hp)
    (by rw [hw.get .x28 (by decide),hu.get .x28 (by decide)]; exact ha)
    (fun j hj => by rw [hw.rd,hw.wr,hu.rd,hu.wr]; exact hin j hj)
    (fun j hj => by rw [hw.wr,hu.wr]; exact hwr j hj) hap)
    (hc := by rfl)) fun z ⟨⟨kz,fz,pz⟩,vz⟩ => ?_
  refine wp_addImm (by decide) fun y hy ey => wp_addImm (by decide) fun q hq eq => wp_movz fun r hr er => wp_movz fun t ht et => wp_nil ?_
  have ksz : Keep [.x6,.x7] w z := ⟨kz.gpr,kz.rd,kz.wr,kz.sp,vz⟩
  have kt : Keep initRegs s t := ((((((hu.keep.trans hw.keep).trans ksz).trans hy.keep).trans hq.keep).trans hr.keep).trans ht.keep).mono (by simp [initRegs])
  have hm : t.mem=z.mem := ht.mem.trans (hr.mem.trans (hq.mem.trans hy.mem))
  have h19 : z.gpr .x19=p := by
    rw [kz.gpr .x19 (by simp),ew,eu]; exact hp
  have mw : w.mem=s.mem := hw.mem.trans hu.mem
  refine ⟨kt,?_,?_,?_,?_,?_,?_⟩
  · rw [hm]; simpa only [mw] using fz
  · rw [ht.get .x19 (by decide),hr.get .x19 (by decide),hq.get .x19 (by decide),hy.get .x19 (by decide),h19]
  · rw [ht.get .x20 (by decide),hr.get .x20 (by decide),hq.get .x20 (by decide),ey,h19]; rfl
  · rw [ht.get .x21 (by decide),hr.get .x21 (by decide),eq,hy.get .x19 (by decide),h19]; rfl
  · rw [et]; rfl
  · rw [hm]; simpa only [mw] using pz

end VG.Proof.MlKem.AArch64.Paired
