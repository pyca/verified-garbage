module

public import VerifiedGarbage.Proof.MlKem.AArch64.Lay
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.InitCall

import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.InitCore
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Block
/-! # Preserve the outer flags while restarting a singleton stream -/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Paired/Reinit.lean`, which only this module imported.
section

/-! # Paired-noise prologue, including the register record -/
section
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
end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon

def flagR (p : Addr) : Region := ⟨p+1848,16⟩
def Flags (p : Addr) (s : State) (m : Mem) : Prop :=
 m.readW (p+1848) 64=s.gpr .x22 ∧ m.readW (p+1856) 64=s.gpr .x23

theorem Flags.frame {p : Addr} {s : State} {m m' : Mem} (h : Flags p s m)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀r∈rs,(flagR p).Disjoint r) : Flags p s m' := by
  constructor
  · rw [hf.readW (r := flagR p) (by simpa only [BitVec.add_zero,flagR,Nat.reduceDiv] using
      (Offset.contains_base (p+1848) (d := 0) (n := 8) (k := 16) (by decide) (by decide))) hd (by decide)]; exact h.1
  · have hc : (flagR p).Contains (p+1856) 8 := by
      change (Region.mk (p+BitVec.ofNat 64 1848) 16).Contains (p+BitVec.ofNat 64 1856) 8
      rw [show p+BitVec.ofNat 64 1856=(p+BitVec.ofNat 64 1848)+BitVec.ofNat 64 8 by bv_omega]
      exact Offset.contains_base _ (by decide) (by decide)
    rw [hf.readW hc hd (by decide)]; exact h.2

theorem fullInit_eq {sb ss a k : Nat} (hss : ss<4096) :
    Impl.MlKem.AArch64.Paired.fullInit sb ss a k =
      ([.str .x .x22 .x19 1848,.str .x .x23 .x19 1856] : List Instr) ++ ptrTo .x2 .x28 ss ++
      ([mov .x19 .x2] : List Instr) ++ Impl.MlKem.AArch64.Paired.initCore sb a a k ++
      ([.addImm .x .x20 .x19 400,.addImm .x .x21 .x19 904,.movz .x .x22 3 0,.movz .x .x22 5 0] : List Instr) := by
  simp only [Impl.MlKem.AArch64.Paired.fullInit,Impl.MlKem.AArch64.Paired.init,
    ptrTo,ite_eq_left hss,Impl.MlKem.AArch64.Paired.saved]
  simp only [List.zipIdx_cons,List.zipIdx_nil,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    List.take_succ_cons,List.take_zero,List.drop_succ_cons,List.drop_zero,List.append_assoc]

theorem fullInit_ok {s : State} {p seed : Addr} {sb ss a k : Nat}
    (hss : ss<4096) (hsb : sb+32≤32768) (h8 : sb%8=0)
    (hp : s.gpr .x19=p) (hbase : s.gpr .x28+BitVec.ofNat 64 ss=p)
    (hseed : s.gpr .x28+BitVec.ofNat 64 sb=seed)
    (hin : ∀j<4, InRegions (s.rd++s.wr) (seed+BitVec.ofNat 64 (8*j)) 8)
    (hc : Covers [⟨p,2048⟩] s.wr) (hsep : (Region.mk seed 32).Disjoint ⟨p,2048⟩) :
    WP isa (.block (Impl.MlKem.AArch64.Paired.fullInit sb ss a k)) s fun t =>
      Keep initRegs s t ∧ Frame [flagR p,pairR p] s.mem t.mem ∧ Flags p s t.mem ∧
      t.gpr .x19=p ∧ t.gpr .x20=p+400 ∧ t.gpr .x21=p+904 ∧ t.gpr .x22=5 ∧
      PairAt t.mem p (seedState s.mem seed a k) (seedState s.mem seed a k) := by
  rw [fullInit_eq hss,List.append_assoc,List.append_assoc,List.append_assoc]
  refine wp_strx (a := p+1848) (by decide) (by rw [hp]; rfl)
    (Noise.inScratch hc (by decide : 1848+8≤2048) (by decide)) fun u hu => ?_
  refine wp_strx (a := p+1856) (by decide) (by rw [hu.gpr,hp]; rfl)
    (by rw [hu.wr]; exact Noise.inScratch hc (by decide : 1856+8≤2048) (by decide)) fun v hv => ?_
  have mv : v.mem=(s.mem.writeW (p+1848) (s.gpr .x22)).writeW (p+1856) (s.gpr .x23) := by
    rw [hv.mem,hu.mem,hu.gpr]
  have fv : Frame [flagR p] s.mem v.mem := by
    rw [mv]
    have h0 : (flagR p).Contains (p+1848) 8 := by simpa only [BitVec.add_zero,flagR,Nat.reduceDiv] using
      (Offset.contains_base (p+1848) (d := 0) (n := 8) (k := 16) (by decide) (by decide))
    have h8 : (flagR p).Contains (p+1856) 8 := by
      change (Region.mk (p+BitVec.ofNat 64 1848) 16).Contains (p+BitVec.ofNat 64 1856) 8
      rw [show p+BitVec.ofNat 64 1856=(p+BitVec.ofNat 64 1848)+BitVec.ofNat 64 8 by bv_omega]
      exact Offset.contains_base _ (by decide) (by decide)
    exact ((Frame.refl _ _).writeW (by simp) _ h0).writeW (by simp) _ h8
  have flagv : Flags p s v.mem := by
    rw [Flags,mv]
    constructor
    · rw [Mem.readW_writeW_sep (Offset.sep p (d := 1848) (e := 1856) (n := 8) (k := 8)
        (by decide) (by decide) (by decide)) (by decide),Mem.readW_writeW_self64]
    · exact Mem.readW_writeW_self64 _ _ _
  change WP isa (.block (ptrTo .x2 .x28 ss ++ ([mov .x19 .x2] ++
    (Impl.MlKem.AArch64.Paired.initCore sb a a k ++
    [.addImm .x .x20 .x19 400,.addImm .x .x21 .x19 904,.movz .x .x22 3 0,.movz .x .x22 5 0])))) v _
  rw [← List.append_assoc,← List.append_assoc]
  refine WP.mono (reinit_ok (by omega) hsb h8
    (by rw [hv.gpr,hu.gpr]; exact hbase) (by rw [hv.gpr,hu.gpr]; exact hseed)
    (fun j hj => by rw [hv.rd,hv.wr,hu.rd,hu.wr]; exact hin j hj)
    (fun j hj => by rw [hv.wr,hu.wr]; exact Noise.inScratch hc (by omega : 16*j+16≤2048) (by decide))
    (hsep.sub_right (Region.sub_prefix (by decide : 400≤2048)))) fun t ⟨kt,ft,h19,h20,h21,h22,pt⟩ => ?_
  have eqseed : seedState v.mem seed a k=seedState s.mem seed a k := seedState_frame fv
    (by intro r hr; rw [List.mem_singleton.mp hr]; exact hsep.sub_right (Offset.sub_base p (by decide))) a k
  exact ⟨((hu.keep.trans hv.keep).trans kt).mono (by simp),
    (fv.mono (by simp)).trans (ft.mono (by simp)),
    flagv.frame ft (by intro r hr; rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base p (by decide) (by decide)),
    h19,h20,h21,h22,by simpa only [eqseed] using pt⟩

end VG.Proof.MlKem.AArch64.Paired
