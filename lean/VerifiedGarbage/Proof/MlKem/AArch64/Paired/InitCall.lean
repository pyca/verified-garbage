module

import VerifiedGarbage.Proof.MlKem.AArch64.Paired.InitCore
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Saved
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.State
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block

/-! # Paired-noise prologue, including the register record -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon
open Noise (savedR Saved saves_ok)

theorem seedState_frame {m m' : Mem} {seed : Addr} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (Region.mk seed 32).Disjoint r) (n k : Nat) :
    seedState m' seed n k = seedState m seed n k := by
  apply Vector.ext; intro i hi
  simp only [seedState,Vector.getElem_ofFn]
  split
  · rw [hf.readW (r := ⟨seed,32⟩) (Offset.contains_base seed (by omega) (by omega)) hd (by decide)]
  · rfl

def initRegs : List Reg := [.x2,.x19,.x20,.x21,.x22,.x6,.x7]

theorem init_ok {s : State} {p seed : Addr} {ss sb a b k : Nat}
    (hss : ss < 65536) (hsb : sb+32≤32768) (h8 : sb%8=0)
    (hp : s.gpr .x28+BitVec.ofNat 64 ss=p)
    (ha : s.gpr .x28+BitVec.ofNat 64 sb=seed)
    (hin : ∀j<4, InRegions (s.rd++s.wr) (seed+BitVec.ofNat 64 (8*j)) 8)
    (hwr : ∀j<25, InRegions s.wr (wordAddr p j) 16)
    (hsv : ∀j<6, InRegions s.wr (p+BitVec.ofNat 64 (1800+8*j)) 8)
    (has : (Region.mk seed 32).Disjoint (savedR p))
    (hap : (Region.mk seed 32).Disjoint (pairR p))
    (hps : (savedR p).Disjoint (pairR p)) :
    WP isa (.block (ptrTo .x2 .x28 ss ++
      (Paired.saved.zipIdx.map fun (r,i) => .str .x r .x2 (1800+8*i)) ++
      ([mov .x19 .x2] : List Instr) ++ Impl.MlKem.AArch64.Paired.initCore sb a b k ++
      ([.addImm .x .x20 .x19 400,.addImm .x .x21 .x19 904,.movz .x .x22 3 0] : List Instr))) s fun t =>
      Keep initRegs s t ∧ Frame [savedR p,pairR p] s.mem t.mem ∧ Saved p s t.mem ∧
      t.gpr .x19=p ∧ t.gpr .x20=p+400 ∧ t.gpr .x21=p+904 ∧ t.gpr .x22=3 ∧
      PairAt t.mem p (seedState s.mem seed a k) (seedState s.mem seed b k) := by
  rw [List.append_assoc,List.append_assoc,List.append_assoc]
  refine wp_ptrTo (by decide) hss fun u hu eu => ?_
  rw [WP.block_append_iff]
  refine WP.mono (saves_ok (p := p) (by rw [eu]; exact hp)
    (fun j hj => by rw [hu.wr]; exact hsv j hj)) fun v ⟨kv,sv,fv⟩ => ?_
  have sv' : Saved p s v.mem := fun j hj => by
    rw [sv j hj,hu.get _ (by rcases (by omega : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5) with rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]
  have fv' : Frame [savedR p] s.mem v.mem := by rw [hu.mem] at fv; exact fv
  refine wp_mov fun w hw ew => ?_
  change WP isa (.block (Impl.MlKem.AArch64.Paired.initCore sb a b k ++
    ([.addImm .x .x20 .x19 400,.addImm .x .x21 .x19 904,.movz .x .x22 3 0] : List Instr))) w _
  rw [WP.block_append_iff]
  refine WP.mono (WP.preservedV (initCore_ok hsb h8
    (by rw [ew,kv.gpr .x2 (by simp),eu]; exact hp)
    (by rw [hw.get .x28 (by decide),kv.gpr .x28 (by simp),hu.get .x28 (by decide)]; exact ha)
    (fun j hj => by rw [hw.rd,hw.wr,kv.rd,kv.wr,hu.rd,hu.wr]; exact hin j hj)
    (fun j hj => by rw [hw.wr,kv.wr,hu.wr]; exact hwr j hj) hap)
    (hc := by rfl)) fun z ⟨⟨kz,fz,pz⟩,vz⟩ => ?_
  refine wp_addImm (by decide) fun y hy ey => wp_addImm (by decide) fun q hq eq => wp_movz fun t ht et => wp_nil ?_
  have ksz : Keep [.x6,.x7] w z := ⟨kz.gpr,kz.rd,kz.wr,kz.sp,vz⟩
  have kt : Keep initRegs s t := ((((((hu.keep.trans kv).trans hw.keep).trans ksz).trans hy.keep).trans hq.keep).trans ht.keep).mono (by simp [initRegs])
  have hm : t.mem=z.mem := ht.mem.trans (hq.mem.trans hy.mem)
  have h19 : z.gpr .x19=p := by
    rw [kz.gpr .x19 (by simp),ew,kv.gpr .x2 (by simp),eu]; exact hp
  have fw : Frame [savedR p] s.mem w.mem := by rw [hw.mem]; exact fv'
  have state_eq (idx : Nat) : seedState w.mem seed idx k = seedState s.mem seed idx k :=
    seedState_frame fw (by intro r hr; rw [List.mem_singleton.mp hr]; exact has) idx k
  refine ⟨kt,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hm]; exact (fw.mono (by simp)).trans (fz.mono (by simp))
  · rw [hm]; apply Saved.frame (m := w.mem) _ fz (by intro r hr; rw [List.mem_singleton.mp hr]; exact hps)
    rw [hw.mem]; exact sv'
  · rw [ht.get .x19 (by decide),hq.get .x19 (by decide),hy.get .x19 (by decide),h19]
  · rw [ht.get .x20 (by decide),hq.get .x20 (by decide),ey,h19]; rfl
  · rw [ht.get .x21 (by decide),eq,hy.get .x19 (by decide),h19]; rfl
  · rw [et]; rfl
  · rw [hm]; simpa only [state_eq a,state_eq b] using pz

end VG.Proof.MlKem.AArch64.Paired
