module

public import VerifiedGarbage.Proof.MlKem.AArch64.Lay
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.InitCall
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SqueezeBlock
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `MlKem.AArch64.Paired.SingleStep`, which the modules that import this one used -/

section

/-! ### `MlKem.AArch64.Paired.SingleWords`, which only this module used -/

section

/-! # Serialize one lane of the paired permutation for the singleton fallback -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
variable {sha3 : Bool}
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

def singleWords : List Instr := (List.range 21).flatMap fun i =>
 [.ldr .x .x6 .x19 (16*i),.str .x .x6 .x20 (8*i)]

theorem singleWords_ok {s : State} {p a : Addr} {A B : Spec.Sha3.State}
    (hp : s.gpr .x19=p) (ha : s.gpr .x20=a) (pair : PairAt s.mem p A B)
    (hin : ∀i<21,InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 (16*i)) 8)
    (hout : ∀i<21,InRegions s.wr (outAddr a i) 8)
    (hd : (pairR p).Disjoint (rateR21 a)) :
    WP isa (.block singleWords) s fun t =>
      Keep [.x6] s t ∧ Frame [rateR21 a] s.mem t.mem ∧ Rate21 t.mem a A := by
  apply wp_range_flatMap (M := isa) (N := 21)
    (fun k t => Keep [.x6] s t ∧ Frame [rateR21 a] s.mem t.mem ∧
      ∀i<k,t.mem.readW (outAddr a i) 64=A[i]!)
  · intro k t hk ⟨kt,ft,old⟩
    refine wp_ldrx (a := p+BitVec.ofNat 64 (16*k)) (by constructor <;> omega_arith)
      (by rw [kt.gpr .x19 (by decide),hp])
      (by rw [kt.rd,kt.wr]; exact hin k hk) fun u hu eu => ?_
    refine wp_strx (a := outAddr a k) (by constructor <;> omega_arith)
      (by rw [hu.get .x20 (by decide),kt.gpr .x20 (by decide),ha]; rfl)
      (by rw [hu.wr,kt.wr]; exact hout k hk) fun v hv => wp_nil ?_
    have hm : v.mem=t.mem.writeW (outAddr a k) (t.mem.readW (p+BitVec.ofNat 64 (16*k)) 64) := by
      rw [hv.mem,eu,hu.mem]
    have val : t.mem.readW (p+BitVec.ofNat 64 (16*k)) 64=A[k]! := by
      rw [ft.readW (r := pairR p) (Offset.contains_base p (by omega_using [hk]) (by omega_using [hk]))
        (by intro r hr; rw [List.mem_singleton.mp hr]; exact hd) (by decide)]
      exact X2.word0 pair (by omega_using [hk])
    refine ⟨((kt.trans hu.keep).trans hv.keep).mono (by simp),?_,fun i hi => ?_⟩
    · rw [hm]
      have hca : (rateR21 a).Contains (outAddr a k) 8 := Offset.contains_base a (by omega_using [hk]) (by omega_using [hk])
      exact ft.writeW (by simp) _ hca
    · rw [hm]
      by_cases he : i=k
      · subst i; rw [Mem.readW_writeW_self64,val]
      · rw [Mem.readW_writeW_sep (Offset.sep a (d := 8*i) (e := 8*k) (n := 8) (k := 8)
          (by omega_using [he]) (by omega_using [hk, hi]) (by omega_using [hk])) (by decide)]
        exact old i (by omega_using [hi, he])
  · exact Nat.le_refl _
  · exact ⟨⟨fun _ _ => rfl,rfl,rfl,rfl,fun _ _ => rfl⟩,Frame.refl _ _,fun i hi => by omega⟩

end VG.Proof.MlKem.AArch64.Paired

end

end


/-! # One singleton fallback permutation and serialization -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
variable {sha3 : Bool}
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

def singleRegs : List Reg := X2.volatile++[.x20,.x22]
def singleBody (sha3 : Bool) : Prog isa := .seq (Impl.Sha3.AArch64.Neon.X2.call sha3 .x19 .x19 1536)
 (.block (singleWords ++ [.addImm .x .x20 .x20 168,.subImm .x .x22 .x22 1]))

theorem singleStep_ok {s : State} {p a : Addr} {A B : Spec.Sha3.State}
    (hp : s.gpr .x19=p) (ha : s.gpr .x20=a) (pair : PairAt s.mem p A B)
    (hin : ∀i<21,InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 (16*i)) 8)
    (hout : ∀i<21,InRegions s.wr (outAddr a i) 8)
    (hd : (pairR p).Disjoint (rateR21 a))
    (hpw : (pairR p).Disjoint (X2.callR (p+1536)))
    (hcov : Covers [pairR p,X2.callR (p+1536)] s.wr) :
    WP isa (singleBody sha3) s fun t =>
      Keep singleRegs s t ∧ PairAt t.mem p (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B) ∧
      Rate21 t.mem a (Spec.Sha3.keccakF A) ∧
      Frame [pairR p,rateR21 a,X2.callR (p+1536)] s.mem t.mem ∧
      t.gpr .x20=a+168 ∧ t.gpr .x22=s.gpr .x22-1 := by
  refine WP.seq (WP.mono (X2.callAny_ok sha3 (by decide) (by decide) (by decide) (by decide)
    (by decide) hp (by rw [hp]; rfl) hpw pair hcov) fun u ⟨ku,vu,fu,pu⟩ => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (singleWords_ok ((ku.gpr .x19 (by decide)).trans hp)
    ((ku.gpr .x20 (by decide)).trans ha) pu
    (fun i hi => by rw [ku.rd,ku.wr]; exact hin i hi)
    (fun i hi => by rw [ku.wr]; exact hout i hi) hd) fun v ⟨kv,fv,av⟩ => ?_
  refine wp_addImm (by decide) fun w hw ew => wp_subImm (by decide) fun t ht et => wp_nil ?_
  have ou : Keep X2.volatile s u := ⟨ku.gpr,ku.rd,ku.wr,ku.sp,vu⟩
  have ot : Only [.x20,.x22] v t := (hw.trans ht).mono (by simp)
  refine ⟨(((ou.trans kv).trans ot.keep)).mono (by decide),?_,?_,?_,?_,?_⟩
  · intro i hi; rw [ot.mem,fv.read (pair_contains p hi)
      (by intro r hr; rw [List.mem_singleton.mp hr]; exact hd) (by decide)]; exact pu i hi
  · rw [ot.mem]; exact av
  · rw [ot.mem]; exact (fu.mono (by simp)).trans (fv.mono (by simp))
  · rw [ht.get .x20 (by decide),ew,kv.gpr .x20 (by decide),ku.gpr .x20 (by decide),ha]; rfl
  · rw [et,hw.get .x22 (by decide),kv.gpr .x22 (by decide),ku.gpr .x22 (by decide)]; rfl

end VG.Proof.MlKem.AArch64.Paired

end

end

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
  refine WP.mono (reinit_ok (by omega_using [hss]) hsb h8
    (by rw [hv.gpr,hu.gpr]; exact hbase) (by rw [hv.gpr,hu.gpr]; exact hseed)
    (fun j hj => by rw [hv.rd,hv.wr,hu.rd,hu.wr]; exact hin j hj)
    (fun j hj => by rw [hv.wr,hu.wr]; exact Noise.inScratch hc (by omega_using [hj] : 16*j+16≤2048) (by decide))
    (hsep.sub_right (Region.sub_prefix (by decide : 400≤2048)))) fun t ⟨kt,ft,h19,h20,h21,h22,pt⟩ => ?_
  have eqseed : seedState v.mem seed a k=seedState s.mem seed a k := seedState_frame fv
    (by intro r hr; rw [List.mem_singleton.mp hr]; exact hsep.sub_right (Offset.sub_base p (by decide))) a k
  exact ⟨((hu.keep.trans hv.keep).trans kt).mono (by simp),
    (fv.mono (by simp)).trans (ft.mono (by simp)),
    flagv.frame ft (by intro r hr; rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base p (by decide) (by decide)),
    h19,h20,h21,h22,by simpa only [eqseed] using pt⟩

end VG.Proof.MlKem.AArch64.Paired
