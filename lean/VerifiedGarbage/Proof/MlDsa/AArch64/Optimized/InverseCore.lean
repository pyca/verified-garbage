module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalLoop
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFirstLoop
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSetup
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseScale
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackInit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalRoots
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Loads
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseLocalTable
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.Framework.Block

/-! ### `MlDsa.AArch64.Optimized.InverseMiddle`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.InverseHoisted`, which only this module used -/

section

/-! ## From `InverseInitConst.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (wp_scalar wp_vop)
open VG.Proof.MlDsa.AArch64.Optimized.ResidentMask (ConstKeep)
open VG.Impl.MlDsa.AArch64.Arith (movW)

def insertWord (d : VReg) (i n : Nat) : List Instr :=
  movW .x9 n ++ [.vop (.ins .s4 d i .x9)]

theorem insertWord_ok (s : State) (d : VReg) (n : Nat) {i : Nat} (hi : i<4) :
    WP isa (.block (insertWord d i n)) s fun t =>
      ConstKeep d s t ∧ t.v d=setLane (s.v d) 32 i (BitVec.ofNat 32 n) := by
  unfold insertWord
  refine wp_scalar (by rfl) (VG.Proof.MlDsa.AArch64.Arith.movW_ok .x9 _ s)
    fun a ⟨⟨ha,hm⟩,hk⟩ hv => ?_
  refine wp_vop (d := d) (x := setLane (a.v d) 32 i ((a.gpr .x9).setWidth 32)) (by simp [VOp.eval,hi])
    fun t ht => WP.block_nil_iff.mpr ⟨?_,?_⟩
  · refine ⟨fun r hr => ?_,fun r hr => ?_,?_,?_,?_,?_⟩
    · rw [ht.gpr,hk.gpr r (by simpa using hr)]
    · rw [ht.other r hr,hv]
    · rw [ht.mem,hm]
    · rw [ht.rd,hk.rd]
    · rw [ht.wr,hk.wr]
    · rw [ht.sp,hk.sp]
  · rw [ht.v,ha,hv]
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 32≤64),BitVec.setWidth_eq,BitVec.natCast_eq_ofNat]

def cvWords (a b c d : Nat) : BitVec 128 :=
  setLane (setLane (setLane (HighPack.repeatedWord a) 32 1 (BitVec.ofNat 32 b))
    32 2 (BitVec.ofNat 32 c)) 32 3 (BitVec.ofNat 32 d)

theorem cv4_ok (s : State) (r : VReg) (a b c d : Nat) (hb : b≠a) (hc : c≠a) (hd : d≠a) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.Inverse.cv r [a,b,c,d])) s fun t =>
      ConstKeep r s t ∧ t.v r=cvWords a b c d := by
  have he : VG.Impl.MlDsa.AArch64.Optimized.Inverse.cv r [a,b,c,d]=
      VG.Impl.MlDsa.AArch64.Optimized.HighPack.vc r a ++
      insertWord r 1 b ++ insertWord r 2 c ++ insertWord r 3 d := by
    simp [VG.Impl.MlDsa.AArch64.Optimized.Inverse.cv,VG.Impl.MlDsa.AArch64.Optimized.HighPack.vc,
      insertWord,hb,hc,hd,List.range_succ,List.append_assoc]
  rw [he]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok s r a) fun s₁ h₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (insertWord_ok s₁ r b (by decide : 1<4)) fun s₂ h₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (insertWord_ok s₂ r c (by decide : 2<4)) fun s₃ h₃ => ?_
  refine WP.mono (insertWord_ok s₃ r d (by decide : 3<4)) fun t h₄ => ?_
  refine ⟨((h₁.1.trans h₂.1).trans h₃.1).trans h₄.1,?_⟩
  rw [h₄.2,h₃.2,h₂.2,h₁.2]
  rfl

def scaleConst : List Instr := VG.Impl.MlDsa.AArch64.Optimized.Inverse.cv .v30
  [16382,VG.Impl.MlDsa.AArch64.Optimized.Inverse.bar 16382,
   (VG.Impl.MlDsa.AArch64.Optimized.Inverse.z 1*16382)%8380417,
   VG.Impl.MlDsa.AArch64.Optimized.Inverse.bar ((VG.Impl.MlDsa.AArch64.Optimized.Inverse.z 1*16382)%8380417)]

def scaleVector : BitVec 128 := cvWords 16382 4197891 8085692 2071960303

theorem folded_value_eq : (VG.Impl.MlDsa.AArch64.Optimized.Inverse.z 1*16382)%8380417=8085692 := by decide +kernel

theorem scaleConst_ok (s : State) : WP isa (.block scaleConst) s fun t =>
    ConstKeep .v30 s t ∧ t.v .v30=scaleVector := by
  have he : scaleConst=VG.Impl.MlDsa.AArch64.Optimized.Inverse.cv .v30 [16382,4197891,8085692,2071960303] := by
    simp only [scaleConst,folded_value_eq]
    rfl
  rw [he]
  exact cv4_ok s .v30 _ _ _ _ (by decide) (by decide) (by decide)

theorem scaleVector_ready {s : State} (h : s.v .v30=scaleVector) : ScaleRoots s := by
  rw [ScaleRoots,h]
  decide +kernel

theorem scaleVector_folded {s : State} (h : s.v .v30=scaleVector) :
    vword (s.v .v30) 2=BitVec.ofInt 32 (finalZ 6 0) ∧
    vword (s.v .v30) 3=BitVec.ofInt 32 (reciprocal (finalZ 6 0)) := by
  rw [h]
  simp only [finalZ,finalValue,show ¬(6<4) by decide,show ¬(6<6) by decide,ite_false,folded_value_eq]
  decide +kernel

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `InverseHoisted.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

def tailRootReg (j : Nat) : VReg := if j=0 then .v22 else .v23
def tailRecipReg (j : Nat) : VReg := if j=0 then .v28 else .v29

def Hoisted (s : State) : Prop := ∀ j : Fin 2, ∀ e<4,
  vword (s.v (tailRootReg j.val)) e=BitVec.ofInt 32 (VG.Impl.MlDsa.AArch64.Optimized.Inverse.z (7-(4*j.val+e)) : Int) ∧
  vword (s.v (tailRecipReg j.val)) e=BitVec.ofInt 32 (reciprocal (VG.Impl.MlDsa.AArch64.Optimized.Inverse.z (7-(4*j.val+e)) : Int))

def tailLoads : List (VReg × Nat) := [(.v22,0),(.v23,16),(.v28,32),(.v29,48)]
def tailLoadCode : List Instr := tailLoads.map fun p => Instr.ldrq p.1 .x1 p.2

theorem tailLoads_mem (j : Fin 2) :
    (tailRootReg j.val,16*j.val)∈tailLoads ∧ (tailRecipReg j.val,32+16*j.val)∈tailLoads := by
  revert j
  decide +kernel

theorem tailLoad_ok {s : State} {p : Addr} {rest : List Instr} {Q : State → Prop}
    (ht : InverseTable.Words s.mem p) (hx : s.gpr .x1=p+3840)
    (hr : ∀ off∈[0,16,32,48], InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (k : ∀ t, VChg [.v22,.v23,.v28,.v29] s t → Hoisted t → WP isa (.block rest) t Q) :
    WP isa (.block (tailLoadCode ++ rest)) s Q := by
  unfold tailLoadCode
  refine load_many_ok tailLoads .x1 (by decide) (by decide) ?_ fun t hc hv => ?_
  · intro a ha
    exact hr a.2 (by simpa only [tailLoads,List.map_cons,List.map_nil,Prod.snd,List.mem_cons,List.not_mem_nil,or_false] using
      List.mem_map_of_mem (f := Prod.snd) ha)
  · refine k t hc ?_
    intro j e he
    rw [hv _ (tailLoads_mem j).1,hv _ (tailLoads_mem j).2,hx]
    have h := nat_row (n := VG.Impl.MlDsa.AArch64.Optimized.Inverse.z (7-(4*j.val+e)))
      (ht.tail (j := j.val) (e := e) j.isLt he)
    change vword (s.mem.read ((p+BitVec.ofNat 64 3840)+BitVec.ofNat 64 (16*j.val)) 16) e=_ ∧
      vword (s.mem.read ((p+BitVec.ofNat 64 3840)+BitVec.ofNat 64 (32+16*j.val)) 16) e=_
    rw [BitVec.add_assoc,← BitVec.ofNat_add,BitVec.add_assoc,← BitVec.ofNat_add]
    rw [show 3840+(32+16*j.val)=3872+16*j.val by omega_using []]
    exact h


def sourceGroup (i : Nat) : Nat := if i<4 then 0 else 1
def sourceLane (i : Nat) : Nat := if i<4 then i else i-4

theorem hoisted_source_geometry (i : Fin 7) (hi : i.val<6) :
    sourceGroup i.val<2 ∧ sourceLane i.val<4 ∧
    finalRootReg i.val=tailRootReg (sourceGroup i.val) ∧
    finalRecipReg i.val=tailRecipReg (sourceGroup i.val) ∧
    finalRootLane i.val=sourceLane i.val ∧ finalRecipLane i.val=sourceLane i.val := by
  exact (show ∀ i : Fin 7, i.val<6 →
    sourceGroup i.val<2 ∧ sourceLane i.val<4 ∧
    finalRootReg i.val=tailRootReg (sourceGroup i.val) ∧
    finalRecipReg i.val=tailRecipReg (sourceGroup i.val) ∧
    finalRootLane i.val=sourceLane i.val ∧ finalRecipLane i.val=sourceLane i.val by decide +kernel) i hi

theorem hoisted_source_value (i : Nat) (hi : i<6) :
    finalZ i 0=(VG.Impl.MlDsa.AArch64.Optimized.Inverse.z (7-(4*sourceGroup i+sourceLane i)) : Int) := by
  unfold finalZ finalValue sourceGroup sourceLane
  by_cases h : i<4
  · simp only [h,ite_true]
    rw [show 4*0+i=i by omega_using []]
  · simp only [h,hi,ite_false,ite_true]
    rw [show 7-(4*1+(i-4))=3-(i-4) by omega_using []]

theorem Hoisted.finalRoots {s : State} (h : Hoisted s)
    (hc : s.v .v30=scaleVector) (hq : ∀ e<4, vword (s.v .v31) e=8380417#32) : FinalRoots s := by
  have hs := scaleVector_folded hc
  have hpair (i : Fin 7) :
      vword (s.v (finalRootReg i.val)) (finalRootLane i.val)=BitVec.ofInt 32 (finalZ i.val 0) ∧
      vword (s.v (finalRecipReg i.val)) (finalRecipLane i.val)=BitVec.ofInt 32 (reciprocal (finalZ i.val 0)) := by
    by_cases hi : i.val<6
    · obtain ⟨hj,he,hr,hb,hl,hl'⟩ := hoisted_source_geometry i hi
      rw [hr,hb,hl,hl',hoisted_source_value i.val hi]
      exact h ⟨sourceGroup i.val,hj⟩ (sourceLane i.val) he
    · have he : i.val=6 := by omega_using [hi]
      simp only [he]
      exact hs
  exact ⟨fun i => (hpair i).1,fun i => (hpair i).2,hq⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

end


@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def middleCode : List Instr := finalSetup ++ tailLoadCode ++ scaleConst

theorem middle_ok {s : State} {p : Addr}
    (ht : InverseTable.Words s.mem p) (hx : s.gpr .x1=p+3840)
    (hr : ∀ off∈[0,16,32,48], InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hq : ∀ e<4, vword (s.v .v31) e=8380417#32) :
    WP isa (.block middleCode) s fun t =>
      Keep [.x0,.x2,.x9,.x12] s t ∧ t.mem=s.mem ∧
      t.gpr .x0=s.gpr .x0-1024 ∧ t.gpr .x2=s.gpr .x0-1024 ∧ t.gpr .x12=8 ∧
      FinalRoots t ∧ ScaleRoots t := by
  simp only [middleCode,List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (finalSetup_ok s) fun a ⟨⟨⟨ha0,ha2,ha12,ham⟩,hak⟩,hav⟩ => ?_
  refine tailLoad_ok (p := p) ?_ ?_ ?_ fun b hload ho => ?_
  · simpa only [ham] using ht
  · rw [hak.get .x1 (by decide)]
    exact hx
  · simpa only [hak.rd,hak.wr,hak.get .x1 (by decide)] using hr
  · refine WP.mono (scaleConst_ok b) fun t hc => ?_
    have hot : Hoisted t := by
      intro j e he
      have hr30 : tailRootReg j.val≠.v30 := (show ∀ j : Fin 2, tailRootReg j.val≠.v30 by decide +kernel) j
      have hb30 : tailRecipReg j.val≠.v30 := (show ∀ j : Fin 2, tailRecipReg j.val≠.v30 by decide +kernel) j
      rw [hc.1.vec _ hr30,hc.1.vec _ hb30]
      exact ho j e he
    have hqt : ∀ e<4, vword (t.v .v31) e=8380417#32 := by
      intro e he
      rw [hc.1.vec .v31 (by decide),hload.get .v31 (by decide),hav]
      exact hq e he
    refine ⟨((hak.trans hload.keep).trans (constKeep_keep hc.1 (by decide))).mono,
      hc.1.mem.trans (hload.mem.trans ham),?_,?_,?_,hot.finalRoots hc.2 hqt,scaleVector_ready hc.2⟩
    · rw [hc.1.gpr .x0 (by decide),hload.gpr,ha0]
    · rw [hc.1.gpr .x2 (by decide),hload.gpr,ha2]
    · rw [hc.1.gpr .x12 (by decide),hload.gpr,ha12]

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def coreRegs : List Reg := [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x9,.x11,.x12]

def inverseMem (m : Mem) (p : Addr) : Mem :=
  finalPassMem (firstPassMem m p 8) p (HighPack.repeatedWord 8380417) 8

theorem qVector_eq {v : BitVec 128} (h : ∀ e<4, vword v e=8380417#32) :
    v=HighPack.repeatedWord 8380417 := by
  apply VG.AArch64.vec_ext
  intro e he
  rw [h e he,HighPack.repeatedWord_lane _ he]

theorem core_eq : VG.Impl.MlDsa.AArch64.Optimized.Inverse.core=
    .seq (.block firstInit) (.seq
      (.loop (.block (fiveSliceCode++firstAdvance)) (.nonzero .x .x11))
      (.seq (.block middleCode) (.loop (.block (finalSliceCode++finalAdvance)) (.nonzero .x .x12)))) := by
  have h : VG.Impl.MlDsa.AArch64.Optimized.Inverse.core=
      .seq (.block firstInit) (.seq
        (.loop (.block VG.Impl.MlDsa.AArch64.Optimized.Inverse.firstBlock) (.nonzero .x .x11))
        (.seq (.block middleCode) (.loop (.block VG.Impl.MlDsa.AArch64.Optimized.Inverse.finalBody) (.nonzero .x .x12)))) := by rfl
  rw [h,firstBlock_eq,finalBody_eq]
  rfl

/-- The standalone inverse executes the selected two-pass memory transform.
Only table and buffer accessibility are required at this machine boundary. -/
theorem core_ok {s : State}
    (ht : InverseTable.Words s.mem (s.gpr .x1))
    (hd : (⟨s.gpr .x1,3904⟩ : Region).Disjoint ⟨s.gpr .x0,1024⟩)
    (hrt : ∀ off, off+16≤3904 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hr : ∀ off, off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hw : ∀ off, off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16) :
    WP isa VG.Impl.MlDsa.AArch64.Optimized.Inverse.core s fun t =>
      Keep coreRegs s t ∧ t.gpr .x0=s.gpr .x0 ∧ t.mem=inverseMem s.mem (s.gpr .x0) := by
  rw [core_eq]
  apply WP.seq
  refine WP.mono (firstInit_ok s) fun a ⟨hka,hma,h11,hqa⟩ => ?_
  have ha0 : a.gpr .x0=s.gpr .x0 := hka.get .x0 (by decide)
  have ha1 : a.gpr .x1=s.gpr .x1 := hka.get .x1 (by decide)
  apply WP.seq
  refine WP.mono (firstLoop_ok (s := a) ?_ ?_ h11 hqa ?_ ?_ ?_) fun b ⟨hkb,hqb,hb0,hb1,hmb⟩ => ?_
  · simpa only [hma,ha1] using ht
  · simpa only [ha0,ha1] using hd
  · simpa only [hka.rd,hka.wr,ha1] using hrt
  · intro u hu i
    simp only [hka.rd,hka.wr,ha0,BitVec.add_assoc,← BitVec.ofNat_add]
    exact hr _ (by omega_using [hu])
  · intro u hu i
    simp only [hka.wr,ha0,BitVec.add_assoc,← BitVec.ofNat_add]
    exact hw _ (by omega_using [hu])
  · have hb0' : b.gpr .x0=s.gpr .x0+1024 := by simpa only [ha0] using hb0
    have hb1' : b.gpr .x1=s.gpr .x1+3840 := by simpa only [ha1] using hb1
    have hmb' : b.mem=firstPassMem s.mem (s.gpr .x0) 8 := by simpa only [hma,ha0] using hmb
    have htb : InverseTable.Words b.mem (s.gpr .x1) := by
      rw [hmb']
      exact tableWords_frame ht (firstPass_frame (by decide)) (by
        intro r hr
        have he := List.mem_singleton.mp hr
        subst r
        exact hd)
    apply WP.seq
    refine WP.mono (middle_ok (s := b) htb hb1' ?_ hqb) fun c ⟨hkc,hmc,hc0,hc2,hc12,hfc,hsc⟩ => ?_
    · intro off hoff
      simp only [hkb.rd,hkb.wr,hka.rd,hka.wr,hb1']
      change InRegions (s.rd++s.wr) ((s.gpr .x1+BitVec.ofNat 64 3840)+BitVec.ofNat 64 off) 16
      rw [BitVec.add_assoc,← BitVec.ofNat_add]
      apply hrt
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hoff
      omega_using [hoff]
    · have hc0' : c.gpr .x0=s.gpr .x0 := by rw [hc0,hb0']; bv_omega_arith
      have hc2' : c.gpr .x2=s.gpr .x0 := by rw [hc2,hb0']; bv_omega_arith
      have hqv : c.v .v31=HighPack.repeatedWord 8380417 := qVector_eq hfc.q
      refine WP.mono (finalLoop_ok hfc hsc hc12 ?_ ?_) fun t ⟨hkt,_,_,hmt⟩ => ?_
      · intro u hu i
        simp only [hkc.rd,hkc.wr,hkb.rd,hkb.wr,hka.rd,hka.wr,hc2',BitVec.add_assoc,← BitVec.ofNat_add]
        exact hr _ (by omega_using [hu])
      · intro u hu i
        simp only [hkc.wr,hkb.wr,hka.wr,hc2',BitVec.add_assoc,← BitVec.ofNat_add]
        exact hw _ (by omega_using [hu])
      · refine ⟨(((hka.trans hkb).trans hkc).trans hkt).mono,?_,?_⟩
        · rw [hkt.get .x0 (by decide),hc0']
        · simpa only [inverseMem,hmc,hmb',hc2',hqv] using hmt

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
