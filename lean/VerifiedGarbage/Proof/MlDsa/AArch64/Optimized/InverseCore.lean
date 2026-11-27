module

import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSetup
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalSlice
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackInit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Loads
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFive
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.SliceFrame
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Slice

/-! ### `MlDsa.AArch64.Optimized.InverseFirstLoop`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.InverseFiveSlice`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg VMem)

def fiveSliceCode : List Instr := firstLoads ++ fiveCode ++ firstStores

def fiveSliceMem (u : Nat) (s : State) : Mem :=
  writeBank (fiveValues u (readBank s.mem (s.gpr .x0) 16)) (s.gpr .x0) 16 s.mem

theorem firstLoads_eq : firstLoads=(bankLoads (regs 0) 16).map (fun p => Instr.ldrq p.1 .x0 p.2) := by decide +kernel
theorem firstStores_eq : firstStores=(bankLoads (regs 7) 16).map (fun p => Instr.strq p.1 .x0 p.2) := rfl

theorem fiveSlice_ok (u : Nat) {s : State} {rest : List Instr} {Q : State → Prop}
    (hp : PackedRoots s (packedRoot u)) (hl : TableRoots localOffset (localRoot u) s)
    (hr : ∀ i : Fin 8, InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*i.val)) 16)
    (hw : ∀ i : Fin 8, InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 (16*i.val)) 16)
    (k : ∀ t, (∃ mid, VChg runRegs s mid ∧ VMem mid t (fiveSliceMem u s)) → WP isa (.block rest) t Q) :
    WP isa (.block (fiveSliceCode ++ rest)) s Q := by
  have ho : ∀ i : Fin 8, (16*i.val)%16=0 ∧ 16*i.val<65536 := by intro i; omega_using []
  have hsub : ((bankLoads (regs 0) 16).map Prod.fst)⊆packedRegs := by decide +kernel
  simp only [fiveSliceCode,firstLoads_eq,firstStores_eq,List.append_assoc]
  refine loadBank_ok (regs 0) 16 .x0 initial_inj ho hr fun s₁ hc₁ hb₁ => ?_
  have hc₁' := hc₁.mono hsub
  refine five_ok u hb₁ (hp.frame hc₁') (hl.frame hc₁' (by decide)) fun s₂ hc₂ hb₂ => ?_
  refine storeBank_ok (regs 7) 16 .x0 ho hb₂ ?_ fun t hm => ?_
  · intro i
    simpa only [hc₂.gpr,hc₂.wr,hc₁.gpr,hc₁.wr] using hw i
  · have hc : VChg runRegs s s₂ := VChg.mono (hc₁'.trans hc₂) (by
      intro r h
      rcases List.mem_append.mp h with h | h
      · exact (show packedRegs⊆runRegs by decide) h
      · exact h)
    have hm' : VMem s₂ t (fiveSliceMem u s) := by
      simpa only [fiveSliceMem,hc₂.mem,hc₁.mem,hc₂.gpr,hc₁.gpr] using hm
    exact k t ⟨s₂,hc,hm'⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def firstPassMem (m : Mem) (p : Addr) : Nat → Mem
  | 0 => m
  | u+1 => let prior := firstPassMem m p u
           let base := p+BitVec.ofNat 64 (128*u)
           writeBank (fiveValues u (readBank prior base 16)) base 16 prior

theorem firstAdvance_ok (s : State) :
    WP isa (.block firstAdvance) s fun t =>
      ((t.gpr .x0=s.gpr .x0+128 ∧ t.gpr .x1=s.gpr .x1+480 ∧
        t.gpr .x11=s.gpr .x11-1 ∧ t.mem=s.mem) ∧ Keep [.x0,.x1,.x11] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold firstAdvance
  arun
  exact ⟨rfl,rfl,rfl⟩

/-- Output stores preserve every static reciprocal-table word. -/
theorem tableWords_frame {m m' : Mem} {p : Addr} {rs : List Region}
    (h : InverseTable.Words m p) (hf : Frame rs m m')
    (hd : ∀ r∈rs, (⟨p,3904⟩ : Region).Disjoint r) : InverseTable.Words m' p := by
  intro k hk
  rw [hf.readW (r := ⟨p,3904⟩) (by
    exact VG.Offset.contains_base p (by omega_using [hk]) (by omega_using [hk])) hd (by decide)]
  exact h k hk

/-- All local stores stay within the output polynomial. -/
theorem firstPass_frame {m : Mem} {p : Addr} {u : Nat} (hu : u≤8) :
    Frame [⟨p,1024⟩] m (firstPassMem m p u) := by
  induction u with
  | zero => exact Frame.refl _ _
  | succ u ih =>
    simp only [firstPassMem]
    apply writeBank_frame _ _ _ (r := ⟨p,1024⟩) (by simp) ?_ (ih (by omega_using [hu]))
    intro i
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact VG.Offset.contains_base p (by omega_using [hu]) (by omega_using [hu])

/-- Eight contiguous five-layer blocks, retaining exact memory and the public
cursors needed by the final strided pass. -/
theorem firstLoop_ok {s : State}
    (ht : InverseTable.Words s.mem (s.gpr .x1))
    (hd : (⟨s.gpr .x1,3904⟩ : Region).Disjoint ⟨s.gpr .x0,1024⟩)
    (hc : s.gpr .x11=8)
    (hq : ∀ e<4, vword (s.v .v31) e=8380417#32)
    (hrt : ∀ off, off+16≤3904 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hr : ∀ u<8, ∀ i : Fin 8, InRegions (s.rd++s.wr)
      ((s.gpr .x0+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (16*i.val)) 16)
    (hw : ∀ u<8, ∀ i : Fin 8, InRegions s.wr
      ((s.gpr .x0+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (16*i.val)) 16) :
    WP isa (.loop (.block (fiveSliceCode++firstAdvance)) (.nonzero .x .x11)) s fun t =>
      Keep [.x0,.x1,.x11] s t ∧ (∀ e<4, vword (t.v .v31) e=8380417#32) ∧
      t.gpr .x0=s.gpr .x0+1024 ∧ t.gpr .x1=s.gpr .x1+3840 ∧
      t.mem=firstPassMem s.mem (s.gpr .x0) 8 := by
  let I := fun u t => Keep [.x0,.x1,.x11] s t ∧
    (∀ e<4, vword (t.v .v31) e=8380417#32) ∧
    t.gpr .x0=s.gpr .x0+BitVec.ofNat 64 (128*u) ∧
    t.gpr .x1=s.gpr .x1+BitVec.ofNat 64 (480*u) ∧
    t.mem=firstPassMem s.mem (s.gpr .x0) u
  apply VG.Proof.MlDsa.AArch64.Arith.wp_countdown (N := 8) (by decide) (by decide) I ?_ ?_ hc
  · intro u hu t hi _
    rcases hi with ⟨hk,hqt,hp0,hp1,hm⟩
    have ht' : InverseTable.Words t.mem (s.gpr .x1) := by
      rw [hm]
      exact tableWords_frame ht (firstPass_frame (by omega_using [hu])) (by
        intro r hr
        have he := List.mem_singleton.mp hr
        subst r
        exact hd)
    have hrt' : ∀ off, off+16≤3904 → InRegions (t.rd++t.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16 := by
      simpa only [hk.rd,hk.wr] using hrt
    refine fiveSlice_ok u (packed_tableRoots hu ht' hrt' hp1 hqt)
      (local_tableRoots hu ht' hrt' hp1 hqt) ?_ ?_ fun t₁ ⟨v,hv,hv₁⟩ => ?_
    · intro i
      simpa only [hk.rd,hk.wr,hp0] using hr u hu i
    · intro i
      simpa only [hk.wr,hp0] using hw u hu i
    · have hk₁ : Keep [] t t₁ := (hv.keep.trans hv₁.keep).mono
      refine WP.mono (firstAdvance_ok t₁) fun t₂ ⟨⟨⟨hp₂,hp₃,hc₂,hm₂⟩,hk₂⟩,hvec₂⟩ => ?_
      refine ⟨⟨((hk.trans hk₁).trans hk₂).mono,?_,?_,?_,?_⟩,?_⟩
      · intro e he
        rw [hvec₂,hv₁.v,hv.get .v31 (by decide)]
        exact hqt e he
      · rw [hp₂,hk₁.get .x0,hp0]
        rw [show 128*(u+1)=128*u+128 by omega_using [],BitVec.ofNat_add,BitVec.add_assoc]
        rfl
      · rw [hp₃,hk₁.get .x1,hp1]
        rw [show 480*(u+1)=480*u+480 by omega_using [],BitVec.ofNat_add,BitVec.add_assoc]
        rfl
      · rw [hm₂,hv₁.mem]
        simp only [fiveSliceMem,hm,hp0,firstPassMem]
      · rw [hc₂,hk₁.get .x11]
        rfl
  · exact ⟨Keep.refl _ _,hq,by simp,by simp,rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

/-! ### `MlDsa.AArch64.Optimized.InverseFinalLoop`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def finalPassMem (m : Mem) (p : Addr) (q : BitVec 128) : Nat → Mem
  | 0 => m
  | u+1 => let prior := finalPassMem m p q u
           let base := p+BitVec.ofNat 64 (16*u)
           writeBank (finalValues (readBank prior base 128) q) base 128 prior

theorem finalAdvance_ok (s : State) :
    WP isa (.block finalAdvance) s fun t =>
      ((t.gpr .x2=s.gpr .x2+16 ∧ t.gpr .x12=s.gpr .x12-1 ∧ t.mem=s.mem) ∧
        Keep [.x2,.x12] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold finalAdvance
  arun
  exact ⟨rfl,rfl⟩

theorem finalPass_frame {m : Mem} {p : Addr} {q : BitVec 128} {u : Nat} (hu : u≤8) :
    Frame [⟨p,1024⟩] m (finalPassMem m p q u) := by
  induction u with
  | zero => exact Frame.refl _ _
  | succ u ih =>
    simp only [finalPassMem]
    apply writeBank_frame _ _ _ (r := ⟨p,1024⟩) (by simp) ?_ (ih (by omega_using [hu]))
    intro i
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact Offset.contains_base p (by omega_using [hu]) (by omega_using [hu])

theorem finalLoop_ok {s : State} (hf : FinalRoots s) (hs : ScaleRoots s)
    (hc : s.gpr .x12=8)
    (hr : ∀ u<8, ∀ i : Fin 8, InRegions (s.rd++s.wr)
      ((s.gpr .x2+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (128*i.val)) 16)
    (hw : ∀ u<8, ∀ i : Fin 8, InRegions s.wr
      ((s.gpr .x2+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (128*i.val)) 16) :
    WP isa (.loop (.block (finalSliceCode++finalAdvance)) (.nonzero .x .x12)) s fun t =>
      Keep [.x2,.x12] s t ∧ (∀ r∈finalConstants, t.v r=s.v r) ∧
      t.gpr .x2=s.gpr .x2+128 ∧ t.mem=finalPassMem s.mem (s.gpr .x2) (s.v .v31) 8 := by
  let I := fun u t => Keep [.x2,.x12] s t ∧ (∀ r∈finalConstants, t.v r=s.v r) ∧
    t.gpr .x2=s.gpr .x2+BitVec.ofNat 64 (16*u) ∧
    t.mem=finalPassMem s.mem (s.gpr .x2) (s.v .v31) u
  apply VG.Proof.MlDsa.AArch64.Arith.wp_countdown (N := 8) (by decide) (by decide) I ?_ ?_ hc
  · intro u hu t ht _
    rcases ht with ⟨hk,hv,hp,hm⟩
    have hft : FinalRoots t := by
      constructor
      · intro i
        rw [hv _ ((show ∀ i : Fin 7, finalRootReg i.val∈finalConstants by decide +kernel) i)]
        exact hf.root i
      · intro i
        rw [hv _ ((show ∀ i : Fin 7, finalRecipReg i.val∈finalConstants by decide +kernel) i)]
        exact hf.recip i
      · intro e he; rw [hv .v31 (by decide)]; exact hf.q e he
    have hst : ScaleRoots t := by simpa only [ScaleRoots,hv .v30 (by decide)] using hs
    refine finalSlice_ok hft hst ?_ ?_ fun t₁ ⟨v,hvc,hvm⟩ => ?_
    · intro i; simpa only [hk.rd,hk.wr,hp] using hr u hu i
    · intro i; simpa only [hk.wr,hp] using hw u hu i
    · have hk₁ : Keep [] t t₁ := (hvc.keep.trans hvm.keep).mono
      refine WP.mono (finalAdvance_ok t₁) fun t₂ ⟨⟨⟨hp₂,hc₂,hm₂⟩,hk₂⟩,hv₂⟩ => ?_
      refine ⟨⟨((hk.trans hk₁).trans hk₂).mono,?_,?_,?_⟩,?_⟩
      · intro r hr
        rw [hv₂,hvm.v,hvc.get r ((show ∀ r∈finalConstants, r∉runRegs by decide) r hr)]
        exact hv r hr
      · rw [hp₂,hk₁.get .x2,hp]
        rw [show 16*(u+1)=16*u+16 by omega_using [],BitVec.ofNat_add,BitVec.add_assoc]
        rfl
      · rw [hm₂,hvm.mem]
        simp only [finalSliceMem,hm,hp,hv .v31 (by decide),finalPassMem]
      · rw [hc₂,hk₁.get .x12]; rfl
  · exact ⟨Keep.refl _ _,fun _ _ => rfl,by simp,rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

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
