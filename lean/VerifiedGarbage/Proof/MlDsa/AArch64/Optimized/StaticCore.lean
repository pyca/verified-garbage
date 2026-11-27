module

import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Core
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.FiveInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.SliceFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Layout
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableMemory
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableDecode
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableWords
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! ### `MlDsa.AArch64.Optimized.TableArtifact`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

/-- Exact immutable 64-bit artifact contents, before splitting into SIMD lanes. -/
def ExpandedArtifact (m : Mem) (p : Addr) : Prop :=
  ∀ i<488, m.readW (p+BitVec.ofNat 64 (8*i)) 64=staticNttWords[i]!

theorem ExpandedArtifact.words {m : Mem} {p : Addr} (h : ExpandedArtifact m p) :
    ExpandedWords m p := by
  intro k hk
  have hi : k/2<488 := by omega_using [hk]
  have hv := h (k/2) hi
  have hr : k%2=0 ∨ k%2=1 := by omega_using []
  rcases hr with hr | hr
  · have he : k=2*(k/2) := by omega_using [hr]
    have hx := congrArg (fun v : BitVec 64 => v.extractLsb' 0 32) hv
    rw [readW64_lo,TableConstants.staticNttWords_low hi] at hx
    simpa only [show 8*(k/2)=4*k by omega_using [hr],← he] using hx
  · have he : k=2*(k/2)+1 := by omega_using [hr]
    have hx := congrArg (fun v : BitVec 64 => v.extractLsb' 32 32) hv
    rw [readW64_hi,TableConstants.staticNttWords_high hi,BitVec.add_assoc,
      ← BitVec.ofNat_add (8*(k/2)) 4] at hx
    simpa only [show 8*(k/2)+4=4*k by omega_using [hr],← he] using hx

theorem ExpandedArtifact.roots {m : Mem} {p : Addr} (h : ExpandedArtifact m p) :
    HoistedTable m p ordinaryRoot ∧ RootTable m p innerRoot tailRoot :=
  ⟨h.words.hoisted,h.words.roots⟩

end VG.Proof.MlDsa.AArch64.Optimized

end

end

/-! ### `MlDsa.AArch64.Optimized.OutCore`, which this module and modules that import it used -/

section

/-! ## From `OuterOutLoop.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Impl.MlKem.AArch64 (mov)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def outerOutMemStep (m : Mem) (p src : Addr) (z : Nat → Int) : Mem :=
  writeBank (outerValues (readBank m src 128) z outerSteps) p 128 m

def outerOutPassMem (m : Mem) (p src : Addr) (z : Nat → Int) : Nat → Mem
  | 0 => m
  | u+1 => outerOutMemStep (outerOutPassMem m p src z u) (p+BitVec.ofNat 64 (16*u)) (src+BitVec.ofNat 64 (16*u)) z

def outerOutAdvance : List Instr := [.addImm .x .x2 .x2 16,.addImm .x .x11 .x11 16,.subImm .x .x5 .x5 1]

theorem outerOutAdvance_ok (s : State) :
    WP isa (.block outerOutAdvance) s fun t =>
      ((t.gpr .x2 = s.gpr .x2+16 ∧ t.gpr .x5 = s.gpr .x5-1 ∧ t.gpr .x11=s.gpr .x11+16 ∧ t.mem = s.mem) ∧
        Keep [.x2,.x5,.x11] s t) ∧ t.v = s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold outerOutAdvance
  arun
  exact ⟨rfl,rfl,rfl⟩

/-- All eight strided slices, with an exact memory result. The array need not
contain canonical words; only the reciprocal table and access bounds matter. -/
theorem outerOutLoop_ok {s : State} {z : Nat → Int} (hconst : Hoisted s z)
    (hc : s.gpr .x5 = 8)
    (hr : ∀ u < 8, ∀ i : Fin 8, InRegions (s.rd++s.wr)
      ((s.gpr .x11+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (128*i.val)) 16)
    (hw : ∀ u < 8, ∀ i : Fin 8, InRegions s.wr
      ((s.gpr .x2+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (128*i.val)) 16) :
    WP isa (.loop (.block (outerSliceCode .x11 ++ outerOutAdvance)) (.nonzero .x .x5)) s fun t =>
      Keep [.x2,.x5,.x11] s t ∧ Hoisted t z ∧ t.gpr .x2 = s.gpr .x2+128 ∧ t.gpr .x11=s.gpr .x11+128 ∧
        t.mem = outerOutPassMem s.mem (s.gpr .x2) (s.gpr .x11) z 8 := by
  let I := fun u t => Keep [.x2,.x5,.x11] s t ∧ Hoisted t z ∧
    t.gpr .x2 = s.gpr .x2+BitVec.ofNat 64 (16*u) ∧
    t.gpr .x11 = s.gpr .x11+BitVec.ofNat 64 (16*u) ∧
    t.mem = outerOutPassMem s.mem (s.gpr .x2) (s.gpr .x11) z u
  apply VG.Proof.MlDsa.AArch64.Arith.wp_countdown (N := 8) (by decide) (by decide) I ?_ ?_ hc
  · intro u hu t ht _
    rcases ht with ⟨hk,ht,hp,hsr,hm⟩
    refine outerSlice_ok .x11 ht ?_ ?_ fun t₁ ⟨v,hv,hv₁⟩ ht₁ => ?_
    · intro i
      simpa only [hk.rd,hk.wr,hsr] using hr u hu i
    · intro i
      simpa only [hk.wr,hp] using hw u hu i
    · have hk₁ : Keep [] t t₁ := (hv.keep.trans hv₁.keep).mono
      refine WP.mono (outerOutAdvance_ok t₁) fun t₂ ⟨⟨⟨hp₂,hc₂,hs₂,hm₂⟩,hk₂⟩,hvec₂⟩ => ?_
      refine ⟨⟨((hk.trans hk₁).trans hk₂).mono, ?_, ?_, ?_, ?_⟩, ?_⟩
      · exact ⟨ht₁.range,by simpa only [hvec₂] using ht₁.q,
          by simpa only [hvec₂] using ht₁.roots⟩
      · rw [hp₂,hk₁.get .x2,hp]
        rw [show 16*(u+1)=16*u+16 by omega_using [],BitVec.ofNat_add,BitVec.add_assoc]
        rfl
      · rw [hs₂,hk₁.get .x11,hsr]
        rw [show 16*(u+1)=16*u+16 by omega_using [],BitVec.ofNat_add,BitVec.add_assoc]
        rfl
      · rw [hm₂,hv₁.mem]
        simp only [outerSliceMem,hm,hp,hsr,outerOutPassMem,outerOutMemStep]
      · rw [hc₂,hk₁.get .x5]
        rfl
  · exact ⟨Keep.refl _ _,hconst,by simp,by simp,rfl⟩

/-- The abstract slice loop is exactly the selected emitter's loop body. -/
theorem outerOut_eq : outerOut =
    .seq (.block ([mov .x2 .x0,.movz .x .x5 8 0] ++ hoistedInit))
      (.loop (.block (outerSliceCode .x11 ++ outerOutAdvance)) (.nonzero .x .x5)) := by
  have hl : (bankLoads ({} : Ren).data 128).map (fun p => Instr.ldrq p.1 .x11 p.2) =
      dataRegs.zipIdx.flatMap (fun (v,i) => [Instr.ldrq v .x11 (128*i)]) := by rfl
  have hs : (bankLoads (renThree true).data 128).map (fun p => Instr.strq p.1 .x2 p.2) =
      (renThree true).data.toList.zipIdx.flatMap (fun (v,i) => [Instr.strq v .x2 (128*i)]) := by
    rw [renThree_data]
    rfl
  simp only [outerOut,outerSliceCode,outerOutAdvance,hl,hs,List.append_assoc]

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `OuterOutInit.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg Keep)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

theorem outerOut_ok {s : State} {z : Nat → Int} (h : HoistedMem s z)
    (hr : ∀ u < 8, ∀ i : Fin 8, InRegions (s.rd++s.wr)
      ((s.gpr .x11+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (128*i.val)) 16)
    (hw : ∀ u < 8, ∀ i : Fin 8, InRegions s.wr
      ((s.gpr .x0+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (128*i.val)) 16) :
    WP isa outerOut s fun t => Keep [.x2,.x5,.x11] s t ∧ Hoisted t z ∧
      t.gpr .x2=s.gpr .x0+128 ∧ t.gpr .x11=s.gpr .x11+128 ∧ t.mem=outerOutPassMem s.mem (s.gpr .x0) (s.gpr .x11) z 8 := by
  rw [outerOut_eq]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (outerSetup_ok s) fun s₁ ⟨⟨⟨hp₁,hc₁,hm₁⟩,hk₁⟩,hv₁⟩ => ?_
  have ht₁ : HoistedMem s₁ z := by
    refine ⟨h.range,?_,?_,?_⟩
    · simpa only [hv₁] using h.q
    · simpa only [hk₁.rd,hk₁.wr,hk₁.get .x1] using h.read
    · simpa only [hm₁,hk₁.get .x1] using h.roots
  refine hoistedInit_ok ht₁ (rest := []) fun s₂ hk₂ ht₂ => ?_
  apply WP.block_nil_iff.mpr
  refine WP.mono (outerOutLoop_ok ht₂ ?_ ?_ ?_) fun t ⟨hk₃,ht₃,hp₃,hs₃,hm₃⟩ => ?_
  · simpa only [hk₂.gpr] using hc₁
  · simpa only [hk₂.rd,hk₂.wr,hk₂.gpr,hk₁.rd,hk₁.wr,hk₁.get .x11] using hr
  · simpa only [hk₂.wr,hk₂.gpr,hk₁.wr,hp₁] using hw
  · refine ⟨((hk₁.trans hk₂.keep).trans hk₃).mono,ht₃,?_,?_,?_⟩
    · simpa only [hk₂.gpr,hp₁] using hp₃
    · simpa only [hk₂.gpr,hk₁.get .x11] using hs₃
    · simpa only [hk₂.mem,hm₁,hk₂.gpr,hp₁,hk₁.get .x11] using hm₃

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `OutCore.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

theorem outerOutPass_frame {m : Mem} {p src : Addr} {r : Region} {z : Nat → Int} {N : Nat}
    (hc : ∀ u<N, ∀ i : Fin 8, r.Contains
      ((p+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (128*i.val)) 16) :
    Frame [r] m (outerOutPassMem m p src z N) := by
  induction N with
  | zero => exact Frame.refl _ _
  | succ N ih =>
    have hf := ih (fun u hu i => hc u (by omega_using [hu]) i)
    simp only [outerOutPassMem,outerOutMemStep]
    exact writeBank_frame _ _ _ (by simp) (hc N (by omega_using [])) hf

def outGprs : List Reg := .x11::nttGprs

def outMemory (m : Mem) (p src : Addr) (z : Nat → Int) (zi zt : Nat → Nat → Nat → Nat → Int) : Mem :=
  fivePassMem (outerOutPassMem m p src z 8) p zi zt 8

/-- Whole selected in-place machine program. This exact word-level contract is
separate from its field interpretation and permits arbitrary initial lane bits. -/
theorem outBody_words_ok {s : State} {z : Nat → Int} {zi zt : Nat → Nat → Nat → Nat → Int}
    (ho : HoistedTable s.mem (s.gpr .x1) z) (ht : RootTable s.mem (s.gpr .x1) zi zt)
    (htr : expandedRegion (s.gpr .x1) ∈ s.rd++s.wr)
    (hr : outputRegion (s.gpr .x11) ∈ s.rd++s.wr)
    (hw : outputRegion (s.gpr .x0) ∈ s.wr)
    (hsep : (expandedRegion (s.gpr .x1)).Disjoint (outputRegion (s.gpr .x0))) :
    WP isa (.seq (.block fastConsts) (.seq outerOut renFive)) s fun t => Keep outGprs s t ∧ Frame [outputRegion (s.gpr .x0)] s.mem t.mem ∧
      t.mem=outMemory s.mem (s.gpr .x0) (s.gpr .x11) z zi zt := by
  refine WP.seq (WP.mono (fastConsts_ok s) fun s₁ ⟨hq₁,hm₁,hk₁⟩ => ?_)
  have ho₁ : HoistedMem s₁ z := HoistedTable.mem
    (by simpa only [hm₁,hk₁.get .x1] using ho)
    (by simpa only [hk₁.rd,hk₁.wr,hk₁.get .x1] using htr) hq₁
  refine WP.seq (WP.mono (outerOut_ok ho₁ ?_ ?_) fun s₂ ⟨hk₂,hc₂,_,_,hm₂⟩ => ?_)
  · intro u hu i
    exact ⟨_,by simpa only [hk₁.rd,hk₁.wr,hk₁.get .x11] using hr,outer_contains _ hu i⟩
  · intro u hu i
    exact ⟨_,by simpa only [hk₁.wr,hk₁.get .x0] using hw,outer_contains _ hu i⟩
  · have hf₂ : Frame [outputRegion (s.gpr .x0)] s.mem s₂.mem := by
      rw [hm₂,hm₁,hk₁.get .x0,hk₁.get .x11]
      exact outerOutPass_frame (fun u hu i => outer_contains _ hu i)
    have ht₂ : RootTable s₂.mem (s₂.gpr .x1) zi zt := by
      rw [hk₂.get .x1,hk₁.get .x1]
      exact ht.frame hf₂ (by intro r hr; have he := List.mem_singleton.mp hr; subst r; exact hsep)
    refine WP.mono (renFive_ok (r := outputRegion (s.gpr .x0)) ht₂ hc₂.q ?_ ?_ ?_ ?_) fun t ⟨hk₃,hf₃,_,_,hm₃⟩ => ?_
    · simpa only [hk₂.rd,hk₂.wr,hk₂.get .x1,hk₁.rd,hk₁.wr,hk₁.get .x1] using htr
    · simpa only [hk₂.wr,hk₁.wr] using hw
    · simpa only [hk₂.get .x1,hk₁.get .x1] using hsep
    · intro u hu i
      rw [hk₂.get .x0,hk₁.get .x0]
      exact inner_output_contains _ hu i
    · refine ⟨((hk₁.trans hk₂).trans hk₃).mono,hf₂.trans hf₃,?_⟩
      simpa only [outMemory,hm₂,hm₁,hk₂.get .x0,hk₁.get .x0,hk₁.get .x11] using hm₃

end VG.Proof.MlDsa.AArch64.Optimized

end

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

theorem staticInit_ok (s : State) :
    WP isa (.block [.adrSym .x1 "VG_MLDSA_NTT_EXPANDED"]) s fun t =>
      (t.gpr .x1=s.syms "VG_MLDSA_NTT_EXPANDED" ∧ t.mem=s.mem) ∧ Keep [.x1] s t := by
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  arun [exec_adrSym]

theorem outInit_ok (s : State) :
    WP isa (.block [.addImm .x .x11 .x1 0,.adrSym .x1 "VG_MLDSA_NTT_EXPANDED"]) s fun t =>
      (t.gpr .x1=s.syms "VG_MLDSA_NTT_EXPANDED" ∧ t.gpr .x11=s.gpr .x1 ∧ t.mem=s.mem) ∧
      Keep [.x1,.x11] s t := by
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  arun [exec_adrSym]
  rfl

theorem staticNtt_words_ok {s : State}
    (ht : ExpandedArtifact s.mem (s.syms "VG_MLDSA_NTT_EXPANDED"))
    (htr : expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED") ∈ s.rd++s.wr)
    (hw : outputRegion (s.gpr .x0) ∈ s.wr)
    (hsep : (expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED")).Disjoint (outputRegion (s.gpr .x0))) :
    WP isa staticNtt s fun t => Keep (.x1::nttGprs) s t ∧ Frame [outputRegion (s.gpr .x0)] s.mem t.mem ∧
      t.mem=nttMemory s.mem (s.gpr .x0) ordinaryRoot innerRoot tailRoot := by
  unfold staticNtt
  refine WP.seq (WP.mono (staticInit_ok s) fun s₁ ⟨⟨ha,hm⟩,hk⟩ => ?_)
  have hr : ExpandedArtifact s₁.mem (s₁.gpr .x1) := by simpa only [hm,ha] using ht
  refine WP.mono (renamedNtt_words_ok hr.roots.1 hr.roots.2 ?_ ?_ ?_) fun t ⟨hk₁,hf₁,hm₁⟩ => ?_
  · simpa only [ha,hk.rd,hk.wr] using htr
  · simpa only [hk.get .x0,hk.wr] using hw
  · simpa only [ha,hk.get .x0] using hsep
  · exact ⟨(hk.trans hk₁).mono,by simpa only [hm,hk.get .x0] using hf₁,
      by simpa only [hm,hk.get .x0] using hm₁⟩

theorem outNtt_words_ok {s : State}
    (ht : ExpandedArtifact s.mem (s.syms "VG_MLDSA_NTT_EXPANDED"))
    (htr : expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED") ∈ s.rd++s.wr)
    (hr : outputRegion (s.gpr .x1) ∈ s.rd++s.wr)
    (hw : outputRegion (s.gpr .x0) ∈ s.wr)
    (hsep : (expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED")).Disjoint (outputRegion (s.gpr .x0))) :
    WP isa outNtt s fun t => Keep (.x1::outGprs) s t ∧ Frame [outputRegion (s.gpr .x0)] s.mem t.mem ∧
      t.mem=outMemory s.mem (s.gpr .x0) (s.gpr .x1) ordinaryRoot innerRoot tailRoot := by
  unfold outNtt
  refine WP.seq (WP.mono (outInit_ok s) fun s₁ ⟨⟨ha,hs,hm⟩,hk⟩ => ?_)
  have hrt : ExpandedArtifact s₁.mem (s₁.gpr .x1) := by simpa only [hm,ha] using ht
  refine WP.mono (outBody_words_ok hrt.roots.1 hrt.roots.2 ?_ ?_ ?_ ?_) fun t ⟨hk₁,hf₁,hm₁⟩ => ?_
  · simpa only [ha,hk.rd,hk.wr] using htr
  · simpa only [hs,hk.rd,hk.wr] using hr
  · simpa only [hk.get .x0,hk.wr] using hw
  · simpa only [ha,hk.get .x0] using hsep
  · exact ⟨(hk.trans hk₁).mono,by simpa only [hm,hk.get .x0] using hf₁,
      by simpa only [hm,hk.get .x0,hs] using hm₁⟩

end VG.Proof.MlDsa.AArch64.Optimized
