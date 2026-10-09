import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.OuterSlice
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic

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
        rw [show 16*(u+1)=16*u+16 by omega,BitVec.ofNat_add,BitVec.add_assoc]
        rfl
      · rw [hs₂,hk₁.get .x11,hsr]
        rw [show 16*(u+1)=16*u+16 by omega,BitVec.ofNat_add,BitVec.add_assoc]
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
