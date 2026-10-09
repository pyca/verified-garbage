import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.OuterSlice
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Impl.MlKem.AArch64 (mov)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def outerMemStep (m : Mem) (p : Addr) (z : Nat → Int) : Mem :=
  writeBank (outerValues (readBank m p 128) z outerSteps) p 128 m

def outerPassMem (m : Mem) (p : Addr) (z : Nat → Int) : Nat → Mem
  | 0 => m
  | u+1 => outerMemStep (outerPassMem m p z u) (p+BitVec.ofNat 64 (16*u)) z

def outerAdvance : List Instr := [.addImm .x .x2 .x2 16,.subImm .x .x5 .x5 1]

theorem outerAdvance_ok (s : State) :
    WP isa (.block outerAdvance) s fun t =>
      ((t.gpr .x2 = s.gpr .x2+16 ∧ t.gpr .x5 = s.gpr .x5-1 ∧ t.mem = s.mem) ∧
        Keep [.x2,.x5] s t) ∧ t.v = s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold outerAdvance
  arun
  exact ⟨rfl,rfl⟩

/-- All eight strided slices, with an exact memory result. The array need not
contain canonical words; only the reciprocal table and access bounds matter. -/
theorem outerLoop_ok {s : State} {z : Nat → Int} (hconst : Hoisted s z)
    (hc : s.gpr .x5 = 8)
    (hr : ∀ u < 8, ∀ i : Fin 8, InRegions (s.rd++s.wr)
      ((s.gpr .x2+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (128*i.val)) 16)
    (hw : ∀ u < 8, ∀ i : Fin 8, InRegions s.wr
      ((s.gpr .x2+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (128*i.val)) 16) :
    WP isa (.loop (.block (outerSliceCode .x2 ++ outerAdvance)) (.nonzero .x .x5)) s fun t =>
      Keep [.x2,.x5] s t ∧ Hoisted t z ∧ t.gpr .x2 = s.gpr .x2+128 ∧
        t.mem = outerPassMem s.mem (s.gpr .x2) z 8 := by
  let I := fun u t => Keep [.x2,.x5] s t ∧ Hoisted t z ∧
    t.gpr .x2 = s.gpr .x2+BitVec.ofNat 64 (16*u) ∧
    t.mem = outerPassMem s.mem (s.gpr .x2) z u
  apply VG.Proof.MlDsa.AArch64.Arith.wp_countdown (N := 8) (by decide) (by decide) I ?_ ?_ hc
  · intro u hu t ht _
    rcases ht with ⟨hk,ht,hp,hm⟩
    refine outerSlice_ok .x2 ht ?_ ?_ fun t₁ ⟨v,hv,hv₁⟩ ht₁ => ?_
    · intro i
      simpa only [hk.rd,hk.wr,hp] using hr u hu i
    · intro i
      simpa only [hk.wr,hp] using hw u hu i
    · have hk₁ : Keep [] t t₁ := (hv.keep.trans hv₁.keep).mono
      refine WP.mono (outerAdvance_ok t₁) fun t₂ ⟨⟨⟨hp₂,hc₂,hm₂⟩,hk₂⟩,hvec₂⟩ => ?_
      refine ⟨⟨((hk.trans hk₁).trans hk₂).mono, ?_, ?_, ?_⟩, ?_⟩
      · exact ⟨ht₁.range,by simpa only [hvec₂] using ht₁.q,
          by simpa only [hvec₂] using ht₁.roots⟩
      · rw [hp₂,hk₁.get .x2,hp]
        rw [show 16*(u+1)=16*u+16 by omega,BitVec.ofNat_add,BitVec.add_assoc]
        rfl
      · rw [hm₂,hv₁.mem]
        simp only [outerSliceMem,hm,hp,outerPassMem,outerMemStep]
      · rw [hc₂,hk₁.get .x5]
        rfl
  · exact ⟨Keep.refl _ _,hconst,by simp, rfl⟩

/-- The abstract slice loop is exactly the selected emitter's loop body. -/
theorem outerRenamed_eq : outerRenamed =
    .seq (.block ([mov .x2 .x0,.movz .x .x5 8 0] ++ hoistedInit))
      (.loop (.block (outerSliceCode .x2 ++ outerAdvance)) (.nonzero .x .x5)) := by
  have hl : (bankLoads ({} : Ren).data 128).map (fun p => Instr.ldrq p.1 .x2 p.2) =
      dataRegs.zipIdx.flatMap (fun (v,i) => [Instr.ldrq v .x2 (128*i)]) := by rfl
  have hs : (bankLoads (renThree true).data 128).map (fun p => Instr.strq p.1 .x2 p.2) =
      (renThree true).data.toList.zipIdx.flatMap (fun (v,i) => [Instr.strq v .x2 (128*i)]) := by
    rw [renThree_data]
    rfl
  simp only [outerRenamed,outerSliceCode,outerAdvance,hl,hs,List.append_assoc]

end VG.Proof.MlDsa.AArch64.Optimized
