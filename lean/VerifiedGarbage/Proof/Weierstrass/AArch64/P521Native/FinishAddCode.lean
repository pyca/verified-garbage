module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishAdd
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.BuildDoubleCode
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64.P521Native VG.Impl.Mont.AArch64

theorem finish_add_source152 : (outerBlock152.drop (outerBlock152.length-4))=
  normalizeCallArgs 1720 1072 1504 := by lit_decide

theorem finish_add_source153 : outerBlock153=
  buildRestore++(normalizeCallArgs 1792 1144 1576) := by lit_decide

theorem finish_add_source154 : outerBlock154=
  buildRestore++(normalizeCallArgs 1864 1216 1648) := by lit_decide

theorem finish_add_source155 : outerBlock155=
  buildRestore++(P521Linear.add 1936 1072 1144++(P521Linear.add 2008 1504 1576++(normalizeCallArgs 1936 1936 2008))) := by lit_decide

theorem finish_add_source156 : outerBlock156=
  buildRestore++(P521Linear.add 2008 1720 1792++(P521Linear.sub 1936 1936 2008++(P521Linear.add 2008 1144 1216++(P521Linear.add 1288 1576 1648++(normalizeCallArgs 2008 2008 1288))))) := by lit_decide

theorem finish_add_source157 : outerBlock157=
  buildRestore++(P521Linear.add 1288 1792 1864++(P521Linear.sub 2008 2008 1288++(P521Linear.add 1288 1072 1216++(P521Linear.add 1360 1504 1648++(normalizeCallArgs 1288 1288 1360))))) := by lit_decide

theorem finish_add_source158 : outerBlock158=
  buildRestore++(P521Linear.add 1360 1720 1864++(P521Linear.sub 1360 1288 1360++(normalizeCallArgs 1432 568 1864))) := by lit_decide

theorem finish_add_source159 : outerBlock159=
  buildRestore++(P521Linear.sub 1288 1360 1432++(P521Linear.add 1432 1288 1288++(P521Linear.add 1288 1288 1432++(P521Linear.sub 1432 1792 1288++(P521Linear.add 1288 1792 1288++(normalizeCallArgs 1360 568 1360)))))) := by lit_decide

theorem finish_add_source160 : outerBlock160=
  buildRestore++(P521Linear.add 1792 1864 1864++(P521Linear.add 1864 1792 1864++(P521Linear.sub 1360 1360 1864++(P521Linear.sub 1360 1360 1720++(P521Linear.add 1792 1360 1360++(P521Linear.add 1360 1792 1360++(P521Linear.add 1792 1720 1720++(P521Linear.add 1720 1792 1720++(P521Linear.sub 1720 1720 1864++(normalizeCallArgs 1792 2008 1360)))))))))) := by lit_decide

theorem finish_add_source161 : outerBlock161=
  buildRestore++(normalizeCallArgs 1864 1720 1360) := by lit_decide

theorem finish_add_source162 : outerBlock162=
  buildRestore++(normalizeCallArgs 1360 1288 1432) := by lit_decide

theorem finish_add_source163 : outerBlock163=
  buildRestore++(P521Linear.add 1360 1360 1864++(normalizeCallArgs 1288 1936 1288)) := by lit_decide

theorem finish_add_source164 : outerBlock164=
  buildRestore++(P521Linear.sub 1288 1288 1792++(normalizeCallArgs 1432 2008 1432)) := by lit_decide

theorem finish_add_source165 : outerBlock165=
  buildRestore++(normalizeCallArgs 1792 1936 1720) := by lit_decide

theorem finish_add_source166 : (outerBlock166.take 53)=
  buildRestore++(P521Linear.add 1432 1432 1792) := by lit_decide

def finishAddMachine : Prog isa := sequence [
  .block (outerBlock152.drop (outerBlock152.length-4)),
  callNormalMul,
  .block outerBlock153,
  callNormalMul,
  .block outerBlock154,
  callNormalMul,
  .block outerBlock155,
  callNormalMul,
  .block outerBlock156,
  callNormalMul,
  .block outerBlock157,
  callNormalMul,
  .block outerBlock158,
  callNormalMul,
  .block outerBlock159,
  callNormalMul,
  .block outerBlock160,
  callNormalMul,
  .block outerBlock161,
  callNormalMul,
  .block outerBlock162,
  callNormalMul,
  .block outerBlock163,
  callNormalMul,
  .block outerBlock164,
  callNormalMul,
  .block outerBlock165,
  callNormalMul,
  .block (outerBlock166.take 53)]

private theorem finish_wp_post_iff {code : Prog isa} {s : State} {Q R : State → Prop}
    (h : ∀t,Q t ↔ R t) : WP isa code s Q ↔ WP isa code s R :=
  ⟨fun q => WP.mono q (fun t ht => (h t).mp ht),fun q => WP.mono q (fun t ht => (h t).mpr ht)⟩

theorem finish_add_machine_wp {s : State} {Q : State → Prop} :
    WP isa finishAddMachine s Q ↔ WP isa (fieldProgram id finishAddOps) s Q := by
  simp only [finishAddMachine,sequence,List.foldr_cons,List.foldr_nil,
    finishAddOps,finishPointOp,rcb3,finishAddSlotMap,finishAddP,finishAddQ,finishAddOut,List.map_cons,List.map_nil,
    fieldProgram,fieldCode,id,Nat.reduceEqDiff,ite_false,normalizeMulStep,
    finish_add_source152,finish_add_source153,finish_add_source154,finish_add_source155,finish_add_source156,finish_add_source157,finish_add_source158,finish_add_source159,finish_add_source160,finish_add_source161,finish_add_source162,finish_add_source163,finish_add_source164,finish_add_source165,finish_add_source166]
  repeat' first | rfl | rw [VG.WP.seq_iff] | rw [VG.WP.block_append_iff] | rw [VG.WP.block_nil_iff] | (apply finish_wp_post_iff; intro t)

/-- Full canonical-field contract for the exact final complete-addition block
sequence, with the generic field interpreter's public and memory frame. -/
theorem finish_add_machine_ok {base : Addr} {s : State}
    {E : Nat → Fin VG.Proof.Mont.AArch64.P521Square.fieldPrime}
    (hs : VG.Proof.Mont.AArch64.Scr s base 8192)
    (inv : VG.Proof.Mont.AArch64.P521Field.OrdinaryInv base
      VG.Proof.Mont.AArch64.P521Square.fieldPrime id [1072,1144,1216,1504,1576,1648,568] E (fun _ => 1) s) :
    WP isa finishAddMachine s fun t =>
      VG.Proof.Mont.AArch64.P521Field.OrdinaryInv base VG.Proof.Mont.AArch64.P521Square.fieldPrime id
        (fieldLive finishAddOps [1072,1144,1216,1504,1576,1648,568])
        (VG.Proof.Mont.AArch64.P521Field.pointRun finishAddOps E) (fun _ => 1) t ∧
      VG.Proof.Mont.AArch64.Scr t base 8192 ∧ FieldPublic s t ∧ FieldProgramFrame base id finishAddOps s.mem t.mem := by
  apply finish_add_machine_wp.mpr
  exact field_program_ok (by decide) (by decide) build_field_layout finishAddOps hs inv
    (by simp [buildSlot]) finishAdd_slots finishAdd_reads finishAdd_coeffs

end VG.Proof.Weierstrass.AArch64.P521Native
