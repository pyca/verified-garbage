import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourBody
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rel

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (vectorVal vectorBody)

/-- The only data-dependent address in the vector parser is indexed by its
four public rejection bits. Split before that lookup, so accepted values stay secret. -/
def vectorPrefix : List Instr :=
 ([.ldr .w .x6 .x2 0,.vop (.dup .s4 .v0 .x6)] : List Instr)++
 (extractCode++acceptCode++maskCode)

def vectorSuffix (η : Nat) : List Instr :=
 ([.lsl .x .x6 .x6 6,.add .x .x13 .x12 .x6,
   .ldrq .v6 .x13 0,.ldr .x .x6 .x13 32] : List Instr)++
 (vectorVal η++([.vop (.tbl .v1 .v1 .v6),.strq .v1 .x3 0] : List Instr)++
 advanceCore++[.subs .x .x8 .x4 .x16,.cselc .x .x8 .x5 .x0 .hs])

theorem vector_split (η : Nat) : vectorBody true η=vectorPrefix++vectorSuffix η := by
  rw [vectorBody_eq]
  simp only [vectorPrefix,vectorSuffix,selectCode,List.append_assoc,List.cons_append,List.nil_append]

theorem vectorPrefix_taint : ∃h,
    (taint.check (Taint.ofRegs [.x2]) (.block vectorPrefix) h).isSome=true :=
  ⟨_,by taint_decide⟩

theorem vectorSuffix_taint {η : Nat} (hη : η=2∨η=4) : ∃h,
    (taint.check (Taint.ofRegs [.x3,.x6,.x12]) (.block (vectorSuffix η)) h).isSome=true := by
  rcases hη with rfl|rfl
  · exact ⟨_,by taint_decide⟩
  · exact ⟨_,by taint_decide⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
