module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTLocal
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! The complete native candidate entry has a fixed stack-address trace. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm

private def entryStores : List (Reg × Nat) := [(.r0, 4), (.r0, 8), (.r1, 12), (.r2, 32), (.r3, 24)]
private def entryCopies : List (Nat × Nat) := [(128, 28), (132, 16), (136, 20), (140, 0), (144, 36)]

theorem candidateEntry_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block VG.Impl.Ffdh.Arm.ParameterCandidate.entry) (fun s t => s.sp = t.sp) := by
  have zero : RelCT isa LocalAddress (.block [.mov .r0 (.imm 0), .str .r0 .r12 40]) LocalAddress :=
    RelCT.block_append (localZero_ct.seq (storeLocal_ct .r0 40))
  have tail : RelCT isa LocalAddress (.block
      ((entryStores.map fun p => Instr.str p.1 .r12 p.2) ++
        (entryCopies.flatMap fun p => [Instr.ldrSp .r0 p.1, Instr.str .r0 .r12 p.2]) ++
        [.mov .r0 (.imm 0), .str .r0 .r12 40])) LocalAddress :=
    RelCT.block_append ((RelCT.block_append ((localStores_ct entryStores).seq (localCopies_ct entryCopies))).seq zero)
  change RelCT isa _ (.block ([.addSp .r12 0] ++ _)) _
  exact RelCT.block_append (stackAddr_ct.seq (tail.mono (fun _ _ h => h) (fun _ _ h => h.2)))

end VG.Proof.Ffdh.Arm.ParameterCandidate
