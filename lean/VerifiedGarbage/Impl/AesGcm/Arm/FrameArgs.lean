module

public import VerifiedGarbage.Impl.AesGcm.Arm

/-! The contiguous and gather entries use the same one-shot workspace layout. -/
@[expose] public section
namespace VG.Impl.AesGcm.Arm

open VG.Arm

/-- Save the link register, place each caller argument in its one-shot slot,
then append the workspace pointer and restore the link register. -/
def orderedFrameArgs (bytes count : Nat) (index : Nat → Nat) : List Instr :=
  let move := fun slot => [Instr.ldrSp .lr (bytes + 4 * index slot), .str .lr .r12 (4 * slot)]
  [.addSp .r12 0, .str .lr .r12 (4 * count + 4)] ++ (List.range count).flatMap move ++
    [.addSp .lr (4 * count + 8), .str .lr .r12 (4 * count), .ldrSp .lr (4 * count + 4)]

end VG.Impl.AesGcm.Arm
