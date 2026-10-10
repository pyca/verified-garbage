import VerifiedGarbage.Impl.MlDsa.AArch64.Call

namespace VG.Impl.MlDsa.AArch64.Optimized.MatrixMask
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Call

def group (i : Nat) : List Instr :=
  [.ldrq .v1 .x1 (16*i),.vop (.logic .and .v1 .v1 .v0),.strq .v1 .x1 (16*i)]

def advance : List Instr := [.addImm .x .x1 .x1 64,.subImm .x .x2 .x2 1]

def body : List Instr := (List.range 4).flatMap group ++ advance

/-- The measured four-vector cleanup; all addresses and loop counts are public. -/
def code (a : Ptr) (count : Nat) : Prog isa :=
  .seq (.block (([.movz .x .x8 0 0,.sub .w .x8 .x8 .x0,.vop (.dup .s4 .v0 .x8)] : List Instr) ++
    lea .x1 a.1 a.2 ++ ([.movz .x .x2 (BitVec.ofNat 16 (count/16)) 0] : List Instr)))
    (.loop (.block body) (.nonzero .x .x2))

end VG.Impl.MlDsa.AArch64.Optimized.MatrixMask
