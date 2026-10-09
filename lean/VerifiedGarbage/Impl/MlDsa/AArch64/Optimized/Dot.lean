import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Inverse

namespace VG.Impl.MlDsa.AArch64.Optimized
open VG VG.AArch64

/-- One term of the selected fused dot/inverse accumulator. Both polynomial
families are contiguous, with 1024 bytes per polynomial. -/
def dotTerm (off k : Nat) : List Instr :=
  [.ldrq .v16 .x13 (1024*k+off),.ldrq .v17 .x14 (1024*k+off)] ++
  (if k=0 then [.vop (.umull false .v18 .v16 .v17),.vop (.umull true .v19 .v16 .v17)]
   else [.vop (.umlal false .v18 .v16 .v17),.vop (.umlal true .v19 .v16 .v17)])

/-- One unsigned reduction after all terms, then the measured signed centering. -/
def dotReduce (d : VReg) : List Instr :=
  [.vop (.perm .uzp1 .s4 .v20 .v18 .v19),.vop (.mul .v20 .v20 .v30),
   .vop (.umlal false .v18 .v20 .v31),.vop (.umlal true .v19 .v20 .v31),
   .vop (.perm .uzp2 .s4 d .v18 .v19),.vop (.sub .s4 d d .v31)]

def dotLoad (n : Nat) (d : VReg) (off : Nat) : List Instr :=
  (List.range n).flatMap (dotTerm off) ++ dotReduce d

/-- The exact eight-bank loader consumed by the selected first inverse pass. -/
def inverseDotLoads (n : Nat) : List Instr :=
  (List.range 8).flatMap fun j => dotLoad n (Inverse.vr j) (16*j)

end VG.Impl.MlDsa.AArch64.Optimized
