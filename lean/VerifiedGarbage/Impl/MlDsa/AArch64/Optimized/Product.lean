import VerifiedGarbage.TCB.AArch64.Isa

namespace VG.Impl.MlDsa.AArch64.Optimized
open VG.AArch64

/-- Exact widening product schedule selected by the fused multiply/inverse prototype. -/
def productMont (d : VReg) : List Instr :=
  [.vop (.umull false .v18 .v16 .v17), .vop (.umull true .v19 .v16 .v17),
   .vop (.perm .uzp1 .s4 .v20 .v18 .v19), .vop (.mul .v20 .v20 .v30),
   .vop (.umlal false .v18 .v20 .v31), .vop (.umlal true .v19 .v20 .v31),
   .vop (.perm .uzp2 .s4 d .v18 .v19)]

def productCentered (d : VReg) : List Instr :=
  productMont d ++ ([.vop (.sub .s4 d d .v31)] : List Instr)

/-- Load one four-coefficient group directly into the fused inverse bank. -/
def productLoad (d : VReg) (off : Nat) : List Instr :=
  ([.ldrq .v16 .x13 off, .ldrq .v17 .x14 off] : List Instr) ++ productCentered d

end VG.Impl.MlDsa.AArch64.Optimized
