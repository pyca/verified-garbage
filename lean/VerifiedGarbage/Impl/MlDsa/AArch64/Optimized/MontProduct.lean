import VerifiedGarbage.TCB.AArch64.Isa

namespace VG.Impl.MlDsa.AArch64.Optimized.MontProduct
open VG VG.AArch64

def setup : List Instr :=
  [.movz .w .x9 57345 0,.movk .w .x9 127 1,
    .movz .w .x10 57343 0,.movk .w .x10 64639 1,
    .vop (.dup .s4 .v16 .x9),.vop (.dup .s4 .v17 .x10),.movz .x .x12 64 0]

def arithmetic : List Instr :=
  [.vop (.umull false .v2 .v0 .v1),.vop (.umull true .v3 .v0 .v1),
    .vop (.perm .uzp1 .s4 .v4 .v2 .v3),.vop (.mul .v4 .v4 .v17),
    .vop (.umlal false .v2 .v4 .v16),.vop (.umlal true .v3 .v4 .v16),
    .vop (.perm .uzp2 .s4 .v0 .v2 .v3),.vop (.sub .s4 .v4 .v0 .v16),
    .vop (.umin .v0 .v0 .v4)]

def body : List Instr :=
  ([.ldrq .v0 .x1 0,.ldrq .v1 .x2 0] : List Instr) ++ arithmetic ++
    ([.strq .v0 .x0 0,.addImm .x .x0 .x0 16,.addImm .x .x1 .x1 16,
      .addImm .x .x2 .x2 16,.subImm .x .x12 .x12 1] : List Instr)

def code : Prog isa := .seq (.block setup) (.loop (.block body) (.nonzero .x .x12))

end VG.Impl.MlDsa.AArch64.Optimized.MontProduct
