module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Vec

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon

def product (j : Nat) : List Instr :=
 ([.ldrq .v0 .x1 (1024*j),.ldrq .v1 .x2 (1024*j)] : List Instr) ++
 (if j=0 then [.vop (.umull false .v2 .v0 .v1),.vop (.umull true .v3 .v0 .v1)]
 else [.vop (.umlal false .v2 .v0 .v1),.vop (.umlal true .v3 .v0 .v1)])
def reduce : List Instr :=
 [.vop (.perm .uzp1 .s4 .v4 .v2 .v3),.vop (.mul .v4 .v4 .v17),
 .vop (.umlal false .v2 .v4 .v16),.vop (.umlal true .v3 .v4 .v16),
 .vop (.perm .uzp2 .s4 .v0 .v2 .v3)]

def body (n : Nat) : List Instr :=
 (List.range n).flatMap product ++ reduce ++ csub .v0 .v4 ++
 ([.strq .v0 .x0 0,.addImm .x .x0 .x0 16,.addImm .x .x1 .x1 16,
 .addImm .x .x2 .x2 16,.subImm .x .x12 .x12 1] : List Instr)

def dot (n : Nat) : Prog isa :=
 .seq (.block (consts ++ ([.movz .x .x12 64 0] : List Instr)))
   (.loop (.block (body n)) (.nonzero .x .x12))

end VG.Impl.MlDsa.AArch64.Optimized.MontDot
