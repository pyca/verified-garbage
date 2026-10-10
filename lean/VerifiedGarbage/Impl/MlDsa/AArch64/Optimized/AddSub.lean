import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Vec

namespace VG.Impl.MlDsa.AArch64.Optimized.AddSub
open VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon (consts csub)

/-- Canonical addition or subtraction of four coefficients. -/
def arithmetic (sub : Bool) : List Instr :=
  (if sub then [.vop (.add .s4 .v0 .v0 .v16), .vop (.sub .s4 .v0 .v0 .v1)]
   else [.vop (.add .s4 .v0 .v0 .v1)]) ++ csub .v0 .v4

def body (sub : Bool) : List Instr :=
  ([.ldrq .v0 .x0 0, .ldrq .v1 .x1 0] : List Instr) ++ arithmetic sub ++
  ([.strq .v0 .x0 0, .addImm .x .x0 .x0 16, .addImm .x .x1 .x1 16,
   .subImm .x .x12 .x12 1] : List Instr)

def code (sub : Bool) : Prog isa :=
  .seq (.block (consts ++ ([.movz .x .x12 64 0] : List Instr)))
    (.loop (.block (body sub)) (.nonzero .x .x12))
end VG.Impl.MlDsa.AArch64.Optimized.AddSub
