import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.HighPack

namespace VG.Impl.MlDsa.AArch64.Optimized.UseHintPack
open VG.Impl.MlDsa.AArch64.Round
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.HighPack
def csub (d modulus : VReg) : List Instr :=
  [.vop (.sub .s4 .v7 d modulus),.vop (.umin d d .v7)]

def four (g : Nat) (r : VReg) (off : Nat) : List Instr :=
 ([.ldrq .v4 .x5 off,.ldrq .v5 .x4 off] : List Instr) ++ hf g .v6 .v4 ++
 ([.vop (.mul .v26 .v6 .v21),.vop (.sub .s4 .v26 .v26 .v4),
  .vop (.shift .ushr .s4 .v26 .v26 31),.vop (.shift .shl .s4 .v26 .v26 1),
  .vop (.sub .s4 .v26 .v26 .v22),.vop (.cmeq .s4 .v5 .v5 .v23),
  .vop (.logic .bic .v26 .v26 .v5),.vop (.add .s4 .v6 .v6 .v26),
  .vop (.add .s4 .v6 .v6 .v20)] : List Instr) ++ csub .v6 .v20 ++ csub .v6 .v20 ++ ([.vop (.mov r .v6)] : List Instr)
def code (g : Nat) : Prog isa :=
 let width := if g==261888 then 4 else 6
 .seq (.block (constants g ++ HighPack.packSetup ++ ([.movz .x .x11 16 0] : List Instr))) <|
 .loop (.block ((([.v0,.v1,.v2,.v3] : List VReg).zipIdx.flatMap fun (r,j) => four g r (16*j)) ++
  HighPack.packTail width ++ ([.addImm .x .x4 .x4 64,.addImm .x .x5 .x5 64,
  .addImm .x .x1 .x1 (2*width),.subImm .x .x11 .x11 1] : List Instr))) (.nonzero .x .x11)
-- ABI packedout, hints[256], canonicalw[256], gamma.
def prog : Prog isa := .seq (.block [.addImm .x .x4 .x1 0,.addImm .x .x5 .x2 0,.addImm .x .x1 .x0 0])
 (zext .x3 <| onGamma .x3 .x6 code)
end VG.Impl.MlDsa.AArch64.Optimized.UseHintPack
