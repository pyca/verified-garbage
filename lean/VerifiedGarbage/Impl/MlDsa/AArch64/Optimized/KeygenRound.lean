import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Common

namespace VG.Impl.MlDsa.AArch64.Optimized.KeygenRound
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith (movW)

def vc (d : VReg) (n : Nat) : List Instr :=
  movW .x9 (BitVec.ofNat 32 n) ++ [.vop (.dup .s4 d .x9)]
def cadd (d : VReg) : List Instr :=
  [.vop (.shift .sshr .s4 .v7 d 31), .vop (.logic .and .v7 .v7 .v16),
   .vop (.add .s4 d d .v7)]
def loop (ptrs : List Reg) (body : Nat → List Instr) : Prog isa :=
  .seq (.block [.movz .x .x10 16 0])
   (.loop (.block (([0,16,32,48].flatMap body) ++
     ptrs.map (fun r => .addImm .x r r 64) ++ [.subImm .x .x10 .x10 1])) (.nonzero .x .x10))
def arithmetic : List Instr :=
  ([.vop (.add .s4 .v1 .v0 .v17),.vop (.shift .ushr .s4 .v1 .v1 13),
   .vop (.shift .shl .s4 .v2 .v1 13),.vop (.sub .s4 .v0 .v0 .v2)] : List Instr) ++ cadd .v0

def body (off : Nat) : List Instr :=
  ([.ldrq .v0 .x0 off] : List Instr) ++ arithmetic ++ [.strq .v1 .x1 off,.strq .v0 .x2 off]

def power2Round : Prog isa :=
  .seq (.block (vc .v16 8380417 ++ vc .v17 4095)) (loop [.x0,.x1,.x2] body)

end VG.Impl.MlDsa.AArch64.Optimized.KeygenRound
