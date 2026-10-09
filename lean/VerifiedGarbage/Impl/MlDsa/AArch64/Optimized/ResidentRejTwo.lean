import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejParser
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejSqueeze

namespace VG.Impl.MlDsa.AArch64.Optimized.ResidentRej.Two
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlKem.AArch64 (mov)

def step : Prog isa := .seq (pair .x22 .x24 .x25) (.block Rej4.advance)
def initCounts : List Instr := [.movz .x .x4 256 0] ++
  (List.range 2).map (fun k => .str .x .x4 .x19 (counts+8*k))

-- Reconstitute squeeze pointers after parsing borrowed x25/x26/x27.
def squeezeSetup (off n : Nat) : List Instr :=
  [mov .x22 .x19,.addImm .x .x23 .x19 400,
   .addImm .x .x24 .x19 840,.addImm .x .x25 .x19 1848,
   .addImm .x .x26 .x19 2856,.addImm .x .x27 .x19 3864] ++
  (if off==0 then [] else [.addImm .x .x24 .x24 off,.addImm .x .x25 .x25 off,
    .addImm .x .x26 .x26 off,.addImm .x .x27 .x27 off]) ++
  [.movz .x .x28 n 0]

def squeezeN (squeeze : Prog isa) (off n : Nat) : Prog isa :=
  .seq (.block (squeezeSetup off n)) (.loop squeeze (.nonzero .x .x28))

def batch (v off n : Nat) : Prog isa :=
 .seq (segment v 0 off n) (segment v 1 off n)

def zeroTail (k : Nat) : Prog isa :=
 .seq (.block [.ldr .x .x4 .x19 (counts+8*k)]) <|
 .ite (.zero .x .x4) (.block []) <|
 .seq (.block ([.addImm .x .x3 .x21 (1024*k),.movz .x .x6 256 0,.sub .x .x6 .x6 .x4,
  .lsl .x .x6 .x6 2,.add .x .x3 .x3 .x6,
  .addImm .x .x6 .x19 (840+1008*k),.addImm .x .x6 .x6 1005,.ldr .w .x6 .x6 0,
  .movz .x .x7 65535 0,.movk .x .x7 127 1,.logic .and .x .x6 .x6 .x7] ++ movQ .x7 ++
  [.sub .x .x6 .x6 .x7,.lsr .x .x6 .x6 63,.movz .x .x7 1 0,.sub .x .x6 .x7 .x6,
   .sub .x .x4 .x4 .x6,.lsl .x .x6 .x6 2,.add .x .x3 .x3 .x6,.movz .x .x9 0 0])) <|
 .ite (.zero .x .x4) (.block [])
 (.loop (.block [.str .w .x9 .x3 0,.addImm .x .x3 .x3 4,.subImm .x .x4 .x4 1]) (.nonzero .x .x4))
def tailZeros : Prog isa := .ite (.zero .x .x27) (.block [])
 ((List.range 2).foldr (fun k rest => .seq (zeroTail k) rest) (.block []))

def flags : List Instr := [.ldr .x .x27 .x19 counts] ++
 (List.range 1).flatMap (fun k => [.ldr .x .x6 .x19 (counts+8*(k+1)),
 .logic .orr .x .x27 .x27 .x6])

def code : Prog isa :=
 .seq (.block (Rej4.pro ++ Rej4.zeroStates ++ Rej4.absorbPair 0 ++ initCounts)) <|
 .seq (.block (squeezeSetup 0 5)) <|
 .seq (five .x22 .x24 .x25) <|
 .seq (batch 0 0 168) <| .seq (batch 0 504 112) <|
 .seq (.block flags) <|
 .seq (.ite (.zero .x .x27) (.block [])
 (.seq (squeezeN step 840 1) <| .seq (batch 0 840 56) (.block flags))) <|
 .seq tailZeros <| .block ([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63]++Rej4.epi)

end VG.Impl.MlDsa.AArch64.Optimized.ResidentRej.Two
