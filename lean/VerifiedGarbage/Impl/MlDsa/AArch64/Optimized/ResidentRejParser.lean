import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt4

/-! Fixed-address vector parsing for the matrix sampler. Failed vector
acceptance falls back to the existing ordered scalar acceptance operation. -/
namespace VG.Impl.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlKem.AArch64 (mov)

def counts : Nat := 7904

def scalarChunk : List Instr :=
 [.ldr .w .x11 .x2 0,.logic .and .x .x11 .x11 .x10,
 .addImm .x .x2 .x2 3,.subImm .x .x5 .x5 1]

def scalarLoop : Prog isa :=
 .loop (.block (scalarChunk ++ rnAccept ++ ([.mul .x .x16 .x4 .x5] : List Instr))) (.nonzero .x .x16)

def setup (k off n : Nat) : List Instr :=
  ([.addImm .x .x2 .x19 (840+1008*k),.addImm .x .x2 .x2 off,
   .addImm .x .x3 .x21 (1024*k),.ldr .x .x4 .x19 (counts+8*k),
   .movz .x .x6 256 0,.sub .x .x6 .x6 .x4,.lsl .x .x6 .x6 2,
   .add .x .x3 .x3 .x6,.movz .x .x5 n 0] : List Instr) ++ movQ .x9 ++ ([.movz .x .x10 127 0] : List Instr)

def imm64 (r : Reg) (n : Nat) : List Instr :=
 ([.movz .x r (BitVec.ofNat 16 n) 0] : List Instr) ++ (List.range 3).map
 (fun i => .movk .x r (BitVec.ofNat 16 (n / 2^(16*(i+1)))) (i+1))

def vectorSetup : List Instr :=
 imm64 .x6 0xff050403ff020100 ++ imm64 .x7 0xff0b0a09ff080706 ++
 ([.vop (.dup .d2 .v3 .x6),.vop (.ins .d2 .v3 1 .x7),
 .movz .x .x10 65535 0,.movk .x .x10 127 1,
 .vop (.dup .s4 .v4 .x10),.vop (.dup .s4 .v5 .x9),
 .movz .x .x12 1 0,.movk .x .x12 1 2,.movz .x .x17 4 0,
 .movz .x .x0 0 0] : List Instr)

def guard : List Instr := [.subs .x .x16 .x4 .x17,.cselc .x .x16 .x5 .x0 .hs]

def vectorTry : List Instr :=
 [.ldrq .v0 .x2 0,.vop (.tbl .v1 .v0 .v3),.vop (.logic .and .v1 .v1 .v4),
 .vop (.sub .s4 .v2 .v1 .v5),.vop (.shift .ushr .s4 .v2 .v2 31),
 .umov .x .x6 .v2 0,.umov .x .x7 .v2 1,.logic .and .x .x6 .x6 .x7,
 .logic .eor .x .x6 .x6 .x12]

def vectorAccept : List Instr := [.strq .v1 .x3 0,.addImm .x .x3 .x3 16,
 .subImm .x .x4 .x4 4]

def vectorReject : List Instr := (List.range 4).flatMap
 (fun i => ([.umov .w .x11 .v1 i] : List Instr) ++ rnAccept)

def vectorBody : Prog isa := .seq (.block vectorTry) <|
 .seq (.ite (.zero .x .x6) (.block vectorAccept) (.block vectorReject)) <|
 .block (([.addImm .x .x2 .x2 12,.subImm .x .x5 .x5 4] : List Instr)++guard)

def wideRegs : List VReg := [.v16,.v17,.v18,.v19]
def wideGuard : List Instr :=
 [.subs .x .x16 .x4 .x17,.cselc .x .x16 .x5 .x0 .hs,
  .subs .x .x16 .x16 .x17,.cselc .x .x16 .x17 .x0 .hs]
def wideTry : List Instr :=
 ([.vop (.dup .d2 .v20 .x12)] : List Instr) ++ (List.range 4).flatMap (fun j =>
  let d := wideRegs[j]!
  [.addImm .x .x6 .x2 (12*j),.ldrq .v0 .x6 0,.vop (.tbl d .v0 .v3),.vop (.logic .and d d .v4),
   .vop (.sub .s4 .v2 d .v5),.vop (.shift .ushr .s4 .v2 .v2 31),.vop (.logic .and .v20 .v20 .v2)]) ++
 ([.umov .x .x6 .v20 0,.umov .x .x7 .v20 1,.logic .and .x .x6 .x6 .x7,.logic .eor .x .x6 .x6 .x12] : List Instr)
def wideAccept : List Instr :=
 (List.range 4).map (fun j => .strq wideRegs[j]! .x3 (16*j)) ++
 ([.addImm .x .x3 .x3 64,.subImm .x .x4 .x4 16] : List Instr)
def wideReject : List Instr := (List.range 16).flatMap fun j =>
 ([.umov .w .x11 wideRegs[j/4]! (j%4)] : List Instr) ++ rnAccept
def wideBody : Prog isa := .seq (.block wideTry) <|
 .seq (.ite (.zero .x .x6) (.block wideAccept) (.block wideReject)) <|
 .block (([.addImm .x .x2 .x2 48,.subImm .x .x5 .x5 16] : List Instr)++wideGuard)

def parse4 (_v : Nat) : Prog isa :=
 .seq (.block (vectorSetup++guard)) <|
 .seq (.ite (.zero .x .x16) (.block [])
   (.loop vectorBody (.nonzero .x .x16))) <|
 .seq (.block [.mul .x .x16 .x4 .x5]) <|
 .ite (.zero .x .x16) (.block []) scalarLoop

def parse (v : Nat) : Prog isa :=
 .seq (.block (vectorSetup++([.movz .x .x17 16 0] : List Instr)++wideGuard)) <|
 .seq (.ite (.zero .x .x16) (.block []) (.loop wideBody (.nonzero .x .x16))) (parse4 v)

def segment (v k off n : Nat) : Prog isa :=
 .seq (.block (setup k off n)) <| .seq (parse v) <|
 .block [.str .x .x4 .x19 (counts+8*k)]


end VG.Impl.MlDsa.AArch64.Optimized.ResidentRej
