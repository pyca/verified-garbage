import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt4
import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.TCB.AArch64.Print

open VG VG.AArch64
open VG.Impl.MlKem.AArch64 (mov)
open VG.Impl.MlDsa.AArch64.Sample
namespace WindowSqueeze
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
def squeeze (a b : Reg) : List Instr :=
 (List.range 10).flatMap (fun i =>
  [.vop (.perm .trn1 .d2 .v26 (vreg (2*i)) (vreg (2*i+1))),
   .vop (.perm .trn2 .d2 .v27 (vreg (2*i)) (vreg (2*i+1))),
   .strq .v26 a (16*i),.strq .v27 b (16*i)]) ++
 [.umov .x .x6 .v20 0,.umov .x .x7 .v20 1,.str .x .x6 a 160,.str .x .x7 b 160]
def pair (sha3 : Bool) (p a b : Reg) : Prog isa :=
 .seq (.block (Impl.Sha3.AArch64.Neon.Pair.load p)) <|
 .seq (Impl.Sha3.AArch64.Neon.Pair.roundsProg sha3 24) <|
 .block (Impl.Sha3.AArch64.Neon.Pair.store p ++ squeeze a b)
def resident (sha3 : Bool) (p a b : Reg) : Prog isa :=
 .seq (.block (Impl.Sha3.AArch64.Neon.Pair.load p ++ [.movz .x .x28 5 0])) <|
 .seq (.loop (.seq (Impl.Sha3.AArch64.Neon.Pair.roundsProg sha3 24)
   (.block (squeeze a b ++ [.addImm .x a a 168,.addImm .x b b 168,.subImm .x .x28 .x28 1]))) (.nonzero .x .x28))
 (.block (Impl.Sha3.AArch64.Neon.Pair.store p))
def step (sha3 : Bool) : Prog isa :=
 .seq (pair sha3 .x22 .x24 .x25) (.seq (pair sha3 .x23 .x26 .x27) (.block Rej4.advance))
end WindowSqueeze
namespace ExpRej

-- These zero only the existing output range; rnSetup reinitializes x3/x4.
def zeroWide : Prog isa := .block <|
  [.movz .x .x9 0 0] ++ (List.range 128).map (fun i => .str .x .x9 .x26 (8*i))

def zeroNeon : Prog isa := .block <|
  [.vop (.movi0 .v0)] ++ (List.range 64).map (fun i => .strq .v0 .x26 (16*i))

def zero (v : Nat) : Prog isa := if v==0 then zeroWide else zeroNeon

def setup (pairs : Bool := false) : List Instr :=
  [.addImm .x .x2 .x25 840,mov .x3 .x26,.movz .x .x4 256 0,
   .movz .x .x5 (if pairs then 168 else 336) 0] ++ movQ .x9 ++
  [.movz .x .x10 65535 0,.movk .x .x10 127 1]

-- Stop consuming chunks once the output is full; x4 retains the exact
-- accept count, including on exhaustion/failure.
def stopWhenFull : Prog isa :=
  .ite (.zero .x .x4) (.block [.movz .x .x5 0 0]) (.block [])

-- Last load consumes the first padding byte at scratch+1848, within
-- the2048-byte scratch contract. The high byte is masked away.
def wideChunk : List Instr :=
  [.ldr .w .x11 .x2 0,.logic .and .x .x11 .x11 .x10,
   .addImm .x .x2 .x2 3,.subImm .x .x5 .x5 1]

def wideLoop : Prog isa := .seq (.block (setup false)) <|
  .loop (.seq (.block (wideChunk++rnAccept)) stopWhenFull) (.nonzero .x .x5)

-- Two3-byte candidates in one64-bit word; at most two masked padding
-- bytes are read, still inside the private scratch buffer.
def pairFirst : List Instr :=
  [.ldr .x .x6 .x2 0,.logic .and .x .x11 .x6 .x10] ++ rnAccept

def pairSecond : List Instr :=
  [.lsr .x .x11 .x6 24,.logic .and .x .x11 .x11 .x10] ++ rnAccept

def pairBody : Prog isa := .seq (.block pairFirst) <|
  .seq (.ite (.zero .x .x4) (.block []) (.block pairSecond)) <|
  .seq (.block [.addImm .x .x2 .x2 6,.subImm .x .x5 .x5 1]) stopWhenFull

def pairLoop : Prog isa :=
  .seq (.block (setup true)) (.loop pairBody (.nonzero .x .x5))

-- Bulk eight candidates while at least eight output slots remain. This
-- removes interior fullness branches and uses exactly three aligned loads.
def bulkExtract (i : Nat) : List Instr :=
  (match i with
   | 0 => [mov .x11 .x6]
   | 1 => [.lsr .x .x11 .x6 24]
   | 2 => [.extr .x .x11 .x7 .x6 48]
   | 3 => [.lsr .x .x11 .x7 8]
   | 4 => [.lsr .x .x11 .x7 32]
   | 5 => [.extr .x .x11 .x8 .x7 56]
   | 6 => [.lsr .x .x11 .x8 16]
   | _ => [.lsr .x .x11 .x8 40]) ++
  [.logic .and .x .x11 .x11 .x10] ++ rnAccept

def bulkBody : List Instr :=
  [.ldr .x .x6 .x2 0,.ldr .x .x7 .x2 8,.ldr .x .x8 .x2 16] ++
  (List.range 8).flatMap bulkExtract ++
  [.addImm .x .x2 .x2 24,.subImm .x .x5 .x5 8,
   .subs .x .x16 .x4 .x12,.cselc .x .x16 .x5 .x0 .hs]

def wideMulLoop : Prog isa :=
  .loop (.block (wideChunk++rnAccept++[.mul .x .x16 .x4 .x5])) (.nonzero .x .x16)

def bulkLoop : Prog isa :=
  .seq (.block (setup false++[.movz .x .x0 0 0,.movz .x .x12 8 0])) <|
   .seq (.loop (.block bulkBody) (.nonzero .x .x16)) <|
    .seq (.block [.mul .x .x16 .x4 .x5]) <|
     .ite (.zero .x .x16) (.block []) wideMulLoop

def mulLoop : Prog isa := .seq (.block (setup false)) wideMulLoop

-- Compact alternatives avoid inflating the sampler text by64stores.
def zeroNeonLoop : Prog isa :=
  .seq (.block [.vop (.movi0 .v0),mov .x3 .x26,.movz .x .x4 16 0]) <|
   .loop (.block [.strq .v0 .x3 0,.strq .v0 .x3 16,.strq .v0 .x3 32,
    .strq .v0 .x3 48,.addImm .x .x3 .x3 64,.subImm .x .x4 .x4 1]) (.nonzero .x .x4)

def parser (v : Nat) : Prog isa :=
  if v==0 then rnLoop else if v==1 then wideLoop else if v==2 then pairLoop else
    if v==3 then bulkLoop else mulLoop

def zeroFor (z : Nat) : Prog isa :=
  if z==0 then zeroPoly else if z==1 then zeroWide else if z==2 then zeroNeon else zeroNeonLoop

def sample (v z k : Nat) : Prog isa :=
  .seq (.block [.addImm .x .x25 .x19 (1008*k),.addImm .x .x26 .x21 (1024*k)]) <|
    .seq (zeroFor z) <| .seq (parser v) <|
      .block (retZ++[.logic .and .x .x27 .x27 .x0])

def rej4With (squeeze : Prog isa) (v z : Nat) : Prog isa :=
  .seq (.block (Rej4.init++Rej4.setup)) <|
   .seq (.loop squeeze (.nonzero .x .x28)) <|
    .seq (.block [.movz .x .x27 1 0]) <|
     .seq (sample v z 0) <| .seq (sample v z 1) <|
      .seq (sample v z 2) <| .seq (sample v z 3) (.block Rej4.epi)

def rejWith (c : Impl.Sha3.AArch64.Callee) (v z : Nat) : Prog isa :=
  .seq (.block (pro .x2 .x1 (.movz .x .x27 0 0) (.movz .x .x4 34 0))) <|
    .seq (spongeWith c 168 1008) <|
      .seq (zeroFor z) <| .seq (parser v) (.block (retZ++epi))
end ExpRej


namespace ExpRejFiveParse


-- Four remaining-output counters; disjoint from buffers and ABI saves.
def counts : Nat := 7904

def initCounts : List Instr := [.movz .x .x4 256 0] ++
  (List.range 4).map (fun k => .str .x .x4 .x19 (counts+8*k))

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

def setup (k off n : Nat) : List Instr :=
  [.addImm .x .x2 .x19 (840+1008*k),.addImm .x .x2 .x2 off,
   .addImm .x .x3 .x21 (1024*k),.ldr .x .x4 .x19 (counts+8*k),
   .movz .x .x6 256 0,.sub .x .x6 .x6 .x4,.lsl .x .x6 .x6 2,
   .add .x .x3 .x3 .x6,.movz .x .x5 n 0] ++ movQ .x9 ++ [.movz .x .x10 127 0]

def imm64 (r : Reg) (n : Nat) : List Instr :=
 [.movz .x r (BitVec.ofNat 16 n) 0] ++ (List.range 3).map
 (fun i => .movk .x r (BitVec.ofNat 16 (n / 2^(16*(i+1)))) (i+1))

def vectorSetup : List Instr :=
 imm64 .x6 0xff050403ff020100 ++ imm64 .x7 0xff0b0a09ff080706 ++
 [.vop (.dup .d2 .v3 .x6),.vop (.ins .d2 .v3 1 .x7),
 .movz .x .x10 65535 0,.movk .x .x10 127 1,
 .vop (.dup .s4 .v4 .x10),.vop (.dup .s4 .v5 .x9),
 .movz .x .x12 1 0,.movk .x .x12 1 2,.movz .x .x17 4 0,
 .movz .x .x0 0 0]

def guard : List Instr := [.subs .x .x16 .x4 .x17,.cselc .x .x16 .x5 .x0 .hs]

def vectorTry : List Instr :=
 [.ldrq .v0 .x2 0,.vop (.tbl .v1 .v0 .v3),.vop (.logic .and .v1 .v1 .v4),
 .vop (.sub .s4 .v2 .v1 .v5),.vop (.shift .ushr .s4 .v2 .v2 31),
 .umov .x .x6 .v2 0,.umov .x .x7 .v2 1,.logic .and .x .x6 .x6 .x7,
 .logic .eor .x .x6 .x6 .x12]

def vectorAccept : List Instr := [.strq .v1 .x3 0,.addImm .x .x3 .x3 16,
 .subImm .x .x4 .x4 4]

def vectorReject : List Instr := (List.range 4).flatMap
 (fun i => [.umov .w .x11 .v1 i] ++ rnAccept)

def vectorBody : Prog isa := .seq (.block vectorTry) <|
 .seq (.ite (.zero .x .x6) (.block vectorAccept) (.block vectorReject)) <|
 .block ([.addImm .x .x2 .x2 12,.subImm .x .x5 .x5 4]++guard)

def wideRegs : List VReg := [.v16,.v17,.v18,.v19]
def wideGuard : List Instr :=
 [.subs .x .x16 .x4 .x17,.cselc .x .x16 .x5 .x0 .hs,
  .subs .x .x16 .x16 .x17,.cselc .x .x16 .x17 .x0 .hs]
def wideTry : List Instr :=
 [.vop (.dup .d2 .v20 .x12)] ++ (List.range 4).flatMap (fun j =>
  let d := wideRegs[j]!
  [.addImm .x .x6 .x2 (12*j),.ldrq .v0 .x6 0,.vop (.tbl d .v0 .v3),.vop (.logic .and d d .v4),
   .vop (.sub .s4 .v2 d .v5),.vop (.shift .ushr .s4 .v2 .v2 31),.vop (.logic .and .v20 .v20 .v2)]) ++
 [.umov .x .x6 .v20 0,.umov .x .x7 .v20 1,.logic .and .x .x6 .x6 .x7,.logic .eor .x .x6 .x6 .x12]
def wideAccept : List Instr :=
 (List.range 4).map (fun j => .strq wideRegs[j]! .x3 (16*j)) ++
 [.addImm .x .x3 .x3 64,.subImm .x .x4 .x4 16]
def wideReject : List Instr := (List.range 16).flatMap fun j =>
 [.umov .w .x11 wideRegs[j/4]! (j%4)] ++ rnAccept
def wideBody : Prog isa := .seq (.block wideTry) <|
 .seq (.ite (.zero .x .x6) (.block wideAccept) (.block wideReject)) <|
 .block ([.addImm .x .x2 .x2 48,.subImm .x .x5 .x5 16]++wideGuard)

def parse4 (_v : Nat) : Prog isa :=
 .seq (.block (vectorSetup++guard)) <|
 .seq (.ite (.zero .x .x16) (.block [])
   (.loop vectorBody (.nonzero .x .x16))) <|
 .seq (.block [.mul .x .x16 .x4 .x5]) <|
 .ite (.zero .x .x16) (.block []) ExpRej.wideMulLoop

def parse (v : Nat) : Prog isa :=
 .seq (.block (vectorSetup++[.movz .x .x17 16 0]++wideGuard)) <|
 .seq (.ite (.zero .x .x16) (.block []) (.loop wideBody (.nonzero .x .x16))) (parse4 v)

def segment (v k off n : Nat) : Prog isa :=
 .seq (.block (setup k off n)) <| .seq (parse v) <|
 .block [.str .x .x4 .x19 (counts+8*k)]

def batch (v off n : Nat) : Prog isa :=
 .seq (segment v 0 off n) <| .seq (segment v 1 off n) <|
 .seq (segment v 2 off n) (segment v 3 off n)

def zeros : Prog isa := .block <| [.vop (.movi0 .v0)] ++
 (List.range 256).map (fun i => .strq .v0 .x21 (16*i))

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
 ((List.range 4).foldr (fun k rest => .seq (zeroTail k) rest) (.block []))

def flags : List Instr := [.ldr .x .x27 .x19 counts] ++
 (List.range 3).flatMap (fun k => [.ldr .x .x6 .x19 (counts+8*(k+1)),
 .logic .orr .x .x27 .x27 .x6])

def rej4With (sha3 : Bool) (squeeze : Prog isa) (v : Nat) : Prog isa :=
 .seq (.block (Rej4.init++initCounts)) <|
 .seq (.block (squeezeSetup 0 5)) <|
 .seq (WindowSqueeze.resident sha3 .x22 .x24 .x25) <| .seq (WindowSqueeze.resident sha3 .x23 .x26 .x27) <|
 .seq (batch v 0 168) <| .seq (batch v 504 112) <|
 .seq (.block flags) <|
 .seq (.ite (.zero .x .x27) (.block [])
 (.seq (squeezeN squeeze 840 1) <| .seq (batch v 840 56) (.block flags))) <|
 .seq tailZeros <| .block ([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63]++Rej4.epi)
def synthetic (legacy : Bool) : Prog isa :=
 .seq (.block (Rej4.pro++initCounts)) <|
 .seq (if legacy then zeros else .block []) <|
 .seq (batch 0 0 336) <| .seq (.block flags) <|
 .seq (if legacy then .block [] else tailZeros) <|
 .block ([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63]++Rej4.epi)
end ExpRejFiveParse

def main : IO Unit := do
 for (name,sha3) in [("baseline",false),("sha3",true)] do
  IO.FS.writeFile ("/tmp/vg-window-rej4-resident5-"++name++".body")
   (String.join ((printer.function (ExpRejFiveParse.rej4With sha3 (WindowSqueeze.step sha3) 0)).map (Rust.line printer.call)))

-- Standalone synthetic-parser entry points for forced rejection/exhaustion tests.
#eval do
 for (name,legacy) in [("legacy",true),("tail",false)] do
  IO.FS.writeFile ("/tmp/vg-window-rej4-resident5-synthetic-"++name++".body")
   (String.join ((printer.function (ExpRejFiveParse.synthetic legacy)).map (Rust.line printer.call)))
