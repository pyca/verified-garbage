import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt4
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded

/-!
Four bounded secret-polynomial samplers, in two independent pairs of SHAKE256
lanes. Each stream consumes up to 544 bytes, in two 272-byte batches. The
four-nibble vector parser runs only with at least four output slots remaining;
the existing scalar parser handles the final coefficient slots. Masked mode
zeros each unsuccessful polynomial and returns the conjunction of all four
success flags. The compaction-table address depends only on rejection bits.
-/

namespace VG.Impl.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Impl.MlKem.AArch64 (mov)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.Sha3.AArch64.Neon.Pair (load store roundsProg)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

def counts : Nat := 7904
def initCounts : List Instr := ([.movz .x .x4 256 0] : List Instr) ++
 (List.range 4).map (fun k => .str .x .x4 .x19 (counts+8*k))
def absorbPair (p : Nat) : List Instr :=
 ([.addImm .x .x2 .x19 (400*p),.addImm .x .x3 .x20 (132*p),.addImm .x .x4 .x3 66] : List Instr) ++
 (List.range 8).flatMap Rej4.seedWord ++
 ([.ldrb .x6 .x3 64,.ldrb .x8 .x3 65,.lsl .x .x8 .x8 8,.add .x .x6 .x6 .x8,
  .ldrb .x7 .x4 64,.ldrb .x8 .x4 65,.lsl .x .x8 .x8 8,.add .x .x7 .x7 .x8] : List Instr) ++
 Rej4.tailAdd ++ ([.vop (.dup .d2 .v0 .x6),.vop (.ins .d2 .v0 1 .x7),.strq .v0 .x2 128,
 .movz .x .x9 0x8000 3,.vop (.dup .d2 .v0 .x9),.strq .v0 .x2 256] : List Instr)
def squeeze (a b : Reg) : List Instr := (List.range 17).flatMap (fun i =>
 [.umov .x .x6 (vreg i) 0,.umov .x .x7 (vreg i) 1,.str .x .x6 a (8*i),.str .x .x7 b (8*i)])
def pair (sha3 : Bool) (p a b : Reg) : Prog isa :=
 .seq (.block (load p)) <| .seq (roundsProg sha3 24) (.block (store p++squeeze a b))
def squeezeStep (sha3 : Bool) : Prog isa :=
 .seq (pair sha3 .x22 .x24 .x25) <| .seq (pair sha3 .x23 .x26 .x27) <|
 .block [.addImm .x .x24 .x24 136,.addImm .x .x25 .x25 136,
 .addImm .x .x26 .x26 136,.addImm .x .x27 .x27 136,.subImm .x .x28 .x28 1]
def squeezeTwo (sha3 : Bool) (off : Nat) : Prog isa :=
 .seq (.block ([mov .x22 .x19,.addImm .x .x23 .x19 400,
 .addImm .x .x24 .x19 (840+off),.addImm .x .x25 .x19 (1384+off),
 .addImm .x .x26 .x19 (1928+off),.addImm .x .x27 .x19 (2472+off),
 .movz .x .x28 2 0])) (.loop (squeezeStep sha3) (.nonzero .x .x28))
def imm64 (r : Reg) (n : Nat) : List Instr :=
 ([.movz .x r (BitVec.ofNat 16 n) 0] : List Instr) ++ (List.range 3).map
 (fun i => .movk .x r (BitVec.ofNat 16 (n / 2^(16*(i+1)))) (i+1))
def bytesWord (xs : List Nat) : Nat := ((xs.zipIdx).map (fun (x,i) => x*2^(8*i))).sum
/-- Accepted source lanes, in their original order. -/
def acceptedIndices (mask : Nat) : List Nat :=
 (List.range 4).filter (fun i => mask / 2^i % 2 == 1)

/-- Lane indices written by the original scalar parser at this mask. -/
def writtenIndices (mask : Nat) : List Nat :=
 acceptedIndices mask ++ if mask / 8 % 2 == 0 then [3] else []

/-- Byte indices for the selected TBL compaction. -/
def shuffleBytes (mask : Nat) : List Nat :=
 let writes := writtenIndices mask
 (List.range 4).flatMap (fun i => (List.range 4).map (fun j =>
   if i < writes.length then 4*(writes[i]!) + j else 255))

-- Shuffle accepted coefficients first, followed by the last rejected value
-- iff the last nibble rejects. Blend preserves all other output bytes.
def entryInit (fast : Bool) (mask : Nat) : List Instr := Id.run do
 let ids := acceptedIndices mask
 let writes := writtenIndices mask
 let sh := shuffleBytes mask
 let wm := (List.range 16).map (fun i => if i < 4*writes.length then 255 else 0)
 let mut code := []
 for (off,bs) in ([(0,sh.take 8),(8,sh.drop 8)] ++ if fast then [] else [(16,wm.take 8),(24,wm.drop 8)]) do
  code := code ++ imm64 .x6 (bytesWord bs) ++ ([.str .x .x6 .x19 (6000+64*mask+off)] : List Instr)
 code := code ++ ([.movz .x .x6 (BitVec.ofNat 16 ids.length) 0,.str .x .x6 .x19 (6000+64*mask+32)] : List Instr)
 return code
def tableInit (fast : Bool) : List Instr := (List.range 16).flatMap (entryInit fast)
def vectorSetup (_eta : Nat) : List Instr :=
 imm64 .x6 0xffffff01ffffff00 ++ imm64 .x7 0xffffff03ffffff02 ++
 ([.vop (.dup .d2 .v25 .x6),.vop (.ins .d2 .v25 1 .x7),
 .vop (.dup .b16 .v23 .x11),.vop (.dup .s4 .v22 .x15),.vop (.dup .s4 .v21 .x9),
 .vop (.dup .s4 .v20 .x10),.vop (.add .s4 .v20 .v20 .v21),.movz .x .x6 13 0,.vop (.dup .s4 .v18 .x6),
 .movz .x .x6 5 0,.vop (.dup .s4 .v19 .x6)] : List Instr) ++
 imm64 .x6 0x0000000200000001 ++ imm64 .x7 0x0000000800000004 ++
 ([.vop (.dup .d2 .v24 .x6),.vop (.ins .d2 .v24 1 .x7),
 .movz .x .x0 0 0,.movz .x .x16 4 0,.addImm .x .x12 .x19 3000,.addImm .x .x12 .x12 3000] : List Instr)
def valueTail : List Instr :=
 [.vop (.sub .s4 .v1 .v20 .v1),.vop (.sub .s4 .v2 .v1 .v21),.vop (.umin .v1 .v1 .v2)]
def vectorVal (eta : Nat) : List Instr :=
 (if eta==2 then [.vop (.mul .v2 .v1 .v18),.vop (.shift .ushr .s4 .v2 .v2 6),
 .vop (.mul .v2 .v2 .v19),.vop (.sub .s4 .v1 .v1 .v2)] else []) ++ valueTail
def vectorBody (fast : Bool) (eta : Nat) : List Instr :=
 ([.ldr .w .x6 .x2 0,.vop (.dup .s4 .v0 .x6),.vop (.logic .and .v1 .v0 .v23),
 .vop (.shift .ushr .b16 .v0 .v0 4),.vop (.perm .zip1 .b16 .v0 .v1 .v0),
 .vop (.tbl .v1 .v0 .v25),.vop (.sub .s4 .v2 .v1 .v22),
 .vop (.shift .ushr .s4 .v2 .v2 31),.vop (.mul .v2 .v2 .v24),
 .umov .x .x6 .v2 0,.umov .x .x7 .v2 1,.add .x .x6 .x6 .x7,
 .lsr .x .x7 .x6 32,.add .x .x6 .x6 .x7,.logic .and .x .x6 .x6 .x11,
 .lsl .x .x6 .x6 6,.add .x .x13 .x12 .x6,.ldrq .v6 .x13 0,
 .ldr .x .x6 .x13 32] : List Instr) ++ vectorVal eta ++
 ([.vop (.tbl .v1 .v1 .v6)] : List Instr) ++
 (if fast then [.strq .v1 .x3 0] else [.ldrq .v7 .x13 16,.ldrq .v0 .x3 0,.vop (.bsel .bsl .v7 .v1 .v0),.strq .v7 .x3 0]) ++
 ([.lsl .x .x7 .x6 2,.add .x .x3 .x3 .x7,.sub .x .x4 .x4 .x6,
 .addImm .x .x2 .x2 2,.subImm .x .x5 .x5 2,
 .subs .x .x8 .x4 .x16,.cselc .x .x8 .x5 .x0 .hs] : List Instr)
def parse (fast : Bool) (eta k off : Nat) : Prog isa :=
 .seq (.block (([.addImm .x .x2 .x19 (840+544*k+off),
 .addImm .x .x3 .x21 (1024*k),.ldr .x .x4 .x19 (counts+8*k),
 .movz .x .x6 256 0,.sub .x .x6 .x6 .x4,.lsl .x .x6 .x6 2,.add .x .x3 .x3 .x6,
 .movz .x .x5 272 0] : List Instr)++movQ .x9++([.movz .x .x10 (BitVec.ofNat 16 eta) 0,
 .movz .x .x11 15 0,.movz .x .x15 (BitVec.ofNat 16 (rbBound eta)) 0] : List Instr)++vectorSetup eta++
 ([.subs .x .x8 .x4 .x16,.cselc .x .x8 .x5 .x0 .hs] : List Instr))) <|
 .seq (.ite (.zero .x .x8) (.block []) (.loop (.block (vectorBody fast eta)) (.nonzero .x .x8))) <|
 .seq (.block [.movz .x .x16 10 0,.movz .x .x17 5 0,.mul .x .x8 .x4 .x5]) <|
 .seq (.ite (.zero .x .x8) (.block [])
 (.loop (.seq (rbBody eta) (.block [.mul .x .x8 .x4 .x5])) (.nonzero .x .x8))) <|
 .block [.str .x .x4 .x19 (counts+8*k)]
def batch (fast : Bool) (eta off : Nat) : Prog isa :=
 .seq (parse fast eta 0 off) <| .seq (parse fast eta 1 off) <|
 .seq (parse fast eta 2 off) (parse fast eta 3 off)
def flags : List Instr := ([.ldr .x .x27 .x19 counts] : List Instr) ++
 (List.range 3).flatMap (fun k => [.ldr .x .x6 .x19 (counts+8*(k+1)),
 .logic .orr .x .x27 .x27 .x6])
def maskOne (k : Nat) : Prog isa :=
 .seq (.block [.ldr .x .x4 .x19 (counts+8*k),.subImm .x .x4 .x4 1,
 .lsr .x .x4 .x4 63,.movz .x .x6 0 0,.sub .w .x4 .x6 .x4,
 .vop (.dup .s4 .v0 .x4),.addImm .x .x3 .x21 (1024*k),.movz .x .x5 64 0]) <|
 .loop (.block [.ldrq .v1 .x3 0,.vop (.logic .and .v1 .v1 .v0),.strq .v1 .x3 0,
 .addImm .x .x3 .x3 16,.subImm .x .x5 .x5 1]) (.nonzero .x .x5)
def sampler (sha3 mask : Bool) (eta : Nat) : Prog isa :=
 .seq (.block (Rej4.pro++Rej4.zeroStates++absorbPair 0++absorbPair 1++initCounts++tableInit mask)) <|
 .seq (squeezeTwo sha3 0) <| .seq (batch mask eta 0) <| .seq (.block flags) <|
 .seq (.ite (.zero .x .x27) (.block [])
   (.seq (squeezeTwo sha3 272) <| .seq (batch mask eta 272) (.block flags))) <|
 .seq (if mask then .seq (maskOne 0) <| .seq (maskOne 1) <| .seq (maskOne 2) (maskOne 3) else .block []) <|
 .block (([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63] : List Instr)++Rej4.epi)

end VG.Impl.MlDsa.AArch64.Optimized.BoundedFour
