import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Resident
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentUnpack

/-! Two independent 66-byte ExpandMask seeds, with the paired Keccak state
resident through all five SHAKE256 blocks. The outer caller ABI is ordinary
AArch64; the resident kernel is inline and never exposed as a C function. -/
namespace VG.Impl.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Impl.MlKem.AArch64 (mov)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
def saved : List Reg := [.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28]
def epi : List Instr :=
 (List.range 8).flatMap (fun i => [.ldr .x .x8 .x19 (8048+8*i),.vop (.ins .d2 (vreg (8+i)) 0 .x8)]) ++
 (List.range 9).map (fun i => .ldr .x (saved[i+1]!) .x19 (7976+8*i)) ++
 [.ldr .x .x19 .x19 7968]
def seedWord (j : Nat) : List Instr :=
 [.ldr .x .x6 .x3 (8*j),.ldr .x .x7 .x4 (8*j),.vop (.dup .d2 .v0 .x6),
  .vop (.ins .d2 .v0 1 .x7),.strq .v0 .x2 (16*j)]
def seedLast (r n : Reg) : List Instr :=
 [.ldrb r n 64,.ldrb .x8 n 65,.lsl .x .x8 .x8 8,.add .x r r .x8]
def tailAdd : List Instr :=
 [.movz .x .x9 31 1,.add .x .x6 .x6 .x9,.add .x .x7 .x7 .x9]
def tailStore : List Instr :=
 [.vop (.dup .d2 .v0 .x6),.vop (.ins .d2 .v0 1 .x7),.strq .v0 .x2 128,
  .movz .x .x9 0x8000 3,.vop (.dup .d2 .v0 .x9),.strq .v0 .x2 256]
def tailPack : List Instr := tailAdd ++ tailStore
def seedTail : List Instr := seedLast .x6 .x3 ++ seedLast .x7 .x4 ++ tailPack
def absorbBody : List Instr := (List.range 8).flatMap seedWord ++ seedTail
def absorb (p : Nat) : List Instr :=
 [.addImm .x .x2 .x19 (400*p),.addImm .x .x3 .x20 (132*p),.addImm .x .x4 .x3 66] ++ absorbBody
def proArgs : List Instr := [.str .w .x1 .x4 7904,mov .x19 .x4,mov .x20 .x0,mov .x21 .x2,mov .x22 .x3]
def pro : List Instr :=
 (List.range 10).map (fun i => .str .x (saved[i]!) .x4 (7968+8*i)) ++
 (List.range 8).flatMap (fun i => [.umov .x .x8 (vreg (8+i)) 0,.str .x .x8 .x4 (8048+8*i)]) ++ proArgs
def zero : List Instr := [.vop (.movi0 .v0)] ++
 (List.range 25).map (fun i => .strq .v0 .x19 (16*i))
def parse (c : Nat) (p : Reg) (off : Nat) : Prog isa :=
 .seq (.block [.addImm .x .x0 .x19 off,mov .x4 p,.movz .x .x11 16 0])
 (.loop (.block (Unpack.body c)) (.nonzero .x .x11))
def parseBoth (c : Nat) : Prog isa := .seq (.block (Unpack.init c)) <|
 .seq (parse c .x21 840) (parse c .x22 1520)
def rawWith (core : Prog isa) : Prog isa :=
 .seq (.block (pro ++ zero ++ absorb 0 ++
 [mov .x23 .x19,.addImm .x .x24 .x19 840,.addImm .x .x25 .x19 1520])) <|
 .seq (Resident.maskPairWith core .x23 .x24 .x25) <|
 .seq (.block [.ldr .w .x27 .x19 7904,.lsr .x .x9 .x27 18]) <|
 .seq (.ite (.zero .x .x9) (parseBoth 18) (parseBoth 20)) (.block epi)

/-- Default resident implementation, using the standard inline SHA3 rounds. -/
def raw : Prog isa := rawWith Resident.permute

end VG.Impl.MlDsa.AArch64.Optimized.ResidentMask
