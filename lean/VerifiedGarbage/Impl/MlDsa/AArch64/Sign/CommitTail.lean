import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector
import VerifiedGarbage.Impl.MlDsa.AArch64.Pack.Encode

/-! Commitment hashing and the next public-index mask share independent
64-bit Keccak lanes. The selected implementation remains entirely inline. -/
namespace VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg rounds)
open VG.Impl.MlKem.AArch64 (mov)

def save : List Instr := (List.range 8).map (fun i => .strq (vreg (8+i)) .x3 (16*i))
def restore : List Instr := (List.range 8).map (fun i => .ldrq (vreg (8+i)) .x3 (16*i))
def first : List Instr :=
 (List.range 4).flatMap (fun i => [.ldrq (vreg (2*i)) .x0 (16*i),
 .vop (.ext (vreg (2*i+1)) (vreg (2*i)) (vreg (2*i)) 8)]) ++
 (List.range 4).flatMap (fun i => [.ldrq (vreg (8+2*i)) .x1 (16*i),
 .vop (.ext (vreg (9+2*i)) (vreg (8+2*i)) (vreg (8+2*i)) 8)]) ++
 [.ldr .x .x6 .x1 64,.vop (.dup .d2 .v16 .x6)] ++
 (List.range 8).map (fun i => .vop (.movi0 (vreg (17+i))))
def output (n : Nat) : List Instr := (List.range (n/16)).flatMap (fun i =>
 [.vop (.perm .zip1 .d2 .v25 (vreg (2*i)) (vreg (2*i+1))),.strq .v25 .x2 (16*i)])
def saved : List Reg := [.x19,.x20,.x21,.x30]
def pro : List Instr := save ++
 (List.range 4).map (fun i => .str .x saved[i]! .x3 (128+8*i)) ++
 [mov .x19 .x3,mov .x20 .x6,mov .x21 .x2]
def upperInit : List Instr :=
 (List.range 8).flatMap (fun i => [.ldr .x .x7 .x4 (8*i),.vop (.ins .d2 (vreg i) 1 .x7)]) ++
 [.movz .x .x7 0 0] ++ (List.range 17).map (fun i => .vop (.ins .d2 (vreg (8+i)) 1 .x7)) ++
 [.lsl .x .x7 .x5 48,.lsr .x .x7 .x7 48,.movz .x .x8 31 1,.add .x .x7 .x7 .x8,
 .vop (.ins .d2 .v8 1 .x7),.movz .x .x7 0x8000 3,.vop (.ins .d2 .v16 1 .x7)]
def lowWord (r : VReg) (off : Nat) : List Instr :=
 [.ldr .x .x7 .x5 off,.vop (.movi0 .v25),.vop (.ins .d2 .v25 0 .x7),.vop (.logic .eor r r .v25)]
def full : List Instr := (List.range 17).flatMap (fun i => lowWord (vreg i) (8*i)) ++ [.addImm .x .x5 .x5 136]
def tail : List Instr := lowWord .v0 0 ++ lowWord .v1 8 ++
 [.movz .x .x7 31 0,.vop (.movi0 .v25),.vop (.ins .d2 .v25 0 .x7),.vop (.logic .eor .v2 .v2 .v25),
 .movz .x .x7 0x8000 3,.vop (.movi0 .v25),.vop (.ins .d2 .v25 0 .x7),.vop (.logic .eor .v16 .v16 .v25)]
def squeeze (n : Nat) : List Instr := [.addImm .x .x10 .x19 (256+136*n)] ++ (List.range 8).flatMap (fun i =>
 [.vop (.perm .trn2 .d2 .v26 (vreg (2*i)) (vreg (2*i+1))),.strq .v26 .x10 (16*i)]) ++
 [.umov .x .x7 .v16 1,.str .x .x7 .x10 128]
def epi : List Instr := [mov .x3 .x19] ++ restore ++
 (List.range 4).map (fun i => .ldr .x saved[i]! .x3 (128+8*i))
def coreFor (wlen : Nat) : Prog isa :=
 let n := (64+wlen)/136
 (List.range (n+1)).foldr (fun i rest =>
 .seq (.block rounds)
 (.seq (.block ((if i<5 then squeeze i else []) ++
 (if i<n-1 then full else if i==n-1 then
  (if wlen=768 then tail else
    [.movz .x .x7 31 0,.vop (.movi0 .v25),.vop (.ins .d2 .v25 0 .x7),.vop (.logic .eor .v0 .v0 .v25),
     .movz .x .x7 0x8000 3,.vop (.movi0 .v25),.vop (.ins .d2 .v25 0 .x7),.vop (.logic .eor .v16 .v16 .v25)])
 else []))) rest)) (.block [])
def code (wlen olen : Nat) : Prog isa :=
 .seq (.block (pro ++ first ++ upperInit ++ [.addImm .x .x5 .x1 72]))
 (.seq (coreFor wlen) (.seq (.block ([mov .x2 .x21]++output olen++[.addImm .x .x0 .x19 256,mov .x4 .x20]))
 (.seq (.seq (.block [.movz .x .x1 640 0]) VG.Impl.MlDsa.AArch64.Pack.bitUnpack) (.block epi))))

end VG.Impl.MlDsa.AArch64.Sign.CommitTail
