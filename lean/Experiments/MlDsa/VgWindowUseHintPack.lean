import VerifiedGarbage.Impl.MlDsa.AArch64.Round.Round
import VerifiedGarbage.Impl.MlDsa.AArch64.Pack.Encode
import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.TCB.AArch64.Print
open VG VG.AArch64
namespace CombRound
open VG.Impl.MlDsa.AArch64.Round
open VG.Impl.MlDsa.AArch64.Arith (movW)

def vc (d : VReg) (n : Nat) : List Instr :=
  movW .x9 (BitVec.ofNat 32 n) ++ [.vop (.dup .s4 d .x9)]
def constants (g : Nat) : List Instr :=
  vc .v16 8380417 ++ vc .v17 127 ++ vc .v18 (dMul g) ++
  vc .v19 (2^(dShift g-1)) ++ vc .v20 (dMod g) ++ vc .v21 (2*g) ++
  vc .v22 1 ++ [.vop (.movi0 .v23)]
def hf (g : Nat) (d a : VReg) : List Instr :=
  [.vop (.add .s4 d a .v17), .vop (.shift .ushr .s4 d d 7),
   .vop (.mul d d .v18), .vop (.add .s4 d d .v19),
   .vop (.shift .ushr .s4 d d (dShift g))]
def hb (g : Nat) (d a : VReg) : List Instr := hf g d a ++
  [.vop (.sub .s4 .v7 d .v20), .vop (.shift .sshr .s4 .v7 .v7 31),
   .vop (.logic .and d d .v7)]
def csub (d : VReg) (modulus : VReg := .v16) : List Instr :=
  [.vop (.sub .s4 .v7 d modulus), .vop (.umin d d .v7)]
def cadd (d : VReg) : List Instr :=
  [.vop (.shift .sshr .s4 .v7 d 31), .vop (.logic .and .v7 .v7 .v16),
   .vop (.add .s4 d d .v7)]
def loop (ptrs : List Reg) (body : Nat → List Instr) : Prog isa :=
  .seq (.block [.movz .x .x10 16 0])
   (.loop (.block (([0,16,32,48].flatMap body) ++
     ptrs.map (fun r => .addImm .x r r 64) ++ [.subImm .x .x10 .x10 1])) (.nonzero .x .x10))
def bits (low : Bool) : Prog isa :=
  zext .x1 <| onGamma .x1 .x3 fun g => .seq (.block (constants g)) <|
   loop [.x0,.x2] fun off => [.ldrq .v0 .x0 off] ++ hb g .v1 .v0 ++
     (if low then [.vop (.mls .v0 .v1 .v21)] ++ cadd .v0 ++ [.strq .v0 .x2 off]
      else [.strq .v1 .x2 off])
def power2Round : Prog isa :=
  .seq (.block (vc .v16 8380417 ++ vc .v17 4095)) <|
   loop [.x0,.x1,.x2] fun off => [.ldrq .v0 .x0 off,
    .vop (.add .s4 .v1 .v0 .v17), .vop (.shift .ushr .s4 .v1 .v1 13),
    .vop (.shift .shl .s4 .v2 .v1 13), .vop (.sub .s4 .v0 .v0 .v2)] ++
    cadd .v0 ++ [.strq .v1 .x1 off,.strq .v0 .x2 off]
def normLt : Prog isa :=
 .seq (.block (vc .v16 8380417 ++ [.vop (.dup .s4 .v17 .x1), .vop (.movi0 .v31)])) <|
 .seq (loop [.x0] fun off => [.ldrq .v0 .x0 off,
   .vop (.sub .s4 .v1 .v16 .v0), .vop (.umin .v0 .v0 .v1),
   .vop (.umin .v1 .v0 .v17), .vop (.cmeq .s4 .v1 .v1 .v17),
   .vop (.logic .orr .v31 .v31 .v1)]) <|
 .block [.umov .w .x0 .v31 0,.umov .w .x9 .v31 1,.logic .orr .w .x0 .x0 .x9,
   .umov .w .x9 .v31 2,.logic .orr .w .x0 .x0 .x9,
   .umov .w .x9 .v31 3,.logic .orr .w .x0 .x0 .x9,
   .addImm .w .x0 .x0 1]
def makeHint : Prog isa :=
 zext .x2 <| .seq (onGamma .x2 .x4 fun g =>
  .seq (.block (constants g ++ [.vop (.movi0 .v31)])) <|
  loop [.x0,.x1,.x3] fun off => [.ldrq .v0 .x1 off,.ldrq .v2 .x0 off] ++
   hb g .v1 .v0 ++ [.vop (.add .s4 .v0 .v0 .v2)] ++ csub .v0 ++ hb g .v3 .v0 ++
   [.vop (.cmeq .s4 .v3 .v3 .v1), .vop (.not .v3 .v3),
    .vop (.shift .ushr .s4 .v3 .v3 31), .strq .v3 .x3 off,
    .vop (.add .s4 .v31 .v31 .v3)]) <|
 .block [.umov .w .x0 .v31 0,.umov .w .x9 .v31 1,.add .w .x0 .x0 .x9,
   .umov .w .x9 .v31 2,.add .w .x0 .x0 .x9,
   .umov .w .x9 .v31 3,.add .w .x0 .x0 .x9]
def useHint : Prog isa :=
 zext .x2 <| onGamma .x2 .x4 fun g => .seq (.block (constants g)) <|
 loop [.x0,.x1,.x3] fun off => [.ldrq .v0 .x1 off,.ldrq .v2 .x0 off] ++ hf g .v1 .v0 ++
 [.vop (.mul .v3 .v1 .v21), .vop (.sub .s4 .v3 .v3 .v0),
  .vop (.shift .ushr .s4 .v3 .v3 31), .vop (.shift .shl .s4 .v3 .v3 1),
  .vop (.sub .s4 .v3 .v3 .v22), .vop (.cmeq .s4 .v2 .v2 .v23),
  .vop (.logic .bic .v3 .v3 .v2), .vop (.add .s4 .v1 .v1 .v3),
  .vop (.add .s4 .v1 .v1 .v20)] ++ csub .v1 .v20 ++ csub .v1 .v20 ++ [.strq .v1 .x3 off]
end CombRound
namespace SquareHighPack
open VG.Impl.MlDsa.AArch64.Round
open VG.Impl.MlDsa.AArch64.Arith (movW)
open CombRound
-- Byte shuffle packs four 24-bit fields into twelve consecutive bytes.
def packSetup : List Instr := [.vop (.movi0 .v28)] ++
 VG.Impl.MlKem.AArch64.movImm .x9 0x0908060504020100 ++ [.vop (.dup .d2 .v29 .x9)] ++
 VG.Impl.MlKem.AArch64.movImm .x9 0xffffffff0e0d0c0a ++ [.vop (.ins .d2 .v29 1 .x9)] ++
 VG.Impl.MlKem.AArch64.movImm .x9 0xffff0504ffff0100 ++ [.vop (.dup .d2 .v24 .x9)] ++
 VG.Impl.MlKem.AArch64.movImm .x9 0xffff0d0cffff0908 ++ [.vop (.ins .d2 .v24 1 .x9)] ++
 VG.Impl.MlKem.AArch64.movImm .x9 0xffff0706ffff0302 ++ [.vop (.dup .d2 .v25 .x9)] ++
 VG.Impl.MlKem.AArch64.movImm .x9 0xffff0f0effff0b0a ++ [.vop (.ins .d2 .v25 1 .x9)]
def packTail (width : Nat) : List Instr :=
 [.vop (.perm .uzp1 .b16 .v4 .v0 .v1),.vop (.perm .uzp1 .b16 .v5 .v2 .v3),
 .vop (.perm .uzp1 .b16 .v4 .v4 .v4),.vop (.perm .uzp1 .b16 .v5 .v5 .v5),
 .vop (.perm .zip1 .d2 .v6 .v4 .v5),
 .vop (.perm .uzp1 .b16 .v4 .v6 .v6),.vop (.perm .uzp2 .b16 .v5 .v6 .v6)] ++
 (if width==4 then [.vop (.shift .shl .b16 .v5 .v5 4),.vop (.logic .orr .v4 .v4 .v5),
 .umov .x .x9 .v4 0,.str .x .x9 .x1 0]
 else [.vop (.perm .zip1 .b16 .v4 .v4 .v28),.vop (.perm .zip1 .b16 .v5 .v5 .v28),
 .vop (.shift .shl .s4 .v5 .v5 6),.vop (.logic .orr .v4 .v4 .v5),
 .vop (.tbl .v5 .v4 .v24),.vop (.tbl .v6 .v4 .v25),
 .vop (.shift .shl .s4 .v6 .v6 12),.vop (.logic .orr .v5 .v5 .v6),
 .vop (.tbl .v4 .v5 .v29),.umov .x .x9 .v4 0,.str .x .x9 .x1 0,
 .umov .w .x9 .v4 2,.str .w .x9 .x1 8])
def code (g : Nat) : Prog isa :=
 let width := if g==261888 then 4 else 6
 .seq (.block (constants g ++ packSetup ++ [.movz .x .x11 16 0])) <|
 .loop (.block ((([.v0,.v1,.v2,.v3] : List VReg).zipIdx.flatMap fun (r,j) =>
 [.ldrq r .x0 (16*j)] ++ hb g r r) ++ packTail width ++
 [.addImm .x .x0 .x0 64,.addImm .x .x1 .x1 (2*width),.subImm .x .x11 .x11 1])) (.nonzero .x .x11)
end SquareHighPack

namespace WindowHintPack
open VG.Impl.MlDsa.AArch64.Round
open CombRound
def four (g : Nat) (r : VReg) (off : Nat) : List Instr :=
 [.ldrq .v4 .x5 off,.ldrq .v5 .x4 off] ++ hf g .v6 .v4 ++
 [.vop (.mul .v26 .v6 .v21),.vop (.sub .s4 .v26 .v26 .v4),
  .vop (.shift .ushr .s4 .v26 .v26 31),.vop (.shift .shl .s4 .v26 .v26 1),
  .vop (.sub .s4 .v26 .v26 .v22),.vop (.cmeq .s4 .v5 .v5 .v23),
  .vop (.logic .bic .v26 .v26 .v5),.vop (.add .s4 .v6 .v6 .v26),
  .vop (.add .s4 .v6 .v6 .v20)] ++ csub .v6 .v20 ++ csub .v6 .v20 ++ [.vop (.mov r .v6)]
def code (g : Nat) : Prog isa :=
 let width := if g==261888 then 4 else 6
 .seq (.block (constants g ++ SquareHighPack.packSetup ++ [.movz .x .x11 16 0])) <|
 .loop (.block ((([.v0,.v1,.v2,.v3] : List VReg).zipIdx.flatMap fun (r,j) => four g r (16*j)) ++
  SquareHighPack.packTail width ++ [.addImm .x .x4 .x4 64,.addImm .x .x5 .x5 64,
  .addImm .x .x1 .x1 (2*width),.subImm .x .x11 .x11 1])) (.nonzero .x .x11)
-- ABI packedout, hints[256], canonicalw[256], gamma.
def prog : Prog isa := .seq (.block [.addImm .x .x4 .x1 0,.addImm .x .x5 .x2 0,.addImm .x .x1 .x0 0])
 (zext .x3 <| onGamma .x3 .x6 code)
end WindowHintPack

def main : IO Unit := do
 IO.FS.writeFile "/tmp/vg-window-usehint-pack.body" (String.join ((printer.function WindowHintPack.prog).map (Rust.line printer.call)))
 IO.FS.writeFile "/tmp/vg-window-usehint-reference.body" (String.join ((printer.function CombRound.useHint).map (Rust.line printer.call)))
 IO.FS.writeFile "/tmp/vg-window-hint-pack-reference.body" (String.join ((printer.function VG.Impl.MlDsa.AArch64.Pack.simpleBitPack).map (Rust.line printer.call)))
