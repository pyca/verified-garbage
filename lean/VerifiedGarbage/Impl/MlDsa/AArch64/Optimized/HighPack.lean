module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Round.Round
public import VerifiedGarbage.Impl.MlDsa.AArch64.Pack.Encode

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Optimized.HighPack
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Round
open VG.Impl.MlDsa.AArch64.Arith (movW)

def vc (d : VReg) (n : Nat) : List Instr :=
  movW .x9 (BitVec.ofNat 32 n) ++ ([.vop (.dup .s4 d .x9)] : List Instr)
def constants (g : Nat) : List Instr :=
  vc .v16 8380417 ++ vc .v17 127 ++ vc .v18 (dMul g) ++
  vc .v19 (2^(dShift g-1)) ++ vc .v20 (dMod g) ++ vc .v21 (2*g) ++
  vc .v22 1 ++ ([.vop (.movi0 .v23)] : List Instr)
def hf (g : Nat) (d a : VReg) : List Instr :=
  [.vop (.add .s4 d a .v17), .vop (.shift .ushr .s4 d d 7),
   .vop (.mul d d .v18), .vop (.add .s4 d d .v19),
   .vop (.shift .ushr .s4 d d (dShift g))]
def hb (g : Nat) (d a : VReg) : List Instr := hf g d a ++
  ([.vop (.sub .s4 .v7 d .v20), .vop (.shift .sshr .s4 .v7 .v7 31),
   .vop (.logic .and d d .v7)] : List Instr)
def packSetup : List Instr := ([.vop (.movi0 .v28)] : List Instr) ++
 VG.Impl.MlKem.AArch64.movImm .x9 0x0908060504020100 ++ ([.vop (.dup .d2 .v29 .x9)] : List Instr) ++
 VG.Impl.MlKem.AArch64.movImm .x9 0xffffffff0e0d0c0a ++ ([.vop (.ins .d2 .v29 1 .x9)] : List Instr) ++
 VG.Impl.MlKem.AArch64.movImm .x9 0xffff0504ffff0100 ++ ([.vop (.dup .d2 .v24 .x9)] : List Instr) ++
 VG.Impl.MlKem.AArch64.movImm .x9 0xffff0d0cffff0908 ++ ([.vop (.ins .d2 .v24 1 .x9)] : List Instr) ++
 VG.Impl.MlKem.AArch64.movImm .x9 0xffff0706ffff0302 ++ ([.vop (.dup .d2 .v25 .x9)] : List Instr) ++
 VG.Impl.MlKem.AArch64.movImm .x9 0xffff0f0effff0b0a ++ ([.vop (.ins .d2 .v25 1 .x9)] : List Instr)
def packTail (width : Nat) : List Instr :=
 ([.vop (.perm .uzp1 .b16 .v4 .v0 .v1),.vop (.perm .uzp1 .b16 .v5 .v2 .v3),
 .vop (.perm .uzp1 .b16 .v4 .v4 .v4),.vop (.perm .uzp1 .b16 .v5 .v5 .v5),
 .vop (.perm .zip1 .d2 .v6 .v4 .v5),
 .vop (.perm .uzp1 .b16 .v4 .v6 .v6),.vop (.perm .uzp2 .b16 .v5 .v6 .v6)] : List Instr) ++
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
 .seq (.block (constants g ++ packSetup ++ ([.movz .x .x11 16 0] : List Instr))) <|
 .loop (.block ((([.v0,.v1,.v2,.v3] : List VReg).zipIdx.flatMap fun (r,j) =>
 ([.ldrq r .x0 (16*j)] : List Instr) ++ hb g r r) ++ packTail width ++
 ([.addImm .x .x0 .x0 64,.addImm .x .x1 .x1 (2*width),.subImm .x .x11 .x11 1] : List Instr))) (.nonzero .x .x11)

end VG.Impl.MlDsa.AArch64.Optimized.HighPack
