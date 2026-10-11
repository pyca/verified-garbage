module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Pack.Encode
public import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Common

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Impl.MlKem.AArch64 (movImm mov)
open VG.Impl.MlDsa.AArch64.Pack

def vc (r : VReg) (n : Nat) : List Instr :=
 movImm .x9 (BitVec.ofNat 64 n) ++ ([.vop (.dup .s4 r .x9)] : List Instr)
def setup (signed : Bool) (b : Nat) : List Instr :=
 if signed then [mov .x2 .x3] ++ vc .v16 b ++ vc .v17 8380417 else []
def convert (r : VReg) : List Instr :=
 [.vop (.sub .s4 r .v16 r),.vop (.shift .sshr .s4 .v4 r 31),
  .vop (.logic .and .v4 .v4 .v17),.vop (.add .s4 r r .v4)]
def loadVec (signed : Bool) (c : Nat) : List Instr :=
 (List.range (c/4)).flatMap fun j =>
 let v := if j=0 then VReg.v0 else if j=1 then .v1 else if j=2 then .v2 else .v3
 ([.ldrq v .x0 (16*j)] : List Instr) ++ if signed then convert v else []
def field (d j : Nat) : List Instr :=
 let sh := d*j%64
 ([.umov .w .x10 (if j<4 then .v0 else .v1) (j%4)] : List Instr) ++
 (if sh=0 then [mov .x9 .x10] else
  [.lsl .x .x11 .x10 sh,.logic .orr .x .x9 .x9 .x11]) ++
 (if sh+d≥64 then ([.str .x .x9 .x2 (d*j/64*8)] : List Instr) ++
  (if sh+d>64 then [.lsr .x .x9 .x10 (64-sh)] else []) else [])
def tail (nb : Nat) : List Instr :=
 let off := nb/8*8
 let rem := nb%8
 (if rem≥4 then [.str .w .x9 .x2 off,.lsr .x .x9 .x9 32] else []) ++
 (if rem%4≥2 then [.strb .x9 .x2 (off+rem/4*4),.lsr .x .x9 .x9 8,
  .strb .x9 .x2 (off+rem/4*4+1),.lsr .x .x9 .x9 8] else []) ++
 (if rem%2=1 then [.strb .x9 .x2 (nb-1)] else [])
def width (signed : Bool) (b d c : Nat) : Prog isa :=
 .seq (.block (setup signed b ++ ([.movz .x .x15 (BitVec.ofNat 16 (256/c)) 0] : List Instr))) <|
 .loop (.block (loadVec signed c ++ (List.range c).flatMap (field d) ++ tail (d*c/8) ++
  ([.addImm .x .x0 .x0 (4*c),.addImm .x .x2 .x2 (d*c/8),.subImm .x .x15 .x15 1] : List Instr))) (.nonzero .x .x15)
def tblc (r : VReg) (xs : List Nat) : List Instr :=
 let lo := (List.range 8).foldl (fun v i => v + xs[i]! * 2^(8*i)) 0
 let hi := (List.range 8).foldl (fun v i => v + xs[8+i]! * 2^(8*i)) 0
 movImm .x9 (BitVec.ofNat 64 lo) ++ movImm .x10 (BitVec.ofNat 64 hi) ++
 ([.vop (.dup .d2 r .x9),.vop (.ins .d2 r 1 .x10)] : List Instr)
def four (signed : Bool) : Prog isa :=
 .seq (.block (setup signed 4 ++
  tblc .v18 [0,4,8,12,16,20,24,28,32,36,40,44,48,52,56,60] ++
  tblc .v19 [0,1,4,5,8,9,12,13,255,255,255,255,255,255,255,255] ++
  vc .v20 0x00ff00ff ++ ([.movz .x .x15 16 0] : List Instr))) <|
 .loop (.block (loadVec signed 16 ++
  ([.vop (.tblN false 4 .v0 .v0 .v18),.vop (.shift .ushr .s4 .v1 .v0 4),
   .vop (.logic .orr .v0 .v0 .v1),.vop (.logic .and .v0 .v0 .v20),
   .vop (.shift .ushr .s4 .v1 .v0 8),.vop (.logic .orr .v0 .v0 .v1),
   .vop (.tbl .v0 .v0 .v19),.umov .x .x9 .v0 0,.str .x .x9 .x2 0,
   .addImm .x .x0 .x0 64,.addImm .x .x2 .x2 8,.subImm .x .x15 .x15 1] : List Instr))) (.nonzero .x .x15)
def simple : Prog isa :=
 sel .x3 128 (four false) <| sel .x3 192 (width false 0 6 8) <|
 sel .x3 320 (width false 0 10 8) simpleBitPack
def signed : Prog isa :=
 sel .x4 96 (width true 2 3 8) <| sel .x4 128 (four true) <|
 sel .x4 416 (width true 4096 13 8) <| sel .x4 576 (width true 131072 18 4) <|
 sel .x4 640 (width true 524288 20 4) bitPack

end VG.Impl.MlDsa.AArch64.Optimized.KeygenPack
