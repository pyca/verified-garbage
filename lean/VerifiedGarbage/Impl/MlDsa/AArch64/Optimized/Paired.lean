import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
import VerifiedGarbage.Impl.MlDsa.AArch64.Round.Round
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith
open VG.Impl.MlKem.AArch64 (mov)
namespace VG.Impl.MlDsa.AArch64.Optimized.PairedBase
def vr (i : Nat) : VReg := ([.v0,.v1,.v2,.v3,.v4,.v5,.v6,.v7,.v16,.v17,.v18,.v19,.v20,.v21,.v22,.v23] : List VReg)[i]!
def z (i : Nat) : Nat := (8380417-1753^Spec.MlDsa.bitRev8 i%8380417)%8380417
def bar (x : Nat) : Nat := x*2^31/8380417
def rootPair (off : Nat) : List Instr := [.ldrq .v28 .x1 off,.ldrq .v29 .x1 (off+16)]
/-- One shared-challenge product, with centered REDC output. -/
def productMont (d : VReg) : List Instr :=
 [.vop (.umull false .v26 .v24 .v25),.vop (.umull true .v27 .v24 .v25),
  .vop (.perm .uzp1 .s4 .v28 .v26 .v27),.vop (.mul .v28 .v28 .v30),
  .vop (.umlal false .v26 .v28 .v31),.vop (.umlal true .v27 .v28 .v31),
  .vop (.perm .uzp2 .s4 d .v26 .v27)]
def productCentered (d : VReg) : List Instr :=
 productMont d ++ ([.vop (.sub .s4 d d .v31)] : List Instr)
def product (j : Nat) : List Instr :=
 ([.ldrq .v24 .x13 (16*j)] : List Instr) ++
 ([0,1].flatMap fun p =>
 ([.ldrq .v25 .x14 (1024*p+16*j)] : List Instr) ++ productCentered (vr (8*p+j)))
def packed (a b : VReg) (len : Nat) : List Instr :=
 let perm := if len=1 then VPermOp.uzp1 else .trn1
 let perm2 := if len=1 then VPermOp.uzp2 else .trn2
 let shape := if len=1 then VArr.s4 else .d2
 ([.vop (.perm perm shape .v24 a b),.vop (.perm perm2 shape .v25 a b),
 .vop (.sub .s4 .v26 .v24 .v25),.vop (.add .s4 .v24 .v24 .v25),
 .vop (.sqdmulh .v27 .v26 .v29),.vop (.mul .v26 .v26 .v28),.vop (.mls .v26 .v27 .v31)] : List Instr) ++
 (if len=1 then [.vop (.perm .zip1 .s4 a .v24 .v26),.vop (.perm .zip2 .s4 b .v24 .v26)]
 else [.vop (.perm .trn1 .d2 a .v24 .v26),.vop (.perm .trn2 .d2 b .v24 .v26)])
def batchPair (a b : Nat) : List Instr :=
 [.vop (.sub .s4 .v24 (vr a) (vr b)),.vop (.add .s4 (vr a) (vr a) (vr b)),
  .vop (.sub .s4 .v25 (vr (a+8)) (vr (b+8))),.vop (.add .s4 (vr (a+8)) (vr (a+8)) (vr (b+8))),
  .vop (.sqdmulh .v26 .v24 .v29),.vop (.sqdmulh .v27 .v25 .v29),
  .vop (.mul (vr b) .v24 .v28),.vop (.mul (vr (b+8)) .v25 .v28),
  .vop (.mls (vr b) .v26 .v31),.vop (.mls (vr (b+8)) .v27 .v31)]
def firstBlock : List Instr :=
 (List.range 8).flatMap product ++
 ([1,2].flatMap fun len => (List.range 4).flatMap fun j =>
  rootPair ((if len=1 then 0 else 128)+32*j) ++
  [0,1].flatMap (fun p => packed (vr (8*p+2*j)) (vr (8*p+2*j+1)) len)) ++
 ([4,8,16].flatMap fun len => (List.range (16/len)).flatMap fun b =>
   rootPair ((if len=4 then 256 else if len=8 then 384 else 448)+32*b) ++
   (List.range (len/4)).flatMap (fun j => batchPair (b*len/2+j) (b*len/2+j+len/4))) ++
 ([0,1].flatMap fun p => (List.range 8).map fun j => Instr.strq (vr (8*p+j)) .x0 (1024*p+16*j)) ++
 ([.addImm .x .x13 .x13 128,.addImm .x .x14 .x14 128,.addImm .x .x0 .x0 128,.addImm .x .x1 .x1 480,.subImm .x .x11 .x11 1] : List Instr)
def finalStore : List Instr := [0,1].flatMap fun p => (List.range 8).map fun j => Instr.strq (vr (8*p+j)) .x2 (1024*p+128*j)
def finalBody : List Instr :=
 ([0,1].flatMap fun p => (List.range 8).map fun j => Instr.ldrq (vr (8*p+j)) .x2 (1024*p+128*j)) ++
 ([1,2,4].flatMap fun dist => (List.range (4/dist)).flatMap fun b =>
   rootPair (32*(8-(8/dist)+b)) ++
   (List.range dist).flatMap (fun j => batchPair (2*b*dist+j) (2*b*dist+j+dist))) ++
 rootPair 224 ++
 ((List.range 4).flatMap fun j =>
 [.vop (.sqdmulh .v24 (vr j) .v29),.vop (.sqdmulh .v25 (vr (8+j)) .v29),
  .vop (.mul (vr j) (vr j) .v28),.vop (.mul (vr (8+j)) (vr (8+j)) .v28),
  .vop (.mls (vr j) .v24 .v31),.vop (.mls (vr (8+j)) .v25 .v31)]) ++
 finalStore ++ ([.addImm .x .x2 .x2 16,.subImm .x .x12 .x12 1] : List Instr)
end VG.Impl.MlDsa.AArch64.Optimized.PairedBase
namespace VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Impl.MlDsa.AArch64.Round
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase
inductive Kind | z | r0 | h deriving BEq
def vc (r : VReg) (n : Nat) : List Instr := movW .x9 n ++ ([.vop (.dup .s4 r .x9)] : List Instr)
def saved : List VReg := [.v8,.v9,.v10,.v11,.v12,.v13,.v14,.v15]
def save : List Instr := saved.zipIdx.flatMap fun (r,i) => [.strq r .x0 (2048+16*i)]
def pro : List Instr :=
 [mov .x13 .x0,mov .x14 .x1,mov .x15 .x2,mov .x16 .x3,mov .x8 .x6,mov .x17 .x5,mov .x0 .x4] ++ save ++
 ([.adrSym .x1 "VG_MLDSA_INV_PAIR"] : List Instr)
def constants (kind : Kind) (g : Nat) : List Instr :=
 vc .v8 (2^22) ++ vc .v10 1 ++ ([.vop (.dup .s4 .v9 .x8),
 .vop (.sub .s4 .v9 .v9 .v10),.vop (.dup .s4 .v10 .x8),
 .vop (.add .s4 .v10 .v10 .v9),.vop (.movi0 .v30)] : List Instr) ++
 (match kind with
 | .z => []
 | .r0 => vc .v11 127 ++ vc .v12 (dMul g) ++ vc .v13 (2^(dShift g-1)) ++ vc .v14 (if g==261888 then 15 else dMod g) ++ vc .v15 (2*g)
 | .h => [.vop (.dup .s4 .v11 .x17),.vop (.movi0 .v13),
 .vop (.sub .s4 .v12 .v13 .v11),.vop (.movi0 .v14)])
def reduce : List Instr := [.vop (.add .s4 .v25 .v24 .v8),
 .vop (.shift .sshr .s4 .v25 .v25 23),.vop (.mls .v24 .v25 .v31)]
def norm : List Instr := [.vop (.add .s4 .v25 .v24 .v9),.vop (.umin .v25 .v25 .v10),
 .vop (.cmeq .s4 .v25 .v25 .v10),.vop (.logic .orr .v30 .v30 .v25)]
def check (kind : Kind) (g p j : Nat) : List Instr :=
 let d := vr (8*p+j)
 let off := 1024*p+128*j
 match kind with
 | .z => ([.ldrq .v27 .x15 off,.vop (.add .s4 .v24 d .v27)] : List Instr) ++ reduce ++
 ([.strq .v24 .x15 off] : List Instr) ++ norm
 | .r0 => ([.ldrq .v27 .x15 off,.vop (.sub .s4 .v24 .v27 d)] : List Instr) ++ reduce ++
 ([.vop (.shift .sshr .s4 .v25 .v24 31),.vop (.logic .and .v25 .v25 .v31),
 .vop (.add .s4 .v24 .v24 .v25),
 .vop (.add .s4 .v26 .v24 .v11),.vop (.shift .ushr .s4 .v26 .v26 7),
 .vop (.mul .v26 .v26 .v12),.vop (.add .s4 .v26 .v26 .v13),
 .vop (.shift .ushr .s4 .v26 .v26 (dShift g))] : List Instr) ++
 (if g==261888 then [.vop (.logic .and .v26 .v26 .v14)] else
 [.vop (.sub .s4 .v25 .v26 .v14),.vop (.shift .sshr .s4 .v25 .v25 31),.vop (.logic .and .v26 .v26 .v25)]) ++ ([.strq .v26 .x15 off,
 .vop (.mls .v24 .v26 .v15)] : List Instr) ++ reduce ++ ([.strq .v24 .x16 off] : List Instr) ++ norm
 | .h => ([.vop (.mov .v24 d)] : List Instr) ++ reduce ++ norm ++
 ([.ldrq .v27 .x15 off,.ldrq .v26 .x16 off,.vop (.add .s4 .v24 .v24 .v27),
 .vop (.sub .s4 .v25 .v11 .v24),.vop (.sub .s4 .v28 .v24 .v12),
 .vop (.logic .orr .v25 .v25 .v28),.vop (.shift .sshr .s4 .v25 .v25 31),
 .vop (.cmeq .s4 .v28 .v24 .v12),.vop (.cmeq .s4 .v26 .v26 .v13),
 .vop (.logic .bic .v28 .v28 .v26),.vop (.logic .orr .v25 .v25 .v28),
 .vop (.shift .ushr .s4 .v25 .v25 31),.strq .v25 .x15 off,
 .vop (.add .s4 .v14 .v14 .v25)] : List Instr)
def r0Lane (g : Nat) (raw a t h other : VReg) (off : Nat) : List Instr :=
 ([.ldrq other .x15 off,.vop (.sub .s4 a other raw),
 .vop (.add .s4 t a .v8),.vop (.shift .sshr .s4 t t 23),.vop (.mls a t .v31),
 .vop (.shift .sshr .s4 t a 31),.vop (.logic .and t t .v31),.vop (.add .s4 a a t),
 .vop (.add .s4 h a .v11),.vop (.shift .ushr .s4 h h 7),
 .vop (.mul h h .v12),.vop (.add .s4 h h .v13),.vop (.shift .ushr .s4 h h (dShift g))] : List Instr) ++
 (if g==261888 then [.vop (.logic .and h h .v14)] else
 [.vop (.sub .s4 t h .v14),.vop (.shift .sshr .s4 t t 31),.vop (.logic .and h h t)]) ++
 ([.strq h .x15 off,.vop (.mls a h .v15),
 .vop (.add .s4 t a .v8),.vop (.shift .sshr .s4 t t 23),.vop (.mls a t .v31),.strq a .x16 off,
 .vop (.add .s4 t a .v9),.vop (.umin t t .v10),.vop (.cmeq .s4 t t .v10),.vop (.logic .orr .v30 .v30 t)] : List Instr)
def r0Pair (g p j : Nat) : List Instr :=
 let d0 := vr (8*p+2*j)
 let d1 := vr (8*p+2*j+1)
 let a := r0Lane g d0 .v24 .v25 .v26 .v27 (1024*p+256*j)
 let b := r0Lane g d1 d0 d1 .v28 .v29 (1024*p+256*j+128)
 (a.zip b).flatMap fun (x,y) => [x,y]
def finalPaired (g : Nat) : List Instr :=
 VG.Impl.MlDsa.AArch64.Optimized.PairedBase.finalBody.take (VG.Impl.MlDsa.AArch64.Optimized.PairedBase.finalBody.length-VG.Impl.MlDsa.AArch64.Optimized.PairedBase.finalStore.length-2) ++
 ([0,1].flatMap fun p => (List.range 4).flatMap fun j => r0Pair g p j) ++
 ([.addImm .x .x2 .x2 16,.addImm .x .x15 .x15 16,.addImm .x .x16 .x16 16,.subImm .x .x12 .x12 1] : List Instr)
def final (kind : Kind) (g : Nat) : List Instr :=
 VG.Impl.MlDsa.AArch64.Optimized.PairedBase.finalBody.take (VG.Impl.MlDsa.AArch64.Optimized.PairedBase.finalBody.length-VG.Impl.MlDsa.AArch64.Optimized.PairedBase.finalStore.length-2) ++
 ([0,1].flatMap fun p => (List.range 8).flatMap fun j => check kind g p j) ++
 ([.addImm .x .x2 .x2 16,.addImm .x .x15 .x15 16,.addImm .x .x16 .x16 16,.subImm .x .x12 .x12 1] : List Instr)
def finish (kind : Kind) : List Instr :=
 ([.umov .w .x0 .v30 0,.umov .w .x9 .v30 1,.logic .orr .w .x0 .x0 .x9,
 .umov .w .x9 .v30 2,.logic .orr .w .x0 .x0 .x9,.umov .w .x9 .v30 3,
 .logic .orr .w .x0 .x0 .x9,.addImm .w .x0 .x0 1] : List Instr) ++
 (if kind==.h then [.lsl .x .x0 .x0 32,
 .umov .w .x9 .v14 0,.umov .w .x10 .v14 1,.add .w .x9 .x9 .x10,
 .umov .w .x10 .v14 2,.add .w .x9 .x9 .x10,.umov .w .x10 .v14 3,
 .add .w .x9 .x9 .x10,.logic .orr .x .x0 .x0 .x9] else []) ++
 saved.zipIdx.map (fun (r,i) => .ldrq r .x2 (1920+16*i))
def kernel (kind : Kind) (g : Nat) : Prog isa :=
 .seq (.block (movW .x10 4236238847 ++ ([.vop (.dup .s4 .v30 .x10)] : List Instr) ++
 movW .x9 8380417 ++ ([.vop (.dup .s4 .v31 .x9),.movz .x .x11 8 0] : List Instr))) <|
 .seq (.loop (.block VG.Impl.MlDsa.AArch64.Optimized.PairedBase.firstBlock) (.nonzero .x .x11)) <|
 .seq (.block (([.subImm .x .x0 .x0 1024,mov .x2 .x0,.movz .x .x12 8 0] : List Instr) ++ constants kind g)) <|
 .seq (.loop (.block (final kind g)) (.nonzero .x .x12)) (.block (finish kind))
def code (kind : Kind) : Prog isa := .seq (.block pro)
 (if kind==.r0 then zext .x17 <| onGamma .x17 .x7 (kernel kind) else kernel kind 0)
def kernelPaired (g : Nat) : Prog isa :=
 .seq (.block (movW .x10 4236238847 ++ ([.vop (.dup .s4 .v30 .x10)] : List Instr) ++
 movW .x9 8380417 ++ ([.vop (.dup .s4 .v31 .x9),.movz .x .x11 8 0] : List Instr))) <|
 .seq (.loop (.block VG.Impl.MlDsa.AArch64.Optimized.PairedBase.firstBlock) (.nonzero .x .x11)) <|
 .seq (.block (([.subImm .x .x0 .x0 1024,mov .x2 .x0,.movz .x .x12 8 0] : List Instr) ++ constants .r0 g)) <|
 .seq (.loop (.block (finalPaired g)) (.nonzero .x .x12)) (.block (finish .r0))
def codePaired : Prog isa := .seq (.block pro) (zext .x17 <| onGamma .x17 .x7 kernelPaired)
/-- Selected response kernel: only the r0 final checks are interleaved. -/
def selected (kind : Kind) : Prog isa := if kind == .r0 then codePaired else code kind
end VG.Impl.MlDsa.AArch64.Optimized.Paired
