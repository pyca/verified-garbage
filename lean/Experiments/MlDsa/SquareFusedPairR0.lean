import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
import VerifiedGarbage.Impl.MlDsa.AArch64.Round.Round
import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.TCB.AArch64.Print
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith
open VG.Impl.MlKem.AArch64 (mov)
namespace SquarePairBase
def vr (i : Nat) : VReg := ([.v0,.v1,.v2,.v3,.v4,.v5,.v6,.v7,.v16,.v17,.v18,.v19,.v20,.v21,.v22,.v23] : List VReg)[i]!
def z (i : Nat) : Nat := (8380417-1753^Spec.MlDsa.bitRev8 i%8380417)%8380417
def bar (x : Nat) : Nat := x*2^31/8380417
def setup : Prog isa := .block <| (List.range 256).flatMap fun j =>
 movW .x9 (z (255-j)) ++ [.str .w .x9 .x1 (4*j)] ++
 movW .x9 (bar (z (255-j))) ++ [.str .w .x9 .x1 (1024+4*j)]
def cv (r : VReg) (xs : List Nat) : List Instr :=
 movW .x9 xs[0]! ++ [.vop (.dup .s4 r .x9)] ++
 (List.range 3).flatMap (fun j => if xs[j+1]! = xs[0]! then [] else movW .x9 xs[j+1]! ++ [.vop (.ins .s4 r (j+1) .x9)])

def rootPair (off : Nat) : List Instr := [.ldrq .v28 .x1 off,.ldrq .v29 .x1 (off+16)]
def product (j : Nat) : List Instr :=
 [.ldrq .v24 .x13 (16*j)] ++
 ([0,1].flatMap fun p =>
 [.ldrq .v25 .x14 (1024*p+16*j),
  .vop (.umull false .v26 .v24 .v25),.vop (.umull true .v27 .v24 .v25),
  .vop (.perm .uzp1 .s4 .v28 .v26 .v27),.vop (.mul .v28 .v28 .v30),
  .vop (.umlal false .v26 .v28 .v31),.vop (.umlal true .v27 .v28 .v31),
  .vop (.perm .uzp2 .s4 (vr (8*p+j)) .v26 .v27),.vop (.sub .s4 (vr (8*p+j)) (vr (8*p+j)) .v31)])
def packed (a b : VReg) (len : Nat) : List Instr :=
 let perm := if len=1 then VPermOp.uzp1 else .trn1
 let perm2 := if len=1 then VPermOp.uzp2 else .trn2
 let shape := if len=1 then VArr.s4 else .d2
 [.vop (.perm perm shape .v24 a b),.vop (.perm perm2 shape .v25 a b),
 .vop (.sub .s4 .v26 .v24 .v25),.vop (.add .s4 .v24 .v24 .v25),
 .vop (.sqdmulh .v27 .v26 .v29),.vop (.mul .v26 .v26 .v28),.vop (.mls .v26 .v27 .v31)] ++
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
 [.addImm .x .x13 .x13 128,.addImm .x .x14 .x14 128,.addImm .x .x0 .x0 128,.addImm .x .x1 .x1 480,.subImm .x .x11 .x11 1]
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
 finalStore ++ [.addImm .x .x2 .x2 16,.subImm .x .x12 .x12 1]
def core : Prog isa :=
 .seq (.block (movW .x10 4236238847 ++ [.vop (.dup .s4 .v30 .x10)] ++ movW .x9 8380417 ++ [.vop (.dup .s4 .v31 .x9),.movz .x .x11 8 0])) <|
 .seq (.loop (.block firstBlock) (.nonzero .x .x11)) <|
 .seq (.block [.subImm .x .x0 .x0 1024,mov .x2 .x0,.movz .x .x12 8 0])
 (.loop (.block finalBody) (.nonzero .x .x12))
end SquarePairBase
namespace SquareFusedR0
open VG.Impl.MlDsa.AArch64.Round
open SquarePairBase
inductive Kind | z | r0 | h deriving BEq
def vc (r : VReg) (n : Nat) : List Instr := movW .x9 n ++ [.vop (.dup .s4 r .x9)]
def saved : List VReg := [.v8,.v9,.v10,.v11,.v12,.v13,.v14,.v15]
def save : List Instr := saved.zipIdx.flatMap fun (r,i) => [.strq r .x0 (2048+16*i)]
def pro : List Instr :=
 [mov .x13 .x0,mov .x14 .x1,mov .x15 .x2,mov .x16 .x3,mov .x8 .x6,mov .x17 .x5,mov .x0 .x4] ++ save ++
 [.adrSym .x1 "VG_MLDSA_INV_PAIR"]
def constants (kind : Kind) (g : Nat) : List Instr :=
 vc .v8 (2^22) ++ vc .v10 1 ++ [.vop (.dup .s4 .v9 .x8),
 .vop (.sub .s4 .v9 .v9 .v10),.vop (.dup .s4 .v10 .x8),
 .vop (.add .s4 .v10 .v10 .v9),.vop (.movi0 .v30)] ++
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
 | .z => [.ldrq .v27 .x15 off,.vop (.add .s4 .v24 d .v27)] ++ reduce ++
 [.strq .v24 .x15 off] ++ norm
 | .r0 => [.ldrq .v27 .x15 off,.vop (.sub .s4 .v24 .v27 d)] ++ reduce ++
 [.vop (.shift .sshr .s4 .v25 .v24 31),.vop (.logic .and .v25 .v25 .v31),
 .vop (.add .s4 .v24 .v24 .v25),
 .vop (.add .s4 .v26 .v24 .v11),.vop (.shift .ushr .s4 .v26 .v26 7),
 .vop (.mul .v26 .v26 .v12),.vop (.add .s4 .v26 .v26 .v13),
 .vop (.shift .ushr .s4 .v26 .v26 (dShift g))] ++
 (if g==261888 then [.vop (.logic .and .v26 .v26 .v14)] else
 [.vop (.sub .s4 .v25 .v26 .v14),.vop (.shift .sshr .s4 .v25 .v25 31),.vop (.logic .and .v26 .v26 .v25)]) ++ [.strq .v26 .x15 off,
 .vop (.mls .v24 .v26 .v15)] ++ reduce ++ [.strq .v24 .x16 off] ++ norm
 | .h => [.vop (.mov .v24 d)] ++ reduce ++ norm ++
 [.ldrq .v27 .x15 off,.ldrq .v26 .x16 off,.vop (.add .s4 .v24 .v24 .v27),
 .vop (.sub .s4 .v25 .v11 .v24),.vop (.sub .s4 .v28 .v24 .v12),
 .vop (.logic .orr .v25 .v25 .v28),.vop (.shift .sshr .s4 .v25 .v25 31),
 .vop (.cmeq .s4 .v28 .v24 .v12),.vop (.cmeq .s4 .v26 .v26 .v13),
 .vop (.logic .bic .v28 .v28 .v26),.vop (.logic .orr .v25 .v25 .v28),
 .vop (.shift .ushr .s4 .v25 .v25 31),.strq .v25 .x15 off,
 .vop (.add .s4 .v14 .v14 .v25)]
def r0Lane (g : Nat) (raw a t h other : VReg) (off : Nat) : List Instr :=
 [.ldrq other .x15 off,.vop (.sub .s4 a other raw),
 .vop (.add .s4 t a .v8),.vop (.shift .sshr .s4 t t 23),.vop (.mls a t .v31),
 .vop (.shift .sshr .s4 t a 31),.vop (.logic .and t t .v31),.vop (.add .s4 a a t),
 .vop (.add .s4 h a .v11),.vop (.shift .ushr .s4 h h 7),
 .vop (.mul h h .v12),.vop (.add .s4 h h .v13),.vop (.shift .ushr .s4 h h (dShift g))] ++
 (if g==261888 then [.vop (.logic .and h h .v14)] else
 [.vop (.sub .s4 t h .v14),.vop (.shift .sshr .s4 t t 31),.vop (.logic .and h h t)]) ++
 [.strq h .x15 off,.vop (.mls a h .v15),
 .vop (.add .s4 t a .v8),.vop (.shift .sshr .s4 t t 23),.vop (.mls a t .v31),.strq a .x16 off,
 .vop (.add .s4 t a .v9),.vop (.umin t t .v10),.vop (.cmeq .s4 t t .v10),.vop (.logic .orr .v30 .v30 t)]
def r0Pair (g p j : Nat) : List Instr :=
 let d0 := vr (8*p+2*j)
 let d1 := vr (8*p+2*j+1)
 let a := r0Lane g d0 .v24 .v25 .v26 .v27 (1024*p+256*j)
 let b := r0Lane g d1 d0 d1 .v28 .v29 (1024*p+256*j+128)
 (a.zip b).flatMap fun (x,y) => [x,y]
def finalPaired (g : Nat) : List Instr :=
 SquarePairBase.finalBody.take (SquarePairBase.finalBody.length-SquarePairBase.finalStore.length-2) ++
 ([0,1].flatMap fun p => (List.range 4).flatMap fun j => r0Pair g p j) ++
 [.addImm .x .x2 .x2 16,.addImm .x .x15 .x15 16,.addImm .x .x16 .x16 16,.subImm .x .x12 .x12 1]
def final (kind : Kind) (g : Nat) : List Instr :=
 SquarePairBase.finalBody.take (SquarePairBase.finalBody.length-SquarePairBase.finalStore.length-2) ++
 ([0,1].flatMap fun p => (List.range 8).flatMap fun j => check kind g p j) ++
 [.addImm .x .x2 .x2 16,.addImm .x .x15 .x15 16,.addImm .x .x16 .x16 16,.subImm .x .x12 .x12 1]
def finish (kind : Kind) : List Instr :=
 [.umov .w .x0 .v30 0,.umov .w .x9 .v30 1,.logic .orr .w .x0 .x0 .x9,
 .umov .w .x9 .v30 2,.logic .orr .w .x0 .x0 .x9,.umov .w .x9 .v30 3,
 .logic .orr .w .x0 .x0 .x9,.addImm .w .x0 .x0 1] ++
 (if kind==.h then [.lsl .x .x0 .x0 32,
 .umov .w .x9 .v14 0,.umov .w .x10 .v14 1,.add .w .x9 .x9 .x10,
 .umov .w .x10 .v14 2,.add .w .x9 .x9 .x10,.umov .w .x10 .v14 3,
 .add .w .x9 .x9 .x10,.logic .orr .x .x0 .x0 .x9] else []) ++
 saved.zipIdx.map (fun (r,i) => .ldrq r .x2 (1920+16*i))
def kernel (kind : Kind) (g : Nat) : Prog isa :=
 .seq (.block (movW .x10 4236238847 ++ [.vop (.dup .s4 .v30 .x10)] ++
 movW .x9 8380417 ++ [.vop (.dup .s4 .v31 .x9),.movz .x .x11 8 0])) <|
 .seq (.loop (.block SquarePairBase.firstBlock) (.nonzero .x .x11)) <|
 .seq (.block ([.subImm .x .x0 .x0 1024,mov .x2 .x0,.movz .x .x12 8 0] ++ constants kind g)) <|
 .seq (.loop (.block (final kind g)) (.nonzero .x .x12)) (.block (finish kind))
def code (kind : Kind) : Prog isa := .seq (.block pro)
 (if kind==.r0 then zext .x17 <| onGamma .x17 .x7 (kernel kind) else kernel kind 0)
def hLane (raw a t h low u : VReg) (off : Nat) : List Instr :=
 [.vop (.mov a raw),.vop (.add .s4 t a .v8),.vop (.shift .sshr .s4 t t 23),.vop (.mls a t .v31),
 .vop (.add .s4 t a .v9),.vop (.umin t t .v10),.vop (.cmeq .s4 t t .v10),.vop (.logic .orr .v30 .v30 t),
 .ldrq low .x15 off,.ldrq h .x16 off,.vop (.add .s4 a a low),
 .vop (.sub .s4 t .v11 a),.vop (.sub .s4 u a .v12),.vop (.logic .orr t t u),
 .vop (.shift .sshr .s4 t t 31),.vop (.cmeq .s4 u a .v12),.vop (.cmeq .s4 h h .v13),
 .vop (.logic .bic u u h),.vop (.logic .orr t t u),.vop (.shift .ushr .s4 t t 31),
 .strq t .x15 off,.vop (.add .s4 .v14 .v14 t)]
def hPair (p j : Nat) : List Instr :=
 let d0 := vr (8*p+2*j)
 let d1 := vr (8*p+2*j+1)
 let a := hLane d0 .v24 .v25 .v26 .v27 .v28 (1024*p+256*j)
 let b := hLane d1 d0 d1 .v29 .v28 .v27 (1024*p+256*j+128)
 (a.zip b).flatMap fun (x,y) => [x,y]
def zLane (raw a t other : VReg) (off : Nat) : List Instr :=
 [.ldrq other .x15 off,.vop (.add .s4 a raw other),
 .vop (.add .s4 t a .v8),.vop (.shift .sshr .s4 t t 23),.vop (.mls a t .v31),.strq a .x15 off,
 .vop (.add .s4 t a .v9),.vop (.umin t t .v10),.vop (.cmeq .s4 t t .v10),.vop (.logic .orr .v30 .v30 t)]
def zPair (p j : Nat) : List Instr :=
 let d0 := vr (8*p+2*j)
 let d1 := vr (8*p+2*j+1)
 let a := zLane d0 .v24 .v25 .v27 (1024*p+256*j)
 let b := zLane d1 d0 d1 .v28 (1024*p+256*j+128)
 (a.zip b).flatMap fun (x,y) => [x,y]
def finalOther (kind : Kind) : List Instr :=
 SquarePairBase.finalBody.take (SquarePairBase.finalBody.length-SquarePairBase.finalStore.length-2) ++
 ([0,1].flatMap fun p => (List.range 4).flatMap fun j => if kind==.h then hPair p j else zPair p j) ++
 [.addImm .x .x2 .x2 16,.addImm .x .x15 .x15 16,.addImm .x .x16 .x16 16,.subImm .x .x12 .x12 1]
def codeOther (kind : Kind) : Prog isa :=
 .seq (.block pro) <|
 .seq (.block (movW .x10 4236238847 ++ [.vop (.dup .s4 .v30 .x10)] ++
 movW .x9 8380417 ++ [.vop (.dup .s4 .v31 .x9),.movz .x .x11 8 0])) <|
 .seq (.loop (.block SquarePairBase.firstBlock) (.nonzero .x .x11)) <|
 .seq (.block ([.subImm .x .x0 .x0 1024,mov .x2 .x0,.movz .x .x12 8 0] ++ constants kind 0)) <|
 .seq (.loop (.block (finalOther kind)) (.nonzero .x .x12)) (.block (finish kind))
def kernelPaired (g : Nat) : Prog isa :=
 .seq (.block (movW .x10 4236238847 ++ [.vop (.dup .s4 .v30 .x10)] ++
 movW .x9 8380417 ++ [.vop (.dup .s4 .v31 .x9),.movz .x .x11 8 0])) <|
 .seq (.loop (.block SquarePairBase.firstBlock) (.nonzero .x .x11)) <|
 .seq (.block ([.subImm .x .x0 .x0 1024,mov .x2 .x0,.movz .x .x12 8 0] ++ constants .r0 g)) <|
 .seq (.loop (.block (finalPaired g)) (.nonzero .x .x12)) (.block (finish .r0))
def codePaired : Prog isa := .seq (.block pro) (zext .x17 <| onGamma .x17 .x7 kernelPaired)
end SquareFusedR0

def main : IO Unit := do
 let xs := printer.function (SquareFusedR0.code .r0)
 IO.FS.writeFile "/tmp/square-fused-pair-r0-mask.body" (String.join (xs.map (Rust.line printer.call)))
 IO.println s!"r0mask: {xs.length}"
 let ys := printer.function SquareFusedR0.codePaired
 IO.FS.writeFile "/tmp/square-fused-pair-r0-pipeline2.body" (String.join (ys.map (Rust.line printer.call)))
 IO.println s!"r0pipeline2: {ys.length}"
 for (name,kind) in [("h",SquareFusedR0.Kind.h),("z",.z)] do
  let zs := printer.function (SquareFusedR0.codeOther kind)
  IO.FS.writeFile ("/tmp/square-fused-pair-"++name++"-pipeline2.body") (String.join (zs.map (Rust.line printer.call)))

-- Additional emission helper is kept separate from shared sources.
