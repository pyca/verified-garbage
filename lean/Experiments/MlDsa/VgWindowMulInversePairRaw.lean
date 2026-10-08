import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.TCB.AArch64.Print
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith
open VG.Impl.MlKem.AArch64 (mov)
namespace CombInvImmediate
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
end CombInvImmediate
def expandedVals : List Nat :=
 let first := (List.range 8).flatMap fun block =>
  [1,2,4,8,16].flatMap fun len =>
   (List.range (if len<4 then 4 else 16/len)).flatMap fun g =>
    let idx := 256/len-1-(32*block)/(2*len)-(if len=1 then 4*g else if len=2 then 2*g else g)
    let zs := if len=1 then (List.range 4).map fun j => CombInvImmediate.z (idx-j)
     else if len=2 then [CombInvImmediate.z idx,CombInvImmediate.z idx,CombInvImmediate.z (idx-1),CombInvImmediate.z (idx-1)]
     else List.replicate 4 (CombInvImmediate.z idx)
    zs ++ zs.map CombInvImmediate.bar
 let last := (List.range 8).flatMap fun j =>
  let z := if j=7 then 16382 else if j=6 then (CombInvImmediate.z 1*16382)%8380417 else CombInvImmediate.z (7-j)
  List.replicate 4 z ++ List.replicate 4 (CombInvImmediate.bar z)
 first ++ last
def expandedWords : List (BitVec 64) :=
 (List.range (expandedVals.length/2)).map fun j => BitVec.ofNat 64 (expandedVals[2*j]!+2^32*expandedVals[2*j+1]!)
def staticCode : Prog isa := .seq (.block [mov .x13 .x1,mov .x14 .x2,.adrSym .x1 "VG_MLDSA_INV_PAIR"]) CombInvImmediate.core
def main : IO Unit := do
 IO.FS.writeFile "/tmp/vg-window-multiply-inverse-pair-raw.body" (String.join ((printer.function staticCode).map (Rust.line printer.call)))
 IO.FS.writeFile "/tmp/vg-window-multiply-inverse-pair-raw.bindings" "        VG_MLDSA_INV_PAIR = sym super::consts::VG_MLDSA_INV_PAIR,\n"
 IO.FS.writeFile "/tmp/vg-window-inv-pair-consts.rs" (Rust.tablesFile "aarch64" [("VG_MLDSA_INV_PAIR",expandedWords)])
