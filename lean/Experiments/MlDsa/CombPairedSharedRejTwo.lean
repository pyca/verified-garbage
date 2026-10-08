import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector
import VerifiedGarbage.Impl.MlDsa.AArch64.Call
import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Vec
import VerifiedGarbage.Variants.Keccak.AArch64.Sha3
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.Sign
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Inst
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt4
import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.TCB.AArch64.Print
namespace WindowShared
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
local instance : Inhabited (Prog isa) := ⟨.block []⟩
def symbol := "vg_keccak_resident_sha3_internal"
def resident : Prog isa := .block rounds
partial def straight : Prog isa → Option (List Instr)
 | .block xs => some xs
 | .seq a b => do return (←straight a)++(←straight b)
 | _ => none
partial def splitBlock (xs : List Instr) : Prog isa :=
 if rounds.isPrefixOf xs then .seq (.call symbol resident) (splitBlock (xs.drop rounds.length))
 else match xs with
 | [] => .block []
 | x::rest => .seq (.block [x]) (splitBlock rest)
partial def rewrite (c : Prog isa) : Prog isa :=
 match straight c with
 | some xs => splitBlock xs
 | none => match c with
   | .seq a b => .seq (rewrite a) (rewrite b)
   | .ite q a b => .ite q (rewrite a) (rewrite b)
   | .loop b q => .loop (rewrite b) q
   | .frame i b j => .frame i (rewrite b) j
   | _ => c
def wrap (c : Prog isa) : Prog isa := .frame (.push .x30) (rewrite c) (.pop .x30)
def emit (path : String) (c : Prog isa) : IO Unit := do
 IO.FS.writeFile path (String.join ((printer.function (wrap c)).map (Rust.line printer.call)))
end WindowShared

namespace RootPaired
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
namespace SquareFusedPair
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
 | .r0 => vc .v11 127 ++ vc .v12 (dMul g) ++ vc .v13 (2^(dShift g-1)) ++ vc .v14 (dMod g) ++ vc .v15 (2*g)
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
 .vop (.shift .ushr .s4 .v26 .v26 (dShift g)),
 .vop (.sub .s4 .v25 .v26 .v14),.vop (.shift .sshr .s4 .v25 .v25 31),
 .vop (.logic .and .v26 .v26 .v25),.strq .v26 .x15 off,
 .vop (.mls .v24 .v26 .v15)] ++ reduce ++ [.strq .v24 .x16 off] ++ norm
 | .h => [.vop (.mov .v24 d)] ++ reduce ++ norm ++
 [.ldrq .v27 .x15 off,.ldrq .v26 .x16 off,.vop (.add .s4 .v24 .v24 .v27),
 .vop (.sub .s4 .v25 .v11 .v24),.vop (.sub .s4 .v28 .v24 .v12),
 .vop (.logic .orr .v25 .v25 .v28),.vop (.shift .sshr .s4 .v25 .v25 31),
 .vop (.cmeq .s4 .v28 .v24 .v12),.vop (.cmeq .s4 .v26 .v26 .v13),
 .vop (.logic .bic .v28 .v28 .v26),.vop (.logic .orr .v25 .v25 .v28),
 .vop (.shift .ushr .s4 .v25 .v25 31),.strq .v25 .x15 off,
 .vop (.add .s4 .v14 .v14 .v25)]
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
end SquareFusedPair

end RootPaired
namespace RootDotInv
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith
open VG.Impl.MlKem.AArch64 (mov)
namespace CombInvImmediate
def vr : Nat → VReg | 0 => .v0 | 1 => .v1 | 2 => .v2 | 3 => .v3 | 4 => .v4 | 5 => .v5 | 6 => .v6 | _ => .v7
def z (i : Nat) : Nat := (8380417-1753^Spec.MlDsa.bitRev8 i%8380417)%8380417
def bar (x : Nat) : Nat := x*2^31/8380417
def setup : Prog isa := .block <| (List.range 256).flatMap fun j =>
 movW .x9 (z (255-j)) ++ [.str .w .x9 .x1 (4*j)] ++
 movW .x9 (bar (z (255-j))) ++ [.str .w .x9 .x1 (1024+4*j)]
def cv (r : VReg) (xs : List Nat) : List Instr :=
 movW .x9 xs[0]! ++ [.vop (.dup .s4 r .x9)] ++
 (List.range 3).flatMap (fun j => if xs[j+1]! = xs[0]! then [] else movW .x9 xs[j+1]! ++ [.vop (.ins .s4 r (j+1) .x9)])
def root (idx len : Nat) : List Instr :=
 let off := 4*(255-idx)
 if len=1 then [.ldrq .v20 .x1 off,.ldrq .v21 .x1 (1024+off)]
 else if len=2 then [.ldr .x .x9 .x1 off,.ldr .x .x10 .x1 (1024+off),
 .vop (.dup .d2 .v20 .x9),.vop (.dup .d2 .v21 .x10),
 .vop (.perm .zip1 .s4 .v20 .v20 .v20),.vop (.perm .zip1 .s4 .v21 .v21 .v21)]
 else [.ldr .w .x9 .x1 off,.ldr .w .x10 .x1 (1024+off),.vop (.dup .s4 .v20 .x9),.vop (.dup .s4 .v21 .x10)]
def mul (d : VReg) : List Instr :=
 [.vop (.sqdmulh .v19 d .v21),.vop (.mul d d .v20),.vop (.mls d .v19 .v31)]
def butterfly (a b : VReg) : List Instr :=
 [.vop (.sub .s4 .v18 a b),.vop (.add .s4 a a b),.vop (.mov b .v18)] ++ mul b
def packed (a b : VReg) (len : Nat) : List Instr :=
 let perm := if len=1 then VPermOp.uzp1 else .trn1
 let perm2 := if len=1 then VPermOp.uzp2 else .trn2
 let shape := if len=1 then VArr.s4 else .d2
 [.vop (.perm perm shape .v16 a b),.vop (.perm perm2 shape .v17 a b)] ++ [.vop (.sub .s4 .v18 .v16 .v17),.vop (.add .s4 .v16 .v16 .v17)] ++ mul .v18 ++
 (if len=1 then [.vop (.perm .zip1 .s4 a .v16 .v18),.vop (.perm .zip2 .s4 b .v16 .v18)]
 else [.vop (.perm .trn1 .d2 a .v16 .v18),.vop (.perm .trn2 .d2 b .v16 .v18)])
structure CS where
 code : List Instr := []
 regs : List VReg := [.v0,.v1,.v2,.v3,.v4,.v5,.v6,.v7]
 free : List VReg := [.v24,.v25,.v26,.v27]
def qt : Nat → VReg | 0 => .v16 | 1 => .v17 | 2 => .v18 | _ => .v19
def batch (st : CS) (pairs : List (Nat × Nat)) : CS :=
 let ds := (List.range pairs.length).flatMap fun j =>
  let (ai,bi) := pairs[j]!
  [.vop (.sub .s4 st.free[j]! st.regs[ai]! st.regs[bi]!),.vop (.add .s4 st.regs[ai]! st.regs[ai]! st.regs[bi]!)]
 let qs := (List.range pairs.length).map fun j => Instr.vop (.sqdmulh (qt j) st.free[j]! .v21)
 let ms := (List.range pairs.length).map fun j => Instr.vop (.mul st.free[j]! st.free[j]! .v20)
 let rs := (List.range pairs.length).map fun j => Instr.vop (.mls st.free[j]! (qt j) .v31)
 let regs := (List.range pairs.length).foldl (fun r j => r.set pairs[j]!.2 st.free[j]!) st.regs
 let free := (List.range pairs.length).foldl (fun r j => r.set j st.regs[pairs[j]!.2]!) st.free
 ⟨st.code++ds++qs++ms++rs,regs,free⟩
def rootAt (base : Reg) (off len : Nat) : List Instr :=
 let start := if len=1 then 0 else if len=2 then 128 else if len=4 then 256 else if len=8 then 384 else 448
 let j := if len=1 then off/16 else if len=2 then off/8 else off/4
 [.ldrq .v20 .x1 (start+32*j),.ldrq .v21 .x1 (start+32*j+16)]

def product (n j : Nat) : List Instr :=
 ((List.range n).flatMap fun k =>
  [.ldrq .v16 .x13 (1024*k+16*j),.ldrq .v17 .x14 (1024*k+16*j)] ++
  (if k=0 then [.vop (.umull false .v18 .v16 .v17),.vop (.umull true .v19 .v16 .v17)]
   else [.vop (.umlal false .v18 .v16 .v17),.vop (.umlal true .v19 .v16 .v17)])) ++
 [.vop (.perm .uzp1 .s4 .v20 .v18 .v19),.vop (.mul .v20 .v20 .v30),
  .vop (.umlal false .v18 .v20 .v31),.vop (.umlal true .v19 .v20 .v31),
  .vop (.perm .uzp2 .s4 (vr j) .v18 .v19),.vop (.sub .s4 (vr j) (vr j) .v31)]

def firstBlock (n : Nat) : List Instr :=
 let ld := (List.range 8).flatMap (product n)
 let packedCode := [1,2].flatMap (fun len => (List.range 4).flatMap (fun j => rootAt (if len=1 then .x3 else .x4) (16*j/len) len ++ packed (vr (2*j)) (vr (2*j+1)) len))
 let st : CS := {code := ld++packedCode}
 let st := [4,8,16].foldl (fun st len => (List.range (16/len)).foldl (fun st b =>
   batch {st with code := st.code++rootAt (if len=4 then .x5 else if len=8 then .x6 else .x7) (4*b) len}
    ((List.range (len/4)).map (fun j => (b*len/2+j,b*len/2+j+len/4)))) st) st
 st.code ++ (List.range 8).map (fun j => Instr.strq st.regs[j]! .x0 (16*j)) ++
 [.addImm .x .x13 .x13 128,.addImm .x .x14 .x14 128,.addImm .x .x0 .x0 128,.addImm .x .x1 .x1 480,.subImm .x .x11 .x11 1]
def finalRoot (idx : Nat) : List Instr :=
 let i := 7-idx
 [.vop (.dupE .s4 .v20 (if i<4 then .v22 else .v23) (i%4)),
  .vop (.dupE .s4 .v21 (if i<4 then .v28 else .v29) (i%4))]

def canon (d : VReg) : List Instr :=
 [.vop (.shift .sshr .s4 .v19 d 31),.vop (.logic .and .v19 .v19 .v31),.vop (.add .s4 d d .v19),
 .vop (.sub .s4 .v19 d .v31),.vop (.umin d d .v19)]
def finalBody : List Instr :=
 let st : CS := {code := (List.range 8).map (fun j => Instr.ldrq (vr j) .x2 (128*j))}
 let st := [1,2].foldl (fun st dist => (List.range (4/dist)).foldl (fun st b =>
   batch {st with code := st.code++finalRoot (8/dist-1-b)}
    ((List.range dist).map (fun j => (2*b*dist+j,2*b*dist+j+dist)))) st) st
 let st := batch {st with code := st.code ++ [.vop (.dupE .s4 .v20 .v30 2),.vop (.dupE .s4 .v21 .v30 3)]}
   ((List.range 4).map fun j => (j,j+4))
 st.code ++ [.vop (.dupE .s4 .v20 .v30 0),.vop (.dupE .s4 .v21 .v30 1)] ++
 ((List.range 4).map fun j => Instr.vop (.sqdmulh (qt j) st.regs[j]! .v21)) ++
 ((List.range 4).map fun j => Instr.vop (.mul st.regs[j]! st.regs[j]! .v20)) ++
 ((List.range 4).map fun j => Instr.vop (.mls st.regs[j]! (qt j) .v31)) ++
 ([0,4] : List Nat).flatMap (fun first =>
  let js := List.range 4
  (js.map fun j => Instr.vop (.shift .sshr .s4 (qt j) st.regs[first+j]! 31)) ++
  (js.map fun j => Instr.vop (.logic .and (qt j) (qt j) .v31)) ++
  (js.map fun j => Instr.vop (.add .s4 st.regs[first+j]! st.regs[first+j]! (qt j))) ++
  (js.map fun j => Instr.vop (.sub .s4 (qt j) st.regs[first+j]! .v31)) ++
  (js.map fun j => Instr.vop (.umin st.regs[first+j]! st.regs[first+j]! (qt j))) ++
  (js.map fun j => Instr.strq st.regs[first+j]! .x2 (128*(first+j)))) ++
 [.addImm .x .x2 .x2 16,.subImm .x .x12 .x12 1]

def core (n : Nat) : Prog isa :=
 .seq (.block (movW .x10 4236238847 ++ [.vop (.dup .s4 .v30 .x10)] ++ movW .x9 8380417 ++ [.vop (.dup .s4 .v31 .x9),mov .x3 .x1,
  .addImm .x .x4 .x1 512,.addImm .x .x5 .x1 768,.addImm .x .x6 .x1 896,.addImm .x .x7 .x1 960,.movz .x .x11 8 0])) <|
 .seq (.loop (.block (firstBlock n)) (.nonzero .x .x11)) <|
 .seq (.block ([.subImm .x .x0 .x0 1024,mov .x2 .x0,.movz .x .x12 8 0,
  .ldrq .v22 .x1 0,.ldrq .v23 .x1 16,.ldrq .v28 .x1 32,.ldrq .v29 .x1 48] ++
  cv .v30 [16382,bar 16382,(z 1*16382)%8380417,bar ((z 1*16382)%8380417)]))
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
 let last := (List.range 8).map fun j => CombInvImmediate.z (7-j)
 first ++ last ++ last.map CombInvImmediate.bar
def expandedWords : List (BitVec 64) :=
 (List.range (expandedVals.length/2)).map fun j => BitVec.ofNat 64 (expandedVals[2*j]!+2^32*expandedVals[2*j+1]!)
-- ABI out=x0, contiguous n-polynomial A=x1,B=x2,scratch=x3 unused.
def staticCode (n : Nat) : Prog isa := .seq (.block [mov .x13 .x1,mov .x14 .x2,.adrSym .x1 "VG_MLDSA_INV_FOLDED"]) (CombInvImmediate.core n)
end RootDotInv
namespace RootMul
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith
open VG.Impl.MlKem.AArch64 (mov)
namespace CombInvImmediate
def vr : Nat → VReg | 0 => .v0 | 1 => .v1 | 2 => .v2 | 3 => .v3 | 4 => .v4 | 5 => .v5 | 6 => .v6 | _ => .v7
def z (i : Nat) : Nat := (8380417-1753^Spec.MlDsa.bitRev8 i%8380417)%8380417
def bar (x : Nat) : Nat := x*2^31/8380417
def setup : Prog isa := .block <| (List.range 256).flatMap fun j =>
 movW .x9 (z (255-j)) ++ [.str .w .x9 .x1 (4*j)] ++
 movW .x9 (bar (z (255-j))) ++ [.str .w .x9 .x1 (1024+4*j)]
def cv (r : VReg) (xs : List Nat) : List Instr :=
 movW .x9 xs[0]! ++ [.vop (.dup .s4 r .x9)] ++
 (List.range 3).flatMap (fun j => if xs[j+1]! = xs[0]! then [] else movW .x9 xs[j+1]! ++ [.vop (.ins .s4 r (j+1) .x9)])
def root (idx len : Nat) : List Instr :=
 let off := 4*(255-idx)
 if len=1 then [.ldrq .v20 .x1 off,.ldrq .v21 .x1 (1024+off)]
 else if len=2 then [.ldr .x .x9 .x1 off,.ldr .x .x10 .x1 (1024+off),
 .vop (.dup .d2 .v20 .x9),.vop (.dup .d2 .v21 .x10),
 .vop (.perm .zip1 .s4 .v20 .v20 .v20),.vop (.perm .zip1 .s4 .v21 .v21 .v21)]
 else [.ldr .w .x9 .x1 off,.ldr .w .x10 .x1 (1024+off),.vop (.dup .s4 .v20 .x9),.vop (.dup .s4 .v21 .x10)]
def mul (d : VReg) : List Instr :=
 [.vop (.sqdmulh .v19 d .v21),.vop (.mul d d .v20),.vop (.mls d .v19 .v31)]
def butterfly (a b : VReg) : List Instr :=
 [.vop (.sub .s4 .v18 a b),.vop (.add .s4 a a b),.vop (.mov b .v18)] ++ mul b
def packed (a b : VReg) (len : Nat) : List Instr :=
 let perm := if len=1 then VPermOp.uzp1 else .trn1
 let perm2 := if len=1 then VPermOp.uzp2 else .trn2
 let shape := if len=1 then VArr.s4 else .d2
 [.vop (.perm perm shape .v16 a b),.vop (.perm perm2 shape .v17 a b)] ++ [.vop (.sub .s4 .v18 .v16 .v17),.vop (.add .s4 .v16 .v16 .v17)] ++ mul .v18 ++
 (if len=1 then [.vop (.perm .zip1 .s4 a .v16 .v18),.vop (.perm .zip2 .s4 b .v16 .v18)]
 else [.vop (.perm .trn1 .d2 a .v16 .v18),.vop (.perm .trn2 .d2 b .v16 .v18)])
structure CS where
 code : List Instr := []
 regs : List VReg := [.v0,.v1,.v2,.v3,.v4,.v5,.v6,.v7]
 free : List VReg := [.v24,.v25,.v26,.v27]
def qt : Nat → VReg | 0 => .v16 | 1 => .v17 | 2 => .v18 | _ => .v19
def batch (st : CS) (pairs : List (Nat × Nat)) : CS :=
 let ds := (List.range pairs.length).flatMap fun j =>
  let (ai,bi) := pairs[j]!
  [.vop (.sub .s4 st.free[j]! st.regs[ai]! st.regs[bi]!),.vop (.add .s4 st.regs[ai]! st.regs[ai]! st.regs[bi]!)]
 let qs := (List.range pairs.length).map fun j => Instr.vop (.sqdmulh (qt j) st.free[j]! .v21)
 let ms := (List.range pairs.length).map fun j => Instr.vop (.mul st.free[j]! st.free[j]! .v20)
 let rs := (List.range pairs.length).map fun j => Instr.vop (.mls st.free[j]! (qt j) .v31)
 let regs := (List.range pairs.length).foldl (fun r j => r.set pairs[j]!.2 st.free[j]!) st.regs
 let free := (List.range pairs.length).foldl (fun r j => r.set j st.regs[pairs[j]!.2]!) st.free
 ⟨st.code++ds++qs++ms++rs,regs,free⟩
def rootAt (base : Reg) (off len : Nat) : List Instr :=
 let start := if len=1 then 0 else if len=2 then 128 else if len=4 then 256 else if len=8 then 384 else 448
 let j := if len=1 then off/16 else if len=2 then off/8 else off/4
 [.ldrq .v20 .x1 (start+32*j),.ldrq .v21 .x1 (start+32*j+16)]

def product (j : Nat) : List Instr :=
 [.ldrq .v16 .x13 (16*j),.ldrq .v17 .x14 (16*j),
  .vop (.umull false .v18 .v16 .v17),.vop (.umull true .v19 .v16 .v17),
  .vop (.perm .uzp1 .s4 .v20 .v18 .v19),.vop (.mul .v20 .v20 .v30),
  .vop (.umlal false .v18 .v20 .v31),.vop (.umlal true .v19 .v20 .v31),
  .vop (.perm .uzp2 .s4 (vr j) .v18 .v19),.vop (.sub .s4 (vr j) (vr j) .v31)]
def firstBlock : List Instr :=
 let ld := (List.range 8).flatMap product
 let packedCode := [1,2].flatMap (fun len => (List.range 4).flatMap (fun j => rootAt (if len=1 then .x3 else .x4) (16*j/len) len ++ packed (vr (2*j)) (vr (2*j+1)) len))
 let st : CS := {code := ld++packedCode}
 let st := [4,8,16].foldl (fun st len => (List.range (16/len)).foldl (fun st b =>
   batch {st with code := st.code++rootAt (if len=4 then .x5 else if len=8 then .x6 else .x7) (4*b) len}
    ((List.range (len/4)).map (fun j => (b*len/2+j,b*len/2+j+len/4)))) st) st
 st.code ++ (List.range 8).map (fun j => Instr.strq st.regs[j]! .x0 (16*j)) ++
 [.addImm .x .x13 .x13 128,.addImm .x .x14 .x14 128,.addImm .x .x0 .x0 128,.addImm .x .x1 .x1 480,.subImm .x .x11 .x11 1]
def finalRoot (idx : Nat) : List Instr :=
 let i := 7-idx
 [.vop (.dupE .s4 .v20 (if i<4 then .v22 else .v23) (i%4)),
  .vop (.dupE .s4 .v21 (if i<4 then .v28 else .v29) (i%4))]

def canon (d : VReg) : List Instr :=
 [.vop (.shift .sshr .s4 .v19 d 31),.vop (.logic .and .v19 .v19 .v31),.vop (.add .s4 d d .v19),
 .vop (.sub .s4 .v19 d .v31),.vop (.umin d d .v19)]
def finalBody : List Instr :=
 let st : CS := {code := (List.range 8).map (fun j => Instr.ldrq (vr j) .x2 (128*j))}
 let st := [1,2].foldl (fun st dist => (List.range (4/dist)).foldl (fun st b =>
   batch {st with code := st.code++finalRoot (8/dist-1-b)}
    ((List.range dist).map (fun j => (2*b*dist+j,2*b*dist+j+dist)))) st) st
 let st := batch {st with code := st.code ++ [.vop (.dupE .s4 .v20 .v30 2),.vop (.dupE .s4 .v21 .v30 3)]}
   ((List.range 4).map fun j => (j,j+4))
 st.code ++ [.vop (.dupE .s4 .v20 .v30 0),.vop (.dupE .s4 .v21 .v30 1)] ++
 ((List.range 4).map fun j => Instr.vop (.sqdmulh (qt j) st.regs[j]! .v21)) ++
 ((List.range 4).map fun j => Instr.vop (.mul st.regs[j]! st.regs[j]! .v20)) ++
 ((List.range 4).map fun j => Instr.vop (.mls st.regs[j]! (qt j) .v31)) ++
 ((List.range 8).map fun j => Instr.strq st.regs[j]! .x2 (128*j)) ++
 [.addImm .x .x2 .x2 16,.subImm .x .x12 .x12 1]

def core : Prog isa :=
 .seq (.block (movW .x10 4236238847 ++ [.vop (.dup .s4 .v30 .x10)] ++ movW .x9 8380417 ++ [.vop (.dup .s4 .v31 .x9),mov .x3 .x1,
  .addImm .x .x4 .x1 512,.addImm .x .x5 .x1 768,.addImm .x .x6 .x1 896,.addImm .x .x7 .x1 960,.movz .x .x11 8 0])) <|
 .seq (.loop (.block firstBlock) (.nonzero .x .x11)) <|
 .seq (.block ([.subImm .x .x0 .x0 1024,mov .x2 .x0,.movz .x .x12 8 0,
  .ldrq .v22 .x1 0,.ldrq .v23 .x1 16,.ldrq .v28 .x1 32,.ldrq .v29 .x1 48] ++
  cv .v30 [16382,bar 16382,(z 1*16382)%8380417,bar ((z 1*16382)%8380417)]))
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
 let last := (List.range 8).map fun j => CombInvImmediate.z (7-j)
 first ++ last ++ last.map CombInvImmediate.bar
def expandedWords : List (BitVec 64) :=
 (List.range (expandedVals.length/2)).map fun j => BitVec.ofNat 64 (expandedVals[2*j]!+2^32*expandedVals[2*j+1]!)
-- ABI out=x0, a=x1, b=x2, scratch=x3 (unused), all256coefficients.
def staticCode : Prog isa := .seq (.block [mov .x13 .x1,mov .x14 .x2,.adrSym .x1 "VG_MLDSA_INV_FOLDED"]) CombInvImmediate.core
end RootMul
namespace RootOut
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith
open VG.Impl.MlDsa.AArch64.Arith.Neon

namespace WindowFusedNtt
open VG.AArch64
open VG.Impl.MlKem.AArch64 (mov)
open VG.Impl.MlDsa.AArch64.Arith (storeTab movW)


def bbar : List Instr :=
 [.vop (.umull false .v2 .v18 .v20),.vop (.umull true .v3 .v18 .v20),
 .vop (.shift .ushr .d2 .v2 .v2 23),.vop (.shift .ushr .d2 .v3 .v3 23),
 .vop (.perm .uzp1 .s4 .v19 .v2 .v3)]
def fastMul (d : VReg) : List Instr :=
 [.vop (.sqdmulh .v4 d .v19),.vop (.mul d d .v18),.vop (.mls d .v4 .v16)]
def fastConsts : List Instr :=
 Neon.consts ++ movW .x9 2149582593 ++ [.vop (.dup .s4 .v20 .x9)]
def canon (d : VReg) : List Instr :=
 [.vop (.shift .sshr .s4 .v4 d 23),.vop (.mls d .v4 .v16),.vop (.add .s4 d d .v16)]

def bfly : List Instr := fastMul .v1 ++
 [.vop (.sub .s4 .v5 .v0 .v1),.vop (.add .s4 .v0 .v0 .v1)]
def bflyInv : List Instr :=
 [.vop (.sub .s4 .v5 .v0 .v1),.vop (.add .s4 .v0 .v0 .v1)] ++ fastMul .v5

def zetaTab (m : Nat) : Nat := 1753 ^ Spec.MlDsa.bitRev8 m % 8380417

def negZetaTab (m : Nat) : Nat :=
  ((8380417 - 1753 ^ Spec.MlDsa.bitRev8 m % 8380417) % 8380417) % 8380417

def stepZ (up : Bool) : Instr :=
  if up then .addImm .x .x3 .x3 4 else .subImm .x .x3 .x3 4

/-- Arrange two or four block zetas in butterfly lane order. -/
def zetaPerms (len : Nat) (up : Bool) : List Instr :=
  (if len = 2 then [.vop (.perm .zip1 .s4 .v18 .v18 .v18)] else []) ++
    if up then [] else
      (if len = 1 then [.vop (.rev .rev64s .v18 .v18)] else []) ++ [.vop (.ext .v18 .v18 .v18 8)]

def packedZetas (len : Nat) (up : Bool) : List Instr :=
  (if up then [] else [.subImm .x .x3 .x3 (4*(4/len-1))]) ++
  [.ldrq .v18 .x3 0] ++ zetaPerms len up ++
  [if up then .addImm .x .x3 .x3 (16/len) else .subImm .x .x3 .x3 4]

/-- Load one zeta per block, replicated across its lanes. -/
def rawZetas (len : Nat) (up : Bool) : List Instr :=
  if len = 2 then packedZetas len up
  else if len = 1 then packedZetas len up
  else [.ldr .w .x6 .x3 0, stepZ up, .vop (.dup .s4 .v18 .x6)]

def zetas (len : Nat) (up : Bool) : List Instr := rawZetas len up ++ bbar

def body (bf : List Instr) (len : Nat) : List Instr :=
  [.ldrq .v0 .x2 0, .ldrq .v1 .x2 (4*len)] ++ bf ++
  [.strq .v0 .x2 0, .strq .v5 .x2 (4*len), .addImm .x .x2 .x2 16, .subImm .x .x5 .x5 1]

def block (bf : List Instr) (len : Nat) (up : Bool) : Prog isa :=
  .seq (.block (zetas len up ++ [.movz .x .x5 (BitVec.ofNat 16 (len/4)) 0]))
    (.seq (.loop (.block (body bf len)) (.nonzero .x .x5))
      (.block [.addImm .x .x2 .x2 (4*len), .subImm .x .x4 .x4 1]))

def gather (len : Nat) : List Instr :=
  if len = 2 then
    [.vop (.perm .trn1 .d2 .v0 .v6 .v7), .vop (.perm .trn2 .d2 .v1 .v6 .v7)]
  else [.vop (.perm .uzp1 .s4 .v0 .v6 .v7), .vop (.perm .uzp2 .s4 .v1 .v6 .v7)]

def scatter (len : Nat) : List Instr :=
  if len = 2 then
    [.vop (.perm .trn1 .d2 .v6 .v0 .v5), .vop (.perm .trn2 .d2 .v7 .v0 .v5)]
  else [.vop (.perm .zip1 .s4 .v6 .v0 .v5), .vop (.perm .zip2 .s4 .v7 .v0 .v5)]

def packedBody (bf : List Instr) (len : Nat) (up : Bool) : List Instr :=
  [.ldrq .v6 .x2 0, .ldrq .v7 .x2 16] ++ zetas len up ++ gather len ++ bf ++ scatter len ++
  [.strq .v6 .x2 0, .strq .v7 .x2 16, .addImm .x .x2 .x2 32, .subImm .x .x5 .x5 1]

/-- The zeta range of a layer is known statically. -/
def layer (bf : List Instr) (len : Nat) (up : Bool) : Prog isa :=
  .seq (.block [mov .x2 .x0, .addImm .x .x3 .x1 (4*(if up then 128/len else 256/len-1))])
    (if len < 4 then
      .seq (.block [.movz .x .x5 32 0])
        (.loop (.block (packedBody bf len up)) (.nonzero .x .x5))
     else .seq (.block [.movz .x .x4 (BitVec.ofNat 16 (128/len)) 0])
       (.loop (block bf len up) (.nonzero .x .x4)))

def layers (bf : List Instr) (up : Bool) : List Nat → Prog isa
  | [] => .block []
  | len :: lens => .seq (layer bf len up) (layers bf up lens)

def pro (tab : Nat → Nat) : List Instr := storeTab tab 256 .x1 ++ fastConsts

def finish : Prog isa :=
 .seq (.block [mov .x2 .x0,.movz .x .x5 64 0])
 (.loop (.block ([.ldrq .v0 .x2 0] ++ canon .v0 ++
 [.strq .v0 .x2 0,.addImm .x .x2 .x2 16,.subImm .x .x5 .x5 1])) (.nonzero .x .x5))
def fusedForwardBody : List Instr :=
 [.ldrq .v6 .x2 0,.ldrq .v7 .x2 16] ++
 zetas 2 true ++ gather 2 ++ bfly ++ scatter 2 ++
 [.ldrq .v18 .x7 0,.addImm .x .x7 .x7 16] ++ bbar ++
 gather 1 ++ bfly ++ scatter 1 ++ canon .v6 ++ canon .v7 ++
 [.strq .v6 .x2 0,.strq .v7 .x2 16,.addImm .x .x2 .x2 32,.subImm .x .x5 .x5 1]
def fusedForward : Prog isa :=
 .seq (.block [mov .x2 .x0,.addImm .x .x3 .x1 256,.addImm .x .x7 .x1 512,.movz .x .x5 32 0])
 (.loop (.block fusedForwardBody) (.nonzero .x .x5))
def ntt : Prog isa := .seq (.block (pro zetaTab))
 (.seq (layers bfly true [128,64,32,16,8,4]) fusedForward)

def swapZ : List Instr := [mov .x6 .x3,mov .x3 .x7,mov .x7 .x6]
def fusedInverseBody : List Instr :=
 [.ldrq .v6 .x2 0,.ldrq .v7 .x2 16] ++
 zetas 1 false ++ gather 1 ++ bflyInv ++ scatter 1 ++
 swapZ ++ zetas 2 false ++ swapZ ++ gather 2 ++ bflyInv ++ scatter 2 ++
 [.strq .v6 .x2 0,.strq .v7 .x2 16,.addImm .x .x2 .x2 32,.subImm .x .x5 .x5 1]
def fusedInverse : Prog isa :=
 .seq (.block [mov .x2 .x0,.addImm .x .x3 .x1 1020,.addImm .x .x7 .x1 508,.movz .x .x5 32 0])
 (.loop (.block fusedInverseBody) (.nonzero .x .x5))

def scaleBody : List Instr :=
  [.ldrq .v0 .x2 0] ++ fastMul .v0 ++ canon .v0 ++
    [.strq .v0 .x2 0, .addImm .x .x2 .x2 16, .subImm .x .x5 .x5 1]

def scale : Prog isa :=
  .seq (.block (movW .x6 8347681 ++
    [.vop (.dup .s4 .v18 .x6), mov .x2 .x0, .movz .x .x5 64 0] ++ bbar))
    (.loop (.block scaleBody) (.nonzero .x .x5))

def nttInv : Prog isa := .seq (.block (pro negZetaTab))
  (.seq fusedInverse (.seq (layers bflyInv false [4,8,16,32,64,128]) scale))

def constVector (d : VReg) (xs : List Nat) : List Instr :=
 movW .x6 xs[0]! ++ [.vop (.dup .s4 d .x6)] ++
 ((List.range 3).flatMap fun i =>
  if xs[i+1]! = xs[0]! then [] else movW .x6 xs[i+1]! ++ [.vop (.ins .s4 d (i+1) .x6)])
def immediateZ (xs : List Nat) : List Instr :=
 constVector .v18 xs ++ constVector .v19 (xs.map fun z => z*2149582593/2^23)
def directBlock (up : Bool) (len index : Nat) : Prog isa :=
 let z := if up then zetaTab index else negZetaTab index
 .seq (.block (immediateZ [z,z,z,z] ++ [.movz .x .x5 (BitVec.ofNat 16 (len/4)) 0]))
 (.seq (.loop (.block (body (if up then bfly else bflyInv) len)) (.nonzero .x .x5))
 (.block [.addImm .x .x2 .x2 (4*len)]))
def directLayer (up : Bool) (len : Nat) : Prog isa :=
 .seq (.block [mov .x2 .x0])
 ((List.range (128/len)).foldr (fun g tail =>
  .seq (directBlock up len (if up then 128/len+g else 256/len-1-g)) tail) (.block []))
def directFusedBody (up : Bool) (i : Nat) : List Instr :=
 let z2 := if up then [zetaTab (64+2*i),zetaTab (64+2*i),zetaTab (65+2*i),zetaTab (65+2*i)]
   else [negZetaTab (127-2*i),negZetaTab (127-2*i),negZetaTab (126-2*i),negZetaTab (126-2*i)]
 let z1 := (List.range 4).map fun j => if up then zetaTab (128+4*i+j) else negZetaTab (255-4*i-j)
 [.ldrq .v6 .x2 0,.ldrq .v7 .x2 16] ++
 (if up then immediateZ z2 ++ gather 2 ++ bfly ++ scatter 2 ++
    immediateZ z1 ++ gather 1 ++ bfly ++ scatter 1 ++ canon .v6 ++ canon .v7
 else immediateZ z1 ++ gather 1 ++ bflyInv ++ scatter 1 ++
    immediateZ z2 ++ gather 2 ++ bflyInv ++ scatter 2) ++
 [.strq .v6 .x2 0,.strq .v7 .x2 16,.addImm .x .x2 .x2 32]
def directFused (up : Bool) : Prog isa :=
 .block ([mov .x2 .x0] ++ (List.range 32).flatMap (directFusedBody up))
def directNtt : Prog isa := .seq (.block fastConsts)
 (([128,64,32,16,8,4] : List Nat).foldr (fun len rest => .seq (directLayer true len) rest) (directFused true))
def directInv : Prog isa := .seq (.block fastConsts) <| .seq (directFused false)
 (([4,8,16,32,64,128] : List Nat).foldr (fun len rest => .seq (directLayer false len) rest) scale)

def dataRegs : List VReg := [.v0,.v1,.v5,.v6,.v7,.v21,.v22,.v23]
def lazyPair (a b : VReg) (up : Bool) : List Instr :=
 if up then fastMul b ++
  [.vop (.sub .s4 .v24 a b),.vop (.add .s4 a a b),.vop (.mov b .v24)]
 else [.vop (.sub .s4 .v24 a b),.vop (.add .s4 a a b),.vop (.mov b .v24)] ++ fastMul b

def fusedOuterOps (up : Bool) : List Instr :=
 ((if up then [4,2,1] else [1,2,4]) : List Nat).flatMap fun gap =>
  (List.range (4/gap)).flatMap fun group =>
   let z := if up then zetaTab (4/gap+group) else negZetaTab (8/gap-1-group)
   immediateZ [z,z,z,z] ++ (List.range gap).flatMap fun j =>
    lazyPair dataRegs[2*gap*group+j]! dataRegs[2*gap*group+j+gap]! up

def fusedOuter (up : Bool) : Prog isa :=
 .seq (.block [mov .x2 .x0,.movz .x .x5 8 0]) <|
 .loop (.block (
  (dataRegs.zipIdx.flatMap fun (r,i) => [.ldrq r .x2 (128*i)]) ++ fusedOuterOps up ++
  (if up then [] else immediateZ [8347681,8347681,8347681,8347681] ++
    dataRegs.flatMap fun r => fastMul r ++ canon r) ++
  (dataRegs.zipIdx.flatMap fun (r,i) => [.strq r .x2 (128*i)]) ++
  [.addImm .x .x2 .x2 16,.subImm .x .x5 .x5 1])) (.nonzero .x .x5)

def fused3Ntt : Prog isa := .seq (.block fastConsts) <| .seq (fusedOuter true)
 (([16,8,4] : List Nat).foldr (fun len rest => .seq (directLayer true len) rest) (directFused true))
def fused3Inv : Prog isa := .seq (.block fastConsts) <| .seq (directFused false)
 (([4,8,16] : List Nat).foldr (fun len rest => .seq (directLayer false len) rest) (fusedOuter false))


-- Eight packed (root, reciprocal) pairs for the first three layers, initialized once.
def rootRegs : List VReg := [.v25,.v26,.v27,.v28]
def hoistedInit : List Instr := (List.range 4).map
 (fun i => .ldrq rootRegs[i]! .x1 (3840+16*i))
def hoistedRoot (i : Nat) : List Instr :=
 [.vop (.dupE .s4 .v18 rootRegs[(i-1)/2]! (2*((i-1)%2))),
  .vop (.dupE .s4 .v19 rootRegs[(i-1)/2]! (2*((i-1)%2)+1))]
def outerHoistedOps : List Instr :=
 ([4,2,1] : List Nat).flatMap fun gap =>
  (List.range (4/gap)).flatMap fun group =>
   hoistedRoot (4/gap+group) ++ (List.range gap).flatMap fun j =>
    lazyPair dataRegs[2*gap*group+j]! dataRegs[2*gap*group+j+gap]! true

def outerHoisted : Prog isa :=
 .seq (.block ([mov .x2 .x0,.movz .x .x5 8 0] ++ hoistedInit)) <|
 .loop (.block (
  (dataRegs.zipIdx.flatMap fun (r,i) => [.ldrq r .x2 (128*i)]) ++ outerHoistedOps ++
  (dataRegs.zipIdx.flatMap fun (r,i) => [.strq r .x2 (128*i)]) ++
  [.addImm .x .x2 .x2 16,.subImm .x .x5 .x5 1])) (.nonzero .x .x5)

-- Explicit internal table ABI: x1 has 2048 initialized bytes, one 64-bit pair per index.
def tableSetup : Prog isa := .block <| (List.range 256).flatMap fun i =>
 let z := zetaTab i
 VG.Impl.MlKem.AArch64.movImm .x6 (BitVec.ofNat 64 (z + (z*2149582593/2^23)*2^32)) ++ [.str .x .x6 .x1 (8*i)]
def tableRoot (i : Nat) : List Instr :=
 [.ldr .x .x6 .x1 (8*i),.vop (.dup .d2 .v19 .x6),
  .vop (.dupE .s4 .v18 .v19 0),.vop (.dupE .s4 .v19 .v19 1)]
def root (table : Bool) (i : Nat) : List Instr :=
 if table then tableRoot i else let z := zetaTab i; immediateZ [z,z,z,z]
def packedRoot (table : Bool) (len i : Nat) : List Instr :=
 if table then
  if len=2 then [.ldrq .v19 .x1 (8*i),.vop (.perm .trn1 .s4 .v18 .v19 .v19),.vop (.perm .trn2 .s4 .v19 .v19 .v19)]
  else [.ldrq .v2 .x1 (8*i),.ldrq .v3 .x1 (8*i+16),
   .vop (.perm .uzp1 .s4 .v18 .v2 .v3),.vop (.perm .uzp2 .s4 .v19 .v2 .v3)]
 else let zs := if len=2 then [zetaTab i,zetaTab i,zetaTab (i+1),zetaTab (i+1)]
   else (List.range 4).map fun j => zetaTab (i+j)
      immediateZ zs
-- Temporary vectors25/26/24; all data stay in their eight assigned registers.
def innerPair (a b : VReg) (len : Nat) : List Instr :=
 [ .vop (.perm (if len=2 then .trn1 else .uzp1) (if len=2 then .d2 else .s4) .v25 a b),
   .vop (.perm (if len=2 then .trn2 else .uzp2) (if len=2 then .d2 else .s4) .v26 a b)] ++ fastMul .v26 ++
 [.vop (.sub .s4 .v24 .v25 .v26),.vop (.add .s4 .v25 .v25 .v26),
  .vop (.perm (if len=2 then .trn1 else .zip1) (if len=2 then .d2 else .s4) a .v25 .v24),
  .vop (.perm (if len=2 then .trn2 else .zip2) (if len=2 then .d2 else .s4) b .v25 .v24)]
def innerFive (table : Bool) (block : Nat) : List Instr :=
 (dataRegs.zipIdx.flatMap fun (r,i) => [.ldrq r .x2 (16*i)]) ++
 (([4,2,1] : List Nat).flatMap fun gap =>
   (List.range (4/gap)).flatMap fun g => root table (32/gap + block*(4/gap)+g) ++
    (List.range gap).flatMap fun j => lazyPair dataRegs[2*gap*g+j]! dataRegs[2*gap*g+j+gap]! true) ++
 ((List.range 4).flatMap fun j =>
   packedRoot table 2 (64+8*block+2*j) ++ innerPair dataRegs[2*j]! dataRegs[2*j+1]! 2 ++
   packedRoot table 1 (128+16*block+4*j) ++ innerPair dataRegs[2*j]! dataRegs[2*j+1]! 1) ++
 (dataRegs.flatMap fun r => canon r) ++
 (dataRegs.zipIdx.flatMap fun (r,i) => [.strq r .x2 (16*i)]) ++ [.addImm .x .x2 .x2 128]
def finalFive (table : Bool) : Prog isa :=
 .block ([mov .x2 .x0] ++ (List.range 8).flatMap (innerFive table))
def fusedFive : Prog isa := .seq (.block fastConsts) (.seq outerHoisted (finalFive false))
def fusedFiveCore : Prog isa := .seq (.block fastConsts) (.seq outerHoisted (finalFive true))
-- Internal-only full wrapper: requires2048 scratch bytes, never replaces public1024 ABI directly.
def fusedFiveTable : Prog isa := .seq tableSetup fusedFiveCore
def fusedTwoCore : Prog isa := .seq (.block fastConsts)
 (.seq (layers bfly true [128,64,32,16,8,4]) fusedForward)
def rootOnlySetup : Prog isa := .block (storeTab zetaTab 256 .x1)
def rootAt (base : Reg) (i : Nat) : List Instr :=
 [.ldrq .v18 base (32*i),.ldrq .v19 base (32*i+16)]
def packedAt (base : Reg) (len i : Nat) : List Instr :=
 let j := if len=2 then i/2 else i/4
 [.ldrq .v18 base (32*j),.ldrq .v19 base (32*j+16)]
def innerFiveLoopBody : List Instr :=
 (dataRegs.zipIdx.flatMap fun (r,i) => [.ldrq r .x2 (16*i)]) ++
 (([4,2,1] : List Nat).flatMap fun gap =>
   (List.range (4/gap)).flatMap fun g => rootAt (if gap=4 then .x3 else if gap=2 then .x4 else .x5) g ++
    (List.range gap).flatMap fun j => lazyPair dataRegs[2*gap*g+j]! dataRegs[2*gap*g+j+gap]! true) ++
 ((List.range 4).flatMap fun j =>
   packedAt .x7 2 (2*j) ++ innerPair dataRegs[2*j]! dataRegs[2*j+1]! 2 ++
   packedAt .x8 1 (4*j) ++ innerPair dataRegs[2*j]! dataRegs[2*j+1]! 1) ++
 (dataRegs.flatMap fun r => canon r) ++
 (dataRegs.zipIdx.flatMap fun (r,i) => [.strq r .x2 (16*i)]) ++
 [.addImm .x .x2 .x2 128,.addImm .x .x3 .x3 8,.addImm .x .x4 .x4 16,
  .addImm .x .x5 .x5 32,.addImm .x .x7 .x7 64,.addImm .x .x8 .x8 128,.subImm .x .x10 .x10 1]
def finalFiveLoop : Prog isa :=
 .seq (.block [mov .x2 .x0,.addImm .x .x3 .x1 64,.addImm .x .x4 .x1 128,.addImm .x .x5 .x1 256,
  .addImm .x .x7 .x1 512,.addImm .x .x8 .x1 1024,.movz .x .x10 8 0])
 (.loop (.block innerFiveLoopBody) (.nonzero .x .x10))
def fusedFiveLoopCore : Prog isa := .seq (.block fastConsts) (.seq outerHoisted finalFiveLoop)
def fusedFiveLoopTable : Prog isa := .seq tableSetup fusedFiveLoopCore
structure Ren where
 code : List Instr := []
 data : List VReg := dataRegs
 free : VReg := .v24

def prodTemps : List VReg := [.v4,.v29,.v30,.v31]
def renGroup (r : Ren) (gap group : Nat) (roots : List Instr) : Ren :=
 let bs := (List.range gap).map fun j => r.data[2*gap*group+j+gap]!
 let ops := ((bs.zipIdx).map fun (b,i) => .vop (.sqdmulh prodTemps[i]! b .v19)) ++
  (bs.map fun b => .vop (.mul b b .v18)) ++
  ((bs.zipIdx).map fun (b,i) => .vop (.mls b prodTemps[i]! .v16))
 (List.range gap).foldl (fun st j =>
   let a := st.data[2*gap*group+j]!
   let b := st.data[2*gap*group+j+gap]!
   { code := st.code ++ [.vop (.sub .s4 st.free a b),.vop (.add .s4 a a b)]
     data := st.data.set (2*gap*group+j+gap) st.free
     free := b }) {r with code := r.code ++ roots ++ ops}
def renThree (outer table : Bool) (block : Nat) : Ren :=
 ([4,2,1] : List Nat).foldl (fun st gap =>
  (List.range (4/gap)).foldl (fun st g =>
   let rs := if outer then hoistedRoot (4/gap+g)
    else if table then rootAt (if gap=4 then .x3 else if gap=2 then .x4 else .x5) g
    else root false (32/gap+block*(4/gap)+g)
   renGroup st gap g rs) st) {}
def outerRenamed : Prog isa :=
 let r := renThree true false 0
 .seq (.block ([mov .x2 .x0,.movz .x .x5 8 0] ++ hoistedInit)) <|
 .loop (.block (
  (dataRegs.zipIdx.flatMap fun (v,i) => [.ldrq v .x11 (128*i)]) ++ r.code ++
  (r.data.zipIdx.flatMap fun (v,i) => [.strq v .x2 (128*i)]) ++
  [.addImm .x .x2 .x2 16,.addImm .x .x11 .x11 16,.subImm .x .x5 .x5 1])) (.nonzero .x .x5)
def renInnerPair (a b tmp : VReg) (len : Nat) : List Instr :=
 [ .vop (.perm (if len=2 then .trn1 else .uzp1) (if len=2 then .d2 else .s4) .v25 a b),
   .vop (.perm (if len=2 then .trn2 else .uzp2) (if len=2 then .d2 else .s4) .v26 a b)] ++ fastMul .v26 ++
 [.vop (.sub .s4 tmp .v25 .v26),.vop (.add .s4 .v25 .v25 .v26),
  .vop (.perm (if len=2 then .trn1 else .zip1) (if len=2 then .d2 else .s4) a .v25 tmp),
  .vop (.perm (if len=2 then .trn2 else .zip2) (if len=2 then .d2 else .s4) b .v25 tmp)]
def renFiveBody (table canonical : Bool) (block : Nat) : List Instr :=
 let r := renThree false table block
 (dataRegs.zipIdx.flatMap fun (v,i) => [.ldrq v .x2 (16*i)]) ++ r.code ++
 ((List.range 4).flatMap fun j =>
   (if table then packedAt .x7 2 (2*j) else packedRoot false 2 (64+8*block+2*j)) ++
    renInnerPair r.data[2*j]! r.data[2*j+1]! r.free 2 ++
   (if table then packedAt .x8 1 (4*j) else packedRoot false 1 (128+16*block+4*j)) ++
    renInnerPair r.data[2*j]! r.data[2*j+1]! r.free 1) ++
 (if canonical then r.data.flatMap fun v => canon v else []) ++
 (r.data.zipIdx.flatMap fun (v,i) => [.strq v .x2 (16*i)]) ++ [.addImm .x .x2 .x2 128]
def renFive (table canonical : Bool) : Prog isa :=
 if table then
  .seq (.block [mov .x2 .x0,mov .x3 .x1,.addImm .x .x4 .x1 32,.addImm .x .x5 .x1 96,
   .addImm .x .x7 .x1 224,.addImm .x .x8 .x1 352,.movz .x .x10 8 0])
  (.loop (.block (renFiveBody true canonical 0 ++ [.addImm .x .x3 .x3 480,.addImm .x .x4 .x4 480,
   .addImm .x .x5 .x5 480,.addImm .x .x7 .x7 480,.addImm .x .x8 .x8 480,.subImm .x .x10 .x10 1])) (.nonzero .x .x10))
 else .block ([mov .x2 .x0] ++ (List.range 8).flatMap (renFiveBody false canonical))
def renamedNtt (table canonical : Bool) : Prog isa :=
 .seq (.block fastConsts) (.seq outerRenamed (renFive table canonical))
end WindowFusedNtt

def expandedVals : List Nat :=
 let bar := fun z => z*2^31/8380417
 let first := (List.range 8).flatMap fun block =>
  ([16,8,4,2,1] : List Nat).flatMap fun len =>
   (List.range (if len<4 then 4 else 16/len)).flatMap fun g =>
    let idx := 128/len+32*block/(2*len)+(if len=2 then 2*g else if len=1 then 4*g else g)
    let zs := if len=1 then (List.range 4).map (fun j => WindowFusedNtt.zetaTab (idx+j))
     else if len=2 then [WindowFusedNtt.zetaTab idx,WindowFusedNtt.zetaTab idx,WindowFusedNtt.zetaTab (idx+1),WindowFusedNtt.zetaTab (idx+1)]
     else List.replicate 4 (WindowFusedNtt.zetaTab idx)
    zs++zs.map bar
 first ++ (List.range 8).flatMap (fun i => let z := WindowFusedNtt.zetaTab (i+1); [z,bar z])
def staticNttWords : List (BitVec 64) := (List.range (expandedVals.length/2)).map
 (fun i => BitVec.ofNat 64 (expandedVals[2*i]!+2^32*expandedVals[2*i+1]!))
def staticNtt : Prog isa := .seq (.block [.addImm .x .x11 .x1 0,.adrSym .x1 "VG_MLDSA_NTT_EXPANDED"])
 (WindowFusedNtt.renamedNtt true true)

end RootOut

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Call
private def rootNttOut (_P : VG.Impl.MlDsa.AArch64.Sign.Prims) (h f : Ptr) : Prog isa :=
 callAt "vg_mldsa_ntt_from" RootOut.staticNtt
 [(.x0,.ptr h),(.x1,.ptr f),(.x2,.ptr (.x28, VG.Impl.MlDsa.AArch64.Sign.oPS))]
namespace RootPair

open VG VG.AArch64
open VG.Impl.MlKem.AArch64 (mov)
open VG.Impl.MlDsa.AArch64.Sample
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
  (List.range 2).map (fun k => .str .x .x4 .x19 (counts+8*k))

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

def parse (_v : Nat) : Prog isa :=
 .seq (.block (vectorSetup++guard)) <|
 .seq (.ite (.zero .x .x16) (.block [])
   (.loop vectorBody (.nonzero .x .x16))) <|
 .seq (.block [.mul .x .x16 .x4 .x5]) <|
 .ite (.zero .x .x16) (.block []) ExpRej.wideMulLoop

def segment (v k off n : Nat) : Prog isa :=
 .seq (.block (setup k off n)) <| .seq (parse v) <|
 .block [.str .x .x4 .x19 (counts+8*k)]

def batch (v off n : Nat) : Prog isa :=
 .seq (segment v 0 off n) (segment v 1 off n)

def zeros : Prog isa := .block <| [.vop (.movi0 .v0)] ++
 (List.range 128).map (fun i => .strq .v0 .x21 (16*i))

def flags : List Instr := [.ldr .x .x27 .x19 counts] ++
 (List.range 1).flatMap (fun k => [.ldr .x .x6 .x19 (counts+8*(k+1)),
 .logic .orr .x .x27 .x27 .x6])

def rej4With (squeeze : Prog isa) (v : Nat) : Prog isa :=
 .seq (.block (Rej4.pro ++ Rej4.zeroStates ++ Rej4.absorbPair 0 ++ initCounts)) <|
 .seq (squeezeN squeeze 0 3) <| .seq zeros <| .seq (batch v 0 168) <|
 .seq (squeezeN squeeze 504 2) <| .seq (batch v 504 112) <|
 .seq (.block flags) <|
 .seq (.ite (.zero .x .x27) (.block [])
 (.seq (squeezeN squeeze 840 1) <| .seq (batch v 840 56) (.block flags))) <|
 .block ([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63]++Rej4.epi)
end ExpRejFiveParse



def rootRej2 : Prog isa := ExpRejFiveParse.rej4With (.seq (Impl.Sha3.AArch64.Neon.Pair.progWith true .x22 .x24 .x25) (.block Rej4.advance)) 0

end RootPair
open VG VG.AArch64
namespace CommitHash
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Impl.MlDsa.AArch64.Call
-- ABI: mu=x0 (64 bytes), w1=x1 (768/1024 bytes), out=x2 (32/48/64), scratch=x3(128).
def save : List Instr := (List.range 8).map (fun i => .strq (vreg (8+i)) .x3 (16*i))
def restore : List Instr := (List.range 8).map (fun i => .ldrq (vreg (8+i)) .x3 (16*i))
def first : List Instr :=
 (List.range 4).flatMap (fun i => [.ldrq (vreg (2*i)) .x0 (16*i),
 .vop (.ext (vreg (2*i+1)) (vreg (2*i)) (vreg (2*i)) 8)]) ++
 (List.range 4).flatMap (fun i => [.ldrq (vreg (8+2*i)) .x1 (16*i),
 .vop (.ext (vreg (9+2*i)) (vreg (8+2*i)) (vreg (8+2*i)) 8)]) ++
 [.ldr .x .x6 .x1 64,.vop (.dup .d2 .v16 .x6)] ++
 (List.range 8).map (fun i => .vop (.movi0 (vreg (17+i))))
def absorbPair (i : Nat) : List Instr := [.ldrq .v25 .x5 (16*i),
 .vop (.ext .v26 .v25 .v25 8),.vop (.logic .eor (vreg (2*i)) (vreg (2*i)) .v25),
 .vop (.logic .eor (vreg (2*i+1)) (vreg (2*i+1)) .v26)]
def full : List Instr := (List.range 8).flatMap absorbPair ++
 [.ldr .x .x6 .x5 128,.vop (.dup .d2 .v25 .x6),.vop (.logic .eor .v16 .v16 .v25),
 .addImm .x .x5 .x5 136]
def tail (wlen : Nat) : List Instr :=
 (if wlen==768 then absorbPair 0 else []) ++
 [.movz .x .x6 31 0,.vop (.dup .d2 .v25 .x6),
 .vop (.logic .eor (if wlen==768 then .v2 else .v0) (if wlen==768 then .v2 else .v0) .v25),
 .movz .x .x6 0x8000 3,.vop (.dup .d2 .v25 .x6),.vop (.logic .eor .v16 .v16 .v25)]
def output (n : Nat) : List Instr := (List.range (n/16)).flatMap (fun i =>
 [.vop (.perm .zip1 .d2 .v25 (vreg (2*i)) (vreg (2*i+1))),.strq .v25 .x2 (16*i)])
def hash (wlen olen : Nat) : Prog isa :=
 .seq (.block (save++first++[.addImm .x .x5 .x1 72,.movz .x .x4 (if wlen==768 then 6 else 8) 0])) <|
 .seq (.loop (.seq (.block (rounds++[.subImm .x .x4 .x4 1]))
  (.ite (.zero .x .x4) (.block []) (.block full))) (.nonzero .x .x4)) <|
 .block (tail wlen++rounds++output olen++restore)
def hashAt (wlen olen : Nat) (mu w out scratch : Ptr) : Prog isa :=
 callAt ("vg_mldsa_commit_hash"++toString olen) (hash wlen olen)
 [(.x0,.ptr mu),(.x1,.ptr w),(.x2,.ptr out),(.x3,.ptr scratch)]
end CommitHash

open VG VG.AArch64
namespace CombDot
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call

def product (j : Nat) : List Instr :=
 [.ldrq .v0 .x1 (1024*j),.ldrq .v1 .x2 (1024*j)] ++
 (if j=0 then [.vop (.umull false .v2 .v0 .v1),.vop (.umull true .v3 .v0 .v1)]
 else [.vop (.umlal false .v2 .v0 .v1),.vop (.umlal true .v3 .v0 .v1)])
def dot (n : Nat) : Prog isa :=
 .seq (.block (consts ++ [.movz .x .x12 64 0])) <|
 .loop (.block ((List.range n).flatMap product ++
 [.vop (.perm .uzp1 .s4 .v4 .v2 .v3),.vop (.mul .v4 .v4 .v17),
 .vop (.umlal false .v2 .v4 .v16),.vop (.umlal true .v3 .v4 .v16),
 .vop (.perm .uzp2 .s4 .v0 .v2 .v3)] ++ csub .v0 .v4 ++
 [.strq .v0 .x0 0,.addImm .x .x0 .x0 16,.addImm .x .x1 .x1 16,
 .addImm .x .x2 .x2 16,.subImm .x .x12 .x12 1])) (.nonzero .x .x12)
def dotAt (n : Nat) (h f g : Ptr) : Prog isa :=
 callAt ("vg_mldsa_dot" ++ toString n) (dot n) [(.x0,.ptr h),(.x1,.ptr f),(.x2,.ptr g)]
end CombDot


namespace CombCopy
open VG.Impl.MlDsa.AArch64.Call
-- Disjoint source/destination regions as in copyChk; handle all lengths, including zero.
def copy (dst src : Ptr) (n : Nat) : Prog isa :=
 .seq (.block (lea .x0 dst.1 dst.2 ++ lea .x1 src.1 src.2)) <|
 .seq (if n/8=0 then .block [] else
  .seq (.block (movV .x2 (n/8)))
   (.loop (.block [.ldr .x .x9 .x1 0,.str .x .x9 .x0 0,
    .addImm .x .x0 .x0 8,.addImm .x .x1 .x1 8,.subImm .x .x2 .x2 1]) (.nonzero .x .x2)))
  (.block ((List.range (n%8)).flatMap fun j => [.ldrb .x9 .x1 j,.strb .x9 .x0 j]))
end CombCopy
/-!
# ML-DSA on AArch64: `vg_mldsa{44,65,87}_sign`

`sign(sk = x0, mu = x1, rnd = x2, sig = x3, scratch = x4) -> w0`:
`ML-DSA.Sign_internal(sk, M′, rnd)` (FIPS 204 Algorithm 7) with the message
representative `μ` given (`Spec.MlDsa.signMu`), for the parameter set `p`,
as calls of the primitives `P` and the sponge functions (`Frag.lean`). It
keeps `scratch` in `x28`, `sk` in `x25`, `mu` in `x26`, `rnd` in `x27` and
`sig` in `x23`, and saves its caller's values of them (and of `x24` and
`x30`) in `scratch`.

1. `ρ` (the first 32 bytes of `sk`) to `RS`, the seed of `RejNTTPoly`, and
   `Â[r, s] = RejNTTPoly(ρ ‖ s ‖ r)` for the `kℓ` entries, with `w24` the
   AND of the results. If one failed (`w24 = 0`), it returns 0 at once.
2. `ŝ₁`, `ŝ₂` and `t̂₀`: the `NTT` of the `BitUnpack` of their pieces of
   `sk`; and `ρ″ = H(K ‖ rnd ‖ μ, 64)` to `MS`.
3. The rejection sampling loop, at most 814 iterations (`minBounds.sign`),
   with the counter `κ` at `KAP`: the commitment (`y ← ExpandMask(ρ″, κ)`,
   `ŷ = NTT(y)`, `w = NTT⁻¹(Â ŷ)`, and `c̃ = H(μ ‖ w1Encode(HighBits(w)), λ/4)`
   at `CT`), then `c = SampleInBall(c̃)` and, if it succeeded, every validity
   check of the iteration, combined without a branch into `w24`: the norms
   of `z = y + NTT⁻¹(ĉ ŝ₁)`, of `r₀ = LowBits(w - NTT⁻¹(ĉ ŝ₂))` and of
   `ct₀ = NTT⁻¹(ĉ t̂₀)`, and the number of 1s of the hint
   `h = MakeHint(-ct₀, w - cs₂ + ct₀)`. The loop ends when `SampleInBall`
   fails (with `w24 = 0`), when the checks pass (`w24 = 1`), or after 814
   iterations.
4. If `w24 = 1`: `c̃`, the `BitPack` of `z` and `HintBitPack(h)` to `sig`.

Only the calls of `vg_mldsa_rej_ntt_poly` (whose seeds are `ρ` and two
indices), and the branch on their results, depend on `ρ`; only the calls of
`vg_mldsa_sample_in_ball`, and the branch on their results, on `c̃`; only
the branch on the validity checks on whether they passed, and only the call
of `vg_mldsa_hint_bit_pack` on the hint of the signature. Every other
address and branch depends only on the pointers.
-/

namespace WindowUnpack
open VG.Impl.MlKem.AArch64 (movImm mov)
open VG.Impl.MlDsa.AArch64.Pack

def vector (r : VReg) (vals : List Nat) : List Instr :=
 movImm .x9 (BitVec.ofNat 64 vals[0]!) ++ [.vop (.dup .s4 r .x9)] ++
 ((List.range 3).flatMap fun i => movImm .x9 (BitVec.ofNat 64 vals[i+1]!) ++ [.vop (.ins .s4 r (i+1) .x9)])
def byteIndices (r : VReg) (xs : List Nat) : List Instr :=
 let lo := ((List.range 8).map fun i => xs[i]! * 2^(8*i)).foldl (·+·) 0
 let hi := ((List.range 8).map fun i => xs[i+8]! * 2^(8*i)).foldl (·+·) 0
 movImm .x9 (BitVec.ofNat 64 lo) ++ [.vop (.dup .d2 r .x9)] ++
 movImm .x9 (BitVec.ofNat 64 hi) ++ [.vop (.ins .d2 r 1 .x9)]
def idxRegs : List VReg := [.v16,.v17,.v18,.v19]
def outRegs : List VReg := [.v4,.v5,.v6,.v7]
-- Sixteen fields consume exactly 2*d bytes. Last vector overlaps earlier bytes.
def indices (d group : Nat) : List Nat :=
 (List.range 16).map fun k =>
  let byte := k%4
  let field := 4*group+k/4
  let off := d*field/8+byte
  let n := if d=10 then 2 else 3
  if byte>=n then 255
  else if off< (if d=10 then 16 else 32) then off
  else off + (if d=10 then 12 else 48-2*d)
def init (d : Nat) : List Instr :=
 (List.range 4).flatMap (fun i => byteIndices idxRegs[i]! (indices d i)) ++
 vector .v23 ((List.range 4).map fun i => 2^((if d=20 then 4 else 6)-(d*i%8))) ++
 vector .v22 [2^d-1,2^d-1,2^d-1,2^d-1] ++
 (if d=10 then [] else vector .v20 [qNat,qNat,qNat,qNat] ++
  vector .v21 [2^(d-1),2^(d-1),2^(d-1),2^(d-1)]) ++ [.movz .x .x11 16 0]
def one (d i : Nat) : List Instr :=
 let r := outRegs[i]!
 [.vop (.tblN false (if d=10 then 2 else 3) r .v0 idxRegs[i]!),
  .vop (.mul r r .v23),.vop (.shift .ushr .s4 r r (if d=20 then 4 else 6)),
  .vop (.logic .and r r .v22)] ++
 (if d=10 then [.vop (.shift .shl .s4 r r 13)] else
  [.vop (.sub .s4 r .v21 r),.vop (.shift .sshr .s4 .v24 r 31),
   .vop (.logic .and .v24 .v24 .v20),.vop (.add .s4 r r .v24)]) ++ [.strq r .x4 (16*i)]
def body (d : Nat) : List Instr :=
 [.ldrq .v0 .x0 0] ++
 (if d=10 then [.addImm .x .x9 .x0 4,.ldrq .v1 .x9 0]
  else [.ldrq .v1 .x0 16,.addImm .x .x9 .x0 (2*d-16),.ldrq .v2 .x9 0]) ++
 (List.range 4).flatMap (one d) ++
 [.addImm .x .x0 .x0 (2*d),.addImm .x .x4 .x4 64,.subImm .x .x11 .x11 1]
def unpack (d : Nat) : Prog isa := .seq (.block (init d)) (.loop (.block (body d)) (.nonzero .x .x11))
def bitUnpack : Prog isa := sel .x1 640 (unpack 20) (sel .x1 576 (unpack 18) VG.Impl.MlDsa.AArch64.Pack.bitUnpack)
def unpackT1 : Prog isa := .seq (.block [mov .x4 .x1]) (unpack 10)
end WindowUnpack


namespace CombMask4
open VG VG.AArch64
open VG.Impl.MlKem.AArch64 (mov)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
def saved : List Reg := [.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28]
def pro : List Instr :=
 (List.range 10).map (fun i => .str .x (saved[i]!) .x3 (7968+8*i)) ++
 (List.range 8).flatMap (fun i => [.umov .x .x8 (vreg (8+i)) 0,.str .x .x8 .x3 (8048+8*i)]) ++
 [.str .w .x1 .x3 7904,mov .x19 .x3,mov .x20 .x0,mov .x21 .x2]
def epi : List Instr :=
 (List.range 8).flatMap (fun i => [.ldr .x .x8 .x19 (8048+8*i),.vop (.ins .d2 (vreg (8+i)) 0 .x8)]) ++
 (List.range 9).map (fun i => .ldr .x (saved[i+1]!) .x19 (7976+8*i)) ++
 [.ldr .x .x19 .x19 7968]
def seedWord (j : Nat) : List Instr :=
 [.ldr .x .x6 .x3 (8*j),.ldr .x .x7 .x4 (8*j),.vop (.dup .d2 .v0 .x6),
  .vop (.ins .d2 .v0 1 .x7),.strq .v0 .x2 (16*j)]
def lastWord (r n : Reg) : List Instr :=
 [.ldrb r n 64,.ldrb .x8 n 65,.lsl .x .x8 .x8 8,.add .x r r .x8]
def absorb (p : Nat) : List Instr :=
 [.addImm .x .x2 .x19 (400*p),.addImm .x .x3 .x20 (132*p),.addImm .x .x4 .x3 66] ++
 (List.range 8).flatMap seedWord ++ lastWord .x6 .x3 ++ lastWord .x7 .x4 ++
 [.movz .x .x9 31 1,.add .x .x6 .x6 .x9,.add .x .x7 .x7 .x9,
  .vop (.dup .d2 .v0 .x6),.vop (.ins .d2 .v0 1 .x7),.strq .v0 .x2 128,
  .movz .x .x9 0x8000 3,.vop (.dup .d2 .v0 .x9),.strq .v0 .x2 256]
def setup : List Instr :=
 [mov .x22 .x19,.addImm .x .x23 .x19 400,.addImm .x .x24 .x19 840,
  .addImm .x .x25 .x19 1520,.addImm .x .x26 .x19 2200,.addImm .x .x27 .x19 2880,
  .movz .x .x28 5 0]
def squeeze (a b : Reg) : List Instr :=
 (List.range 8).flatMap (fun i =>
 [.vop (.perm .trn1 .d2 .v26 (vreg (2*i)) (vreg (2*i+1))),
 .vop (.perm .trn2 .d2 .v27 (vreg (2*i)) (vreg (2*i+1))),
 .strq .v26 a (16*i),.strq .v27 b (16*i)]) ++
 [.umov .x .x6 .v16 0,.umov .x .x7 .v16 1,.str .x .x6 a 128,.str .x .x7 b 128]
def pair (p a b : Reg) : Prog isa :=
 .seq (.block (Impl.Sha3.AArch64.Neon.Pair.load p)) <|
 .seq (Impl.Sha3.AArch64.Neon.Pair.roundsProg true 24) <|
 .block (Impl.Sha3.AArch64.Neon.Pair.store p ++ squeeze a b)
-- Process each independent pair with its Keccak state resident for allfive blocks.
def residentPair (p a b : Reg) : Prog isa :=
 .seq (.block (Impl.Sha3.AArch64.Neon.Pair.load p ++ [.movz .x .x28 5 0])) <|
 .seq (.loop (.seq (Impl.Sha3.AArch64.Neon.Pair.roundsProg true 24)
  (.block (squeeze a b ++ [.addImm .x a a 136,.addImm .x b b 136,.subImm .x .x28 .x28 1]))) (.nonzero .x .x28)) <|
 .block (Impl.Sha3.AArch64.Neon.Pair.store p)
def unpack (c k : Nat) : Prog isa :=
 .seq (.block [.addImm .x .x0 .x19 (840+680*k),.addImm .x .x4 .x21 (1024*k),.movz .x .x11 16 0]) <|
 .loop (.block (WindowUnpack.body c)) (.nonzero .x .x11)
def unpack4 (c : Nat) : Prog isa :=
 .seq (.block (WindowUnpack.init c)) <|
 .seq (unpack c 0) <| .seq (unpack c 1) <| .seq (unpack c 2) (unpack c 3)
def prog : Prog isa :=
 .seq (.block (pro ++ Rej4.zeroStates ++ absorb 0 ++ absorb 1 ++ setup)) <|
 .seq (.seq (residentPair .x22 .x24 .x25) (residentPair .x23 .x26 .x27)) <|
 .seq (.block [.ldr .w .x27 .x19 7904,.lsr .x .x9 .x27 18]) <|
 .seq (.ite (.zero .x .x9) (unpack4 18) (unpack4 20)) (.block epi)
end CombMask4
/-!
# ML-DSA on AArch64: `vg_mldsa{44,65,87}_sign`

`sign(sk = x0, mu = x1, rnd = x2, sig = x3, scratch = x4) -> w0`:
`ML-DSA.Sign_internal(sk, M′, rnd)` (FIPS 204 Algorithm 7) with the message
representative `μ` given (`Spec.MlDsa.signMu`), for the parameter set `p`,
as calls of the primitives `P` and the sponge functions (`Frag.lean`). It
keeps `scratch` in `x28`, `sk` in `x25`, `mu` in `x26`, `rnd` in `x27` and
`sig` in `x23`, and saves its caller's values of them (and of `x24` and
`x30`) in `scratch`.

1. `ρ` (the first 32 bytes of `sk`) to `RS`, the seed of `RejNTTPoly`, and
   `Â[r, s] = RejNTTPoly(ρ ‖ s ‖ r)` for the `kℓ` entries, with `w24` the
   AND of the results. If one failed (`w24 = 0`), it returns 0 at once.
2. `ŝ₁`, `ŝ₂` and `t̂₀`: the `NTT` of the `BitUnpack` of their pieces of
   `sk`; and `ρ″ = H(K ‖ rnd ‖ μ, 64)` to `MS`.
3. The rejection sampling loop, at most 814 iterations (`minBounds.sign`),
   with the counter `κ` at `KAP`: the commitment (`y ← ExpandMask(ρ″, κ)`,
   `ŷ = NTT(y)`, `w = NTT⁻¹(Â ŷ)`, and `c̃ = H(μ ‖ w1Encode(HighBits(w)), λ/4)`
   at `CT`), then `c = SampleInBall(c̃)` and, if it succeeded, every validity
   check of the iteration, combined without a branch into `w24`: the norms
   of `z = y + NTT⁻¹(ĉ ŝ₁)`, of `r₀ = LowBits(w - NTT⁻¹(ĉ ŝ₂))` and of
   `ct₀ = NTT⁻¹(ĉ t̂₀)`, and the number of 1s of the hint
   `h = MakeHint(-ct₀, w - cs₂ + ct₀)`. The loop ends when `SampleInBall`
   fails (with `w24 = 0`), when the checks pass (`w24 = 1`), or after 814
   iterations.
4. If `w24 = 1`: `c̃`, the `BitPack` of `z` and `HintBitPack(h)` to `sig`.

Only the calls of `vg_mldsa_rej_ntt_poly` (whose seeds are `ρ` and two
indices), and the branch on their results, depend on `ρ`; only the calls of
`vg_mldsa_sample_in_ball`, and the branch on their results, on `c̃`; only
the branch on the validity checks on whether they passed, and only the call
of `vg_mldsa_hint_bit_pack` on the hint of the signature. Every other
address and branch depends only on the pointers.
-/

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

namespace CombHintReuse
open VG VG.AArch64
-- r=x0, gamma=x1, high=x2, low=x3; supports high==r.
def decompose : Prog isa :=
 VG.Impl.MlDsa.AArch64.Round.zext .x1 <|
 VG.Impl.MlDsa.AArch64.Round.onGamma .x1 .x4 fun g =>
 .seq (.block (CombRound.constants g)) <|
 CombRound.loop [.x0,.x2,.x3] fun off => [.ldrq .v0 .x0 off] ++
 CombRound.hb g .v1 .v0 ++ [.vop (.mls .v0 .v1 .v21)] ++ CombRound.cadd .v0 ++
 [.strq .v1 .x2 off,.strq .v0 .x3 off]
-- canonical lowSum=x0, high=x1, gamma=x2, hints=x3. The low sum is bounded
-- by two gamma once all norm checks pass; otherwise the attempt is discarded.
def hint : Prog isa :=
 VG.Impl.MlDsa.AArch64.Round.zext .x2 <|
 .seq (VG.Impl.MlDsa.AArch64.Round.onGamma .x2 .x4 fun g =>
  .seq (.block (CombRound.vc .v16 g ++ CombRound.vc .v17 (8380417-g) ++
    [.vop (.movi0 .v18),.vop (.movi0 .v31)])) <|
  CombRound.loop [.x0,.x1,.x3] fun off =>
   [.ldrq .v0 .x0 off,.ldrq .v1 .x1 off,
    .vop (.sub .s4 .v2 .v16 .v0),.vop (.sub .s4 .v3 .v0 .v17),
    .vop (.logic .and .v2 .v2 .v3),.vop (.shift .sshr .s4 .v2 .v2 31),
    .vop (.cmeq .s4 .v3 .v0 .v17),.vop (.cmeq .s4 .v4 .v1 .v18),
    .vop (.logic .bic .v3 .v3 .v4),.vop (.logic .orr .v2 .v2 .v3),
    .vop (.shift .ushr .s4 .v2 .v2 31),.strq .v2 .x3 off,
    .vop (.add .s4 .v31 .v31 .v2)]) <|
 .block [.umov .w .x0 .v31 0,.umov .w .x9 .v31 1,.add .w .x0 .x0 .x9,
  .umov .w .x9 .v31 2,.add .w .x0 .x0 .x9,.umov .w .x9 .v31 3,.add .w .x0 .x0 .x9]
end CombHintReuse
namespace CombFusedCheck
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Round
open CombRound
def testNorm : List Instr :=
 [.vop (.sub .s4 .v2 .v16 .v0),.vop (.umin .v2 .v0 .v2),
 .vop (.umin .v2 .v2 .v24),.vop (.cmeq .s4 .v2 .v2 .v24),.vop (.logic .orr .v31 .v31 .v2)]
def finish : Prog isa := .block [
 .umov .w .x0 .v31 0,.umov .w .x9 .v31 1,.logic .orr .w .x0 .x0 .x9,
 .umov .w .x9 .v31 2,.logic .orr .w .x0 .x0 .x9,.umov .w .x9 .v31 3,
 .logic .orr .w .x0 .x0 .x9,.addImm .w .x0 .x0 1]
-- canonical inout=x0, canonical addend=x1, bound=w2; return bool w0.
def addNorm : Prog isa :=
 .seq (.block (vc .v16 8380417 ++ [.vop (.dup .s4 .v24 .x2),.vop (.movi0 .v31)])) <|
 .seq (loop [.x0,.x1] fun off => [.ldrq .v0 .x0 off,.ldrq .v1 .x1 off,
 .vop (.add .s4 .v0 .v0 .v1)] ++ csub .v0 ++ [.strq .v0 .x0 off] ++ testNorm) finish
-- inout=x0 (canonical input, high output), subtrahend=x1, low=x2, gamma=w3, bound=w4.
def subLowNorm : Prog isa :=
 zext .x3 <| onGamma .x3 .x5 fun g =>
 .seq (.block (constants g ++ [.vop (.dup .s4 .v24 .x4),.vop (.movi0 .v31)])) <|
 .seq (loop [.x0,.x1,.x2] fun off => [.ldrq .v0 .x0 off,.ldrq .v1 .x1 off,
 .vop (.add .s4 .v0 .v0 .v16),.vop (.sub .s4 .v0 .v0 .v1)] ++ csub .v0 ++
 hb g .v1 .v0 ++ [.strq .v1 .x0 off,.vop (.mls .v0 .v1 .v21)] ++ cadd .v0 ++
 [.strq .v0 .x2 off] ++ testNorm) finish
end CombFusedCheck

namespace CombFusedCheck
-- low→hint=x0, ct0=x1, high=x2, gamma=w3; return u64: low32=count, bit32=normflag.
def hintNorm : Prog isa :=
 .seq (.block (CombRound.vc .v16 8380417 ++
 [.vop (.dup .s4 .v24 .x3),.vop (.dup .s4 .v17 .x3),
 .vop (.sub .s4 .v18 .v16 .v17),.vop (.movi0 .v23),.vop (.movi0 .v30),.vop (.movi0 .v31)])) <|
 .seq (CombRound.loop [.x0,.x1,.x2] fun off =>
 [.ldrq .v0 .x1 off,.ldrq .v3 .x0 off,.ldrq .v4 .x2 off] ++ testNorm ++
 [.vop (.add .s4 .v0 .v0 .v3)] ++ CombRound.csub .v0 ++
 [.vop (.sub .s4 .v2 .v17 .v0),.vop (.sub .s4 .v3 .v0 .v18),
 .vop (.logic .and .v2 .v2 .v3),.vop (.shift .sshr .s4 .v2 .v2 31),
 .vop (.cmeq .s4 .v3 .v0 .v18),.vop (.cmeq .s4 .v4 .v4 .v23),
 .vop (.logic .bic .v3 .v3 .v4),.vop (.logic .orr .v2 .v2 .v3),
 .vop (.shift .ushr .s4 .v2 .v2 31),.strq .v2 .x0 off,.vop (.add .s4 .v30 .v30 .v2)]) <|
 .block [.umov .w .x1 .v31 0,.umov .w .x9 .v31 1,.logic .orr .w .x1 .x1 .x9,
 .umov .w .x9 .v31 2,.logic .orr .w .x1 .x1 .x9,.umov .w .x9 .v31 3,.logic .orr .w .x1 .x1 .x9,.addImm .w .x1 .x1 1,
 .umov .w .x0 .v30 0,.umov .w .x9 .v30 1,.add .w .x0 .x0 .x9,
 .umov .w .x9 .v30 2,.add .w .x0 .x0 .x9,.umov .w .x9 .v30 3,.add .w .x0 .x0 .x9,
 .lsl .x .x1 .x1 32,.logic .orr .x .x0 .x0 .x1]
end CombFusedCheck

namespace SquareSignedCheck
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Round
open CombRound
-- v25=2^22, v16=q. v6 temporary; result congruent modulo q.
def reduce (d : VReg) : List Instr :=
 [.vop (.add .s4 .v6 d .v25),.vop (.shift .sshr .s4 .v6 .v6 23),.vop (.mls d .v6 .v16)]
def normConstants : List Instr := vc .v27 1 ++
 [.vop (.sub .s4 .v27 .v24 .v27),.vop (.add .s4 .v24 .v24 .v27)]
def testNorm : List Instr :=
 [.vop (.add .s4 .v2 .v0 .v27),.vop (.umin .v2 .v2 .v24),
 .vop (.cmeq .s4 .v2 .v2 .v24),.vop (.logic .orr .v31 .v31 .v2)]
def addNorm : Prog isa :=
 .seq (.block (vc .v16 8380417 ++ vc .v25 (2^22) ++
 [.vop (.dup .s4 .v24 .x2),.vop (.movi0 .v31)] ++ normConstants)) <|
 .seq (loop [.x0,.x1] fun off => [.ldrq .v0 .x0 off,.ldrq .v1 .x1 off,
 .vop (.add .s4 .v0 .v0 .v1)] ++ reduce .v0 ++ [.strq .v0 .x0 off] ++ testNorm)
 CombFusedCheck.finish
-- Canonical input w; signed raw cs; high output overwrites w, signed low to x2.
def subLowNorm : Prog isa :=
 zext .x3 <| onGamma .x3 .x5 fun g =>
 .seq (.block (constants g ++ vc .v25 (2^22) ++ vc .v26 4190208 ++
 [.vop (.dup .s4 .v24 .x4),.vop (.movi0 .v31)] ++ normConstants)) <|
 .seq (loop [.x0,.x1,.x2] fun off => [.ldrq .v0 .x0 off,.ldrq .v1 .x1 off,
 .vop (.sub .s4 .v0 .v0 .v1)] ++ reduce .v0 ++ cadd .v0 ++
 hb g .v1 .v0 ++ [.strq .v1 .x0 off,.vop (.mls .v0 .v1 .v21),
 -- For the exceptional wrapped high=0, subtract q from the large positive low.
 .vop (.sub .s4 .v6 .v26 .v0),.vop (.shift .sshr .s4 .v6 .v6 31),
 .vop (.logic .and .v6 .v6 .v16),.vop (.sub .s4 .v0 .v0 .v6),
 .strq .v0 .x2 off] ++ testNorm) CombFusedCheck.finish
-- Signed low -> hints; signed raw ct; canonical high. u64 count | validNorm<<32.
def hintNorm : Prog isa :=
 .seq (.block (vc .v16 8380417 ++ vc .v25 (2^22) ++
 [.vop (.dup .s4 .v24 .x3),.vop (.dup .s4 .v17 .x3),
 .vop (.movi0 .v23),.vop (.sub .s4 .v18 .v23 .v17),
 .vop (.movi0 .v30),.vop (.movi0 .v31)] ++ normConstants)) <|
 .seq (loop [.x0,.x1,.x2] fun off =>
 [.ldrq .v0 .x1 off,.ldrq .v3 .x0 off,.ldrq .v4 .x2 off] ++ reduce .v0 ++ testNorm ++
 [.vop (.add .s4 .v0 .v0 .v3),
 -- negative masks for gamma-t and t+gamma implement strict outside interval.
 .vop (.sub .s4 .v2 .v17 .v0),.vop (.sub .s4 .v3 .v0 .v18),
 .vop (.logic .orr .v2 .v2 .v3),.vop (.shift .sshr .s4 .v2 .v2 31),
 .vop (.cmeq .s4 .v3 .v0 .v18),.vop (.cmeq .s4 .v4 .v4 .v23),
 .vop (.logic .bic .v3 .v3 .v4),.vop (.logic .orr .v2 .v2 .v3),
 .vop (.shift .ushr .s4 .v2 .v2 31),.strq .v2 .x0 off,.vop (.add .s4 .v30 .v30 .v2)]) <|
 .block [.umov .w .x1 .v31 0,.umov .w .x9 .v31 1,.logic .orr .w .x1 .x1 .x9,
 .umov .w .x9 .v31 2,.logic .orr .w .x1 .x1 .x9,.umov .w .x9 .v31 3,.logic .orr .w .x1 .x1 .x9,.addImm .w .x1 .x1 1,
 .umov .w .x0 .v30 0,.umov .w .x9 .v30 1,.add .w .x0 .x0 .x9,
 .umov .w .x9 .v30 2,.add .w .x0 .x0 .x9,.umov .w .x9 .v30 3,.add .w .x0 .x0 .x9,
 .lsl .x .x1 .x1 32,.logic .orr .x .x0 .x0 .x1]
-- Called only at accepted output: signed z in (-gamma1,gamma1), to canonical residues.
def canonicalize : Prog isa := .seq (.block (vc .v16 8380417)) <|
 loop [.x0] fun off => [.ldrq .v0 .x0 off] ++ cadd .v0 ++ [.strq .v0 .x0 off]
end SquareSignedCheck

namespace CombSignMask4
open VG.Impl.MlDsa.AArch64.Sign

variable (c : Impl.Sha3.AArch64.Callee)

open VG.AArch64 VG.Impl.MlDsa.AArch64.Call
open VG.Spec.MlDsa (Params bitlen q)

/-! ## The constants of a parameter set -/

section
variable (p : Params)

/-- `λ/4`, the length of `c̃`. -/
abbrev cLen : Nat := p.ctildeLen
/-- The bound `(q - 1)/(2γ₂) - 1` of the coefficients of `w₁`. -/
abbrev w1Max : Nat := (q - 1) / (2 * p.γ₂) - 1
/-- The length of the encoding of a polynomial of `w₁`. -/
abbrev w1Len : Nat := 32 * bitlen (w1Max p)
/-- The length of the encoding of a polynomial of `z`. -/
abbrev zLen : Nat := 32 * (1 + bitlen (p.γ₁ - 1))
/-- The length of the encoding of a polynomial of `s₁` or `s₂`. -/
abbrev sLen : Nat := 32 * bitlen (2 * p.η)

/-- The offsets of `s₁[r]`, `s₂[i]` and `t₀[i]` in `sk`. -/
abbrev skS1 (r : Nat) : Nat := 128 + sLen p * r
abbrev skS2 (i : Nat) : Nat := 128 + sLen p * p.ℓ + sLen p * i
abbrev skT0 (i : Nat) : Nat := 128 + sLen p * (p.ℓ + p.k) + 416 * i

/-- The offsets of `z[r]` and of the hint in `sig`. -/
abbrev sigZ (r : Nat) : Nat := cLen p + zLen p * r
abbrev sigH : Nat := cLen p + zLen p * p.ℓ

/-! ## The polynomials of the working space

`ĉ` (0), four temporaries (1–4), then `h` (`k`), `y` (`ℓ`), `ŷ` (`ℓ`),
`w` (`k`), `ŝ₁` (`ℓ`), `ŝ₂` (`k`), `t̂₀` (`k`) and `Â` (`kℓ`, row by row). -/

abbrev pS (i : Nat) : Ptr := sc (oP i)
abbrev cP : Ptr := pS 0
abbrev t1P : Ptr := pS 1
abbrev t2P : Ptr := pS 2
abbrev t3P : Ptr := pS 3
abbrev t4P : Ptr := pS 4
abbrev hP (i : Nat) : Ptr := pS (5 + i)
abbrev yP (r : Nat) : Ptr := pS (5 + p.k + r)
abbrev yhP (r : Nat) : Ptr := pS (5 + p.k + p.ℓ + r)
abbrev wP (i : Nat) : Ptr := pS (5 + p.k + 2 * p.ℓ + i)
abbrev s1P (r : Nat) : Ptr := pS (5 + 2 * p.k + 2 * p.ℓ + r)
abbrev s2P (i : Nat) : Ptr := pS (5 + 2 * p.k + 3 * p.ℓ + i)
abbrev t0P (i : Nat) : Ptr := pS (5 + 3 * p.k + 3 * p.ℓ + i)
abbrev aP (i j : Nat) : Ptr := pS (5 + 4 * p.k + 3 * p.ℓ + p.ℓ * i + j)

end

/-! ## The pieces -/

section
variable (P : Prims) (p : Params)

/-- `Â[e / ℓ, e % ℓ] = RejNTTPoly(ρ ‖ e % ℓ ‖ e / ℓ)`, with `ρ` at `RS`. -/
def sampleE (e : Nat) : Prog isa :=
  .seq (.block (setB (sc (oRS + 32)) (e % p.ℓ) ++ setB (sc (oRS + 33)) (e / p.ℓ))) (rejAt P (aP p (e / p.ℓ) (e % p.ℓ)))

/-- Scratch for the four simultaneous SHAKE streams, after the matrix. -/
def oR4 : Nat := oP (5+4*p.k+3*p.ℓ+p.k*p.ℓ)

def seedSlot4 (e j : Nat) : Prog isa :=
  .seq (.block (lea .x10 .x28 (oRS4+34*j) ++ Impl.MlKem.AArch64.copy32 .x28 oRS .x10 0))
    (.block (setB (sc (oRS4+34*j+32)) ((e+j)%p.ℓ) ++ setB (sc (oRS4+34*j+33)) ((e+j)/p.ℓ)))

def sample4 (g : Nat) : Prog isa :=
  .seq (seqR (seedSlot4 p (4*g)) 0 4)
    (.seq (callAt ("vg_mldsa_rej_ntt_poly4"++P.suffix) P.rej4
      [(.x0,.ptr (sc oRS4)),(.x1,.ptr (pS (5+4*p.k+3*p.ℓ+4*g))),(.x2,.ptr (sc (oR4 p)))]) (.block and24))

def sampleAll : Prog isa :=
  .seq (seqR (sample4 P p) 0 (p.k*p.ℓ/4)) (if P.suffix == "_sha3" && p.k*p.ℓ%4 == 2 then
    .seq (seqR (seedSlot4 p (4*(p.k*p.ℓ/4))) 0 2)
     (.seq (callAt "vg_mldsa_rej_ntt_poly2_sha3" RootPair.rootRej2
      [(.x0,.ptr (sc oRS4)),(.x1,.ptr (pS (5+4*p.k+3*p.ℓ+4*(p.k*p.ℓ/4)))),(.x2,.ptr (sc (oR4 p)))]) (.block and24))
   else seqR (sampleE P p) (4*(p.k*p.ℓ/4)) (p.k*p.ℓ%4))

/-- `ρ` to four seed slots, and matrix expansion in batches of four. -/
def expandA : Prog isa :=
  .seq (.block (Impl.MlKem.AArch64.copy32 .x25 0 .x28 oRS)) (sampleAll P p)

/-- `ŝ₁[r]`. -/
def decS1 (r : Nat) : Prog isa :=
  .seq (bitUnpackAt P (.x25, skS1 p r) (sLen p) p.η p.η (s1P p r)) (nttAt P (s1P p r))

/-- `ŝ₂[i]`. -/
def decS2 (i : Nat) : Prog isa :=
  .seq (bitUnpackAt P (.x25, skS2 p i) (sLen p) p.η p.η (s2P p i)) (nttAt P (s2P p i))

/-- `t̂₀[i]`. -/
def decT0 (i : Nat) : Prog isa :=
  .seq (bitUnpackAt P (.x25, skT0 p i) 416 4095 4096 (t0P p i)) (nttAt P (t0P p i))

/-- `ŝ₁`, `ŝ₂`, `t̂₀`, and `ρ″ = H(K ‖ rnd ‖ μ, 64)` to `MS`. -/
def decodeWith : Prog isa :=
  .seq (seqR (decS1 P p) 0 p.ℓ) (.seq (seqR (decS2 P p) 0 p.k) (.seq (seqR (decT0 P p) 0 p.k)
    ((shakeAtWith c) [⟨.x25, 32, 32⟩, ⟨.x27, 0, 32⟩, ⟨.x26, 0, 64⟩] ⟨.x28, oMS, 64⟩)))

/-! ### An iteration -/

/-- The two bytes of `κ + r` to `MS + 64`, through `x9`. -/
def setKappa (r : Nat) : List Instr :=
  [.ldr .x .x9 .x28 oKAP, .addImm .x .x9 .x9 r, .strb .x9 .x28 (oMS + 64), .lsr .x .x9 .x9 8,
    .strb .x9 .x28 (oMS + 65)]

/-- `y[r]` and `ŷ[r] = NTT(y[r])`. -/
def maskR (r : Nat) : Prog isa :=
  .seq (.block (setKappa r)) (.seq (maskAt P p.γ₁ (yP p r)) (rootNttOut P (yhP p r) (yP p r)))

/-- `w[i] = NTT⁻¹(∑_j Â[i, j] ŷ[j])`. -/
def rowW (i : Nat) : Prog isa :=
  .seq (CombDot.dotAt p.ℓ (wP p i) (aP p i 0) (yhP p 0)) (invNttAt P (wP p i))

/-- `w1Encode(HighBits(w[i]))` to `W1 + i · w1Len`. -/
def w1R (i : Nat) : Prog isa :=
  .seq (highBitsAt P (wP p i) p.γ₂ t1P) (simpleBitPackAt P t1P (w1Max p) (sc (oW1 + w1Len p * i)) (w1Len p))

def mask4Seed (g j : Nat) : Prog isa :=
 .seq (CombCopy.copy (sc (1632+66*j)) (sc oMS) 64) <|
 .block [.ldr .x .x9 .x28 oKAP,.addImm .x .x9 .x9 (4*g+j),
  .strb .x9 .x28 (1632+66*j+64),.lsr .x .x9 .x9 8,.strb .x9 .x28 (1632+66*j+65)]
def mask4Group (g : Nat) : Prog isa :=
 .seq (seqR (mask4Seed g) 0 4) <|
 .seq (.block (glue [(.x0,.ptr (sc 1632)),(.x1,.imm p.γ₁),
   (.x2,.ptr (yP p (4*g))),(.x3,.ptr (sc (oR4 p)))])) <|
 .seq (.call "vg_mldsa_expand_mask4_resident_shared" (WindowShared.wrap CombMask4.prog)) <|
 seqR (fun j => rootNttOut P (yhP p j) (yP p j)) (4*g) 4

/-- `y`, `ŷ`, `w`, `w₁` and `c̃ = H(μ ‖ w1Encode(w₁), λ/4)` to `CT`. -/
def commitWith (_c : Impl.Sha3.AArch64.Callee) (P : Prims) (p : Params) : Prog isa :=
  .seq (.seq (seqR (mask4Group P p) 0 (p.ℓ/4)) (seqR (maskR P p) (4*(p.ℓ/4)) (p.ℓ%4))) (.seq (seqR (rowW P p) 0 p.k) (.seq (seqR (w1R P p) 0 p.k)
    (CommitHash.hashAt (p.k * w1Len p) (cLen p) (.x26,0) (sc oW1) (sc oCT) (sc 0))))

/-- `z[r] = y[r] + NTT⁻¹(ĉ ŝ₁[r])` (in `y[r]`), and its norm. -/
def zR (r : Nat) : Prog isa :=
 .seq (callAt "vg_mldsa_multiply_inverse_raw" RootMul.staticCode [(.x0,.ptr t1P),(.x1,.ptr cP),(.x2,.ptr (s1P p r)),(.x3,.ptr (sc oPS))]) <|
 .seq (callAt "vg_mldsa_signed_add_norm" SquareSignedCheck.addNorm
  [(.x0,.ptr (yP p r)),(.x1,.ptr t1P),(.x2,.imm (p.γ₁-p.β))]) (.block and24)

def r0R (i : Nat) : Prog isa :=
 .seq (callAt "vg_mldsa_multiply_inverse_raw" RootMul.staticCode [(.x0,.ptr t1P),(.x1,.ptr cP),(.x2,.ptr (s2P p i)),(.x3,.ptr (sc oPS))]) <|
 .seq (callAt "vg_mldsa_signed_sub_low_norm" SquareSignedCheck.subLowNorm
  [(.x0,.ptr (wP p i)),(.x1,.ptr t1P),(.x2,.ptr (hP i)),(.x3,.imm p.γ₂),(.x4,.imm (p.γ₂-p.β))]) (.block and24)
def hR (i : Nat) : Prog isa :=
 .seq (callAt "vg_mldsa_multiply_inverse_raw" RootMul.staticCode [(.x0,.ptr t3P),(.x1,.ptr cP),(.x2,.ptr (t0P p i)),(.x3,.ptr (sc oPS))]) <|
 .seq (callAt "vg_mldsa_signed_hint_norm" SquareSignedCheck.hintNorm
 [(.x0,.ptr (hP i)),(.x1,.ptr t3P),(.x2,.ptr (wP p i)),(.x3,.imm p.γ₂)])
 (.block ([.lsr .x .x1 .x0 32,.logic .and .w .x24 .x24 .x1] ++ onesAdd))

def zPair (r : Nat) : Prog isa :=
 .seq (callAt "vg_mldsa_fused_pair_z" (RootPaired.SquareFusedPair.code .z)
 [(.x0,.ptr cP),(.x1,.ptr (s1P p (2*r))),(.x2,.ptr (yP p (2*r))),
  (.x3,.ptr t1P),(.x4,.ptr t1P),(.x5,.imm p.γ₁),(.x6,.imm (p.γ₁-p.β))]) (.block and24)
def r0Pair (i : Nat) : Prog isa :=
 .seq (callAt "vg_mldsa_fused_pair_r0" (RootPaired.SquareFusedPair.code .r0)
 [(.x0,.ptr cP),(.x1,.ptr (s2P p (2*i))),(.x2,.ptr (wP p (2*i))),
  (.x3,.ptr (hP (2*i))),(.x4,.ptr t1P),(.x5,.imm p.γ₂),(.x6,.imm (p.γ₂-p.β))]) (.block and24)
def hPair (i : Nat) : Prog isa :=
 .seq (callAt "vg_mldsa_fused_pair_h" (RootPaired.SquareFusedPair.code .h)
 [(.x0,.ptr cP),(.x1,.ptr (t0P p (2*i))),(.x2,.ptr (hP (2*i))),
  (.x3,.ptr (wP p (2*i))),(.x4,.ptr t1P),(.x5,.imm p.γ₂),(.x6,.imm p.γ₂)])
 (.block ([.lsr .x .x1 .x0 32,.logic .and .w .x24 .x24 .x1] ++ onesAdd))
def pairChecks (single paired : Nat → Prog isa) (n : Nat) : Prog isa :=
 .seq (seqR paired 0 (n/2)) (seqR single (2*(n/2)) (n%2))

/-- `x24 ← x24 ∧ (ONES ≤ ω)`: `ONES - (ω + 1)` is negative exactly then. -/
def onesOk : List Instr :=
  [.ldr .x .x9 .x28 oONES, .subImm .x .x9 .x9 (p.ω + 1), .lsr .x .x9 .x9 63, .logic .and .w .x24 .x24 .x9]

/-- `KAP ← KAP + ℓ`, through `x9`. -/
def kapAdd : List Instr := [.ldr .x .x9 .x28 oKAP, .addImm .x .x9 .x9 p.ℓ, .str .x .x9 .x28 oKAP]

/-- The validity checks of an iteration, combined into `x24`; then, if they
passed, `CNT ← 1` (the loop ends with `w24 = 1`), and otherwise `κ ← κ + ℓ`. -/
def checks : Prog isa :=
  .seq (nttAt P cP) (.seq (.block ([.movz .x .x24 1 0] ++ setQ (sc oONES) 0))
    (.seq (pairChecks (zR p) (zPair p) p.ℓ) (.seq (pairChecks (r0R p) (r0Pair p) p.k) (.seq (pairChecks (hR p) (hPair p) p.k)
      (.seq (.block (onesOk p)) (ifOkElse (.block (setQ (sc oCNT) 1)) (.block (kapAdd p))))))))

/-- `CNT ← CNT - 1`, left in `x9`, which the loop tests. -/
def cntDec : List Instr := [.ldr .x .x9 .x28 oCNT, .subImm .x .x9 .x9 1, .str .x .x9 .x28 oCNT]

/-- An iteration: the commitment, `SampleInBall`, and the checks if it
succeeded (and otherwise `x24 ← 0`, `CNT ← 1`); then `CNT ← CNT - 1`. -/
def iterWith : Prog isa :=
  .seq ((commitWith c) P p) (.seq (ballAt P (cLen p) p.τ cP)
    (.seq (.ite (.nonzero .w .x0) (checks P p) (.block ([.movz .x .x24 0 0] ++ setQ (sc oCNT) 1)))
      (.block cntDec)))

/-- The rejection sampling loop: `κ ← 0`, `CNT ← 814`, and iterations while
`CNT ≠ 0`. -/
def signLoopWith : Prog isa :=
  .seq (.block (setQ (sc oKAP) 0 ++ setQ (sc oCNT) 814)) (.loop ((iterWith c) P p) (.nonzero .x .x9))

/-! ### The signature -/

/-- `BitPack(z[r], γ₁ - 1, γ₁)` to `sig`. -/
def packZ (r : Nat) : Prog isa :=
 .seq (callAt "vg_mldsa_signed_canonicalize" SquareSignedCheck.canonicalize [(.x0,.ptr (yP p r))])
 (bitPackAt P (yP p r) (p.γ₁ - 1) p.γ₁ (.x23, sigZ p r) (zLen p))

/-- `c̃`, `z` and `HintBitPack(h)` to `sig`. -/
def output : Prog isa :=
  .seq (CombCopy.copy (.x23, 0) (sc oCT) (cLen p)) (.seq (seqR (packZ P p) 0 p.ℓ)
    (hintBitPackAt P (hP 0) (256 * p.k) p.ω (.x23, sigH p) (p.ω + p.k)))

/-- Once `Â` is sampled: the private key, the loop, and the signature if the
loop succeeded. -/
def restWith : Prog isa := .seq ((decodeWith c) P p) (.seq ((signLoopWith c) P p) (ifOk (output P p)))

end

/-- `vg_mldsa{44,65,87}_sign` for the parameter set `p`, with the primitives `P`. -/
def signWith (P : Prims) (p : Params) : Prog isa :=
  .seq (.block pro) (.seq (expandA P p) (.seq (ifOk ((restWith c) P p)) (.block epi)))

def decode := decodeWith .scalar
def commit := commitWith .scalar
def iter := iterWith .scalar
def signLoop := signLoopWith .scalar
def rest := restWith .scalar
def sign := signWith .scalar

end CombSignMask4



def main : IO Unit := do
 let callee := VG.Variants.Keccak.AArch64.Sha3.variant.callee
 let prims := Proof.MlDsa.AArch64.Sign.primsWith callee
 for (name,p) in [("44",Spec.MlDsa.mlDsa44),("65",Spec.MlDsa.mlDsa65)] do
  let code := printer.function (CombSignMask4.signWith callee prims p)
  IO.FS.writeFile ("/tmp/comb-pairedshared-sign"++name++"_sha3.body") (String.join (code.map (Rust.line printer.call)))
  IO.println s!"signed-roworiginal-sign{name}: {code.length}"
