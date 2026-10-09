import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith
open VG.Impl.MlKem.AArch64 (mov)
namespace VG.Impl.MlDsa.AArch64.Optimized.Inverse
def vr : Nat → VReg | 0 => .v0 | 1 => .v1 | 2 => .v2 | 3 => .v3 | 4 => .v4 | 5 => .v5 | 6 => .v6 | _ => .v7
def z (i : Nat) : Nat := (8380417-1753^Spec.MlDsa.bitRev8 i%8380417)%8380417
def bar (x : Nat) : Nat := x*2^31/8380417
def cv (r : VReg) (xs : List Nat) : List Instr :=
 movW .x9 xs[0]! ++ [.vop (.dup .s4 r .x9)] ++
 (List.range 3).flatMap (fun j => if xs[j+1]! = xs[0]! then [] else movW .x9 xs[j+1]! ++ [.vop (.ins .s4 r (j+1) .x9)])
def mul (d : VReg) : List Instr :=
 [.vop (.sqdmulh .v19 d .v21),.vop (.mul d d .v20),.vop (.mls d .v19 .v31)]
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
def rootAt (_base : Reg) (off len : Nat) : List Instr :=
 let start := if len=1 then 0 else if len=2 then 128 else if len=4 then 256 else if len=8 then 384 else 448
 let j := if len=1 then off/16 else if len=2 then off/8 else off/4
 [.ldrq .v20 .x1 (start+32*j),.ldrq .v21 .x1 (start+32*j+16)]

def firstBlock : List Instr :=
 let ld := (List.range 8).map (fun j => Instr.ldrq (vr j) .x0 (16*j))
 let packedCode := [1,2].flatMap (fun len => (List.range 4).flatMap (fun j => rootAt (if len=1 then .x3 else .x4) (16*j/len) len ++ packed (vr (2*j)) (vr (2*j+1)) len))
 let st : CS := {code := ld++packedCode}
 let st := [4,8,16].foldl (fun st len => (List.range (16/len)).foldl (fun st b =>
   batch {st with code := st.code++rootAt (if len=4 then .x5 else if len=8 then .x6 else .x7) (4*b) len}
    ((List.range (len/4)).map (fun j => (b*len/2+j,b*len/2+j+len/4)))) st) st
 st.code ++ (List.range 8).map (fun j => Instr.strq st.regs[j]! .x0 (16*j)) ++
 [.addImm .x .x0 .x0 128,.addImm .x .x1 .x1 480,.subImm .x .x11 .x11 1]
def finalRoot (idx : Nat) : List Instr :=
 let i := 7-idx
 [.vop (.dupE .s4 .v20 (if i<4 then .v22 else .v23) (i%4)),
  .vop (.dupE .s4 .v21 (if i<4 then .v28 else .v29) (i%4))]

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

def core : Prog isa :=
 .seq (.block (movW .x9 8380417 ++ [.vop (.dup .s4 .v31 .x9),mov .x3 .x1,
  .addImm .x .x4 .x1 512,.addImm .x .x5 .x1 768,.addImm .x .x6 .x1 896,.addImm .x .x7 .x1 960,.movz .x .x11 8 0])) <|
 .seq (.loop (.block firstBlock) (.nonzero .x .x11)) <|
 .seq (.block ([.subImm .x .x0 .x0 1024,mov .x2 .x0,.movz .x .x12 8 0,
  .ldrq .v22 .x1 0,.ldrq .v23 .x1 16,.ldrq .v28 .x1 32,.ldrq .v29 .x1 48] ++
  cv .v30 [16382,bar 16382,(z 1*16382)%8380417,bar ((z 1*16382)%8380417)]))
 (.loop (.block finalBody) (.nonzero .x .x12))


def expandedVals : List Nat :=
 let first := (List.range 8).flatMap fun block =>
  [1,2,4,8,16].flatMap fun len =>
   (List.range (if len<4 then 4 else 16/len)).flatMap fun g =>
    let idx := 256/len-1-(32*block)/(2*len)-(if len=1 then 4*g else if len=2 then 2*g else g)
    let zs := if len=1 then (List.range 4).map fun j => z (idx-j)
     else if len=2 then [z idx,z idx,z (idx-1),z (idx-1)]
     else List.replicate 4 (z idx)
    zs ++ zs.map bar
 let last := (List.range 8).map fun j => z (7-j)
 first ++ last ++ last.map bar
def expandedWords : List (BitVec 64) :=
 (List.range (expandedVals.length/2)).map fun j => BitVec.ofNat 64 (expandedVals[2*j]!+2^32*expandedVals[2*j+1]!)
def staticCode : Prog isa := .seq (.block [.adrSym .x1 "VG_MLDSA_INV_FOLDED"]) core

end VG.Impl.MlDsa.AArch64.Optimized.Inverse
