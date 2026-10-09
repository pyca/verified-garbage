import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Vec
import VerifiedGarbage.Spec.MlDsa
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Arithmetic

namespace VG.Impl.MlDsa.AArch64.Optimized.Ntt
open VG VG.AArch64
open VG.Impl.MlKem.AArch64 (mov)
open VG.Impl.MlDsa.AArch64.Arith (movW)
open VG.Impl.MlDsa.AArch64.Arith

def fastMul (d : VReg) : List Instr := Optimized.fastMul d .v4 .v18 .v19 .v16
def canon (d : VReg) : List Instr := Optimized.positive d .v4 .v16
def fastConsts : List Instr :=
 Neon.consts ++ movW .x9 2149582593 ++ [.vop (.dup .s4 .v20 .x9)]

def zetaTab (m : Nat) : Nat := 1753 ^ Spec.MlDsa.bitRev8 m % 8380417

def dataRegs : List VReg := [.v0,.v1,.v5,.v6,.v7,.v21,.v22,.v23]

def rootRegs : List VReg := [.v25,.v26,.v27,.v28]

def hoistedInit : List Instr := (List.range 4).map
 (fun i => .ldrq rootRegs[i]! .x1 (3840+16*i))

def hoistedRoot (i : Nat) : List Instr :=
 [.vop (.dupE .s4 .v18 rootRegs[(i-1)/2]! (2*((i-1)%2))),
  .vop (.dupE .s4 .v19 rootRegs[(i-1)/2]! (2*((i-1)%2)+1))]

def rootAt (base : Reg) (i : Nat) : List Instr :=
 [.ldrq .v18 base (32*i),.ldrq .v19 base (32*i+16)]

def packedAt (base : Reg) (len i : Nat) : List Instr :=
 let j := if len=2 then i/2 else i/4
 [.ldrq .v18 base (32*j),.ldrq .v19 base (32*j+16)]

structure Ren where
 code : List Instr := []
 data : Vector VReg 8 := ⟨#[.v0,.v1,.v5,.v6,.v7,.v21,.v22,.v23], rfl⟩
 free : VReg := .v24

def prodTemps : List VReg := [.v4,.v29,.v30,.v31]

def pairCode (r : Ren) (i j : Nat) : List Instr :=
 [.vop (.sub .s4 r.free r.data[i]! r.data[j]!),
  .vop (.add .s4 r.data[i]! r.data[i]! r.data[j]!)]

def renamePair (r : Ren) (i j : Nat) : Ren :=
 { code := r.code ++ pairCode r i j
   data := r.data.set! j r.free
   free := r.data[j]! }

def renGroup (r : Ren) (gap group : Nat) (roots : List Instr) : Ren :=
 let bs := (List.range gap).map fun j => r.data[2*gap*group+j+gap]!
 let ops := ((bs.zipIdx).map fun (b,i) => .vop (.sqdmulh prodTemps[i]! b .v19)) ++
  (bs.map fun b => .vop (.mul b b .v18)) ++
  ((bs.zipIdx).map fun (b,i) => .vop (.mls b prodTemps[i]! .v16))
 (List.range gap).foldl (fun st j => renamePair st (2*gap*group+j) (2*gap*group+j+gap))
   {r with code := r.code ++ roots ++ ops}

def renThree (outer : Bool)  : Ren :=
 ([4,2,1] : List Nat).foldl (fun st gap =>
  (List.range (4/gap)).foldl (fun st g =>
   let rs := if outer then hoistedRoot (4/gap+g)
    else rootAt (if gap=4 then .x3 else if gap=2 then .x4 else .x5) g
   renGroup st gap g rs) st) {}

def outerRenamed : Prog isa :=
 let r := renThree true
 .seq (.block ([mov .x2 .x0,.movz .x .x5 8 0] ++ hoistedInit)) <|
 .loop (.block (
  (dataRegs.zipIdx.flatMap fun (v,i) => [.ldrq v .x2 (128*i)]) ++ r.code ++
  (r.data.toList.zipIdx.flatMap fun (v,i) => [.strq v .x2 (128*i)]) ++
  [.addImm .x .x2 .x2 16,.subImm .x .x5 .x5 1])) (.nonzero .x .x5)

def renInnerPair (a b tmp : VReg) (len : Nat) : List Instr :=
 [ .vop (.perm (if len=2 then .trn1 else .uzp1) (if len=2 then .d2 else .s4) .v25 a b),
   .vop (.perm (if len=2 then .trn2 else .uzp2) (if len=2 then .d2 else .s4) .v26 a b)] ++ fastMul .v26 ++
 [.vop (.sub .s4 tmp .v25 .v26),.vop (.add .s4 .v25 .v25 .v26),
  .vop (.perm (if len=2 then .trn1 else .zip1) (if len=2 then .d2 else .s4) a .v25 tmp),
  .vop (.perm (if len=2 then .trn2 else .zip2) (if len=2 then .d2 else .s4) b .v25 tmp)]

def renFiveBody  : List Instr :=
 let r := renThree false
 (dataRegs.zipIdx.flatMap fun (v,i) => [.ldrq v .x2 (16*i)]) ++ r.code ++
 ((List.range 4).flatMap fun j =>
   packedAt .x7 2 (2*j) ++
    renInnerPair r.data[2*j]! r.data[2*j+1]! r.free 2 ++
   packedAt .x8 1 (4*j) ++
    renInnerPair r.data[2*j]! r.data[2*j+1]! r.free 1) ++
 (r.data.toList.flatMap fun v => canon v) ++
 (r.data.toList.zipIdx.flatMap fun (v,i) => [.strq v .x2 (16*i)]) ++ [.addImm .x .x2 .x2 128]

def renFive  : Prog isa :=
  .seq (.block [mov .x2 .x0,mov .x3 .x1,.addImm .x .x4 .x1 32,.addImm .x .x5 .x1 96,
   .addImm .x .x7 .x1 224,.addImm .x .x8 .x1 352,.movz .x .x10 8 0])
  (.loop (.block (renFiveBody ++ [.addImm .x .x3 .x3 480,.addImm .x .x4 .x4 480,
   .addImm .x .x5 .x5 480,.addImm .x .x7 .x7 480,.addImm .x .x8 .x8 480,.subImm .x .x10 .x10 1])) (.nonzero .x .x10))

def renamedNtt  : Prog isa :=
 .seq (.block fastConsts) (.seq outerRenamed (renFive))

def expandedVals : List Nat :=
 let bar := fun z => z*2^31/8380417
 let first := (List.range 8).flatMap fun block =>
  ([16,8,4,2,1] : List Nat).flatMap fun len =>
   (List.range (if len<4 then 4 else 16/len)).flatMap fun g =>
    let idx := 128/len+32*block/(2*len)+(if len=2 then 2*g else if len=1 then 4*g else g)
    let zs := if len=1 then (List.range 4).map (fun j => zetaTab (idx+j))
     else if len=2 then [zetaTab idx,zetaTab idx,zetaTab (idx+1),zetaTab (idx+1)]
     else List.replicate 4 (zetaTab idx)
    zs++zs.map bar
 first ++ (List.range 8).flatMap (fun i => let z := zetaTab (i+1); [z,bar z])
def staticNttWords : List (BitVec 64) := (List.range (expandedVals.length/2)).map
 (fun i => BitVec.ofNat 64 (expandedVals[2*i]!+2^32*expandedVals[2*i+1]!))
def staticNtt : Prog isa := .seq (.block [.adrSym .x1 "VG_MLDSA_NTT_EXPANDED"])
 (renamedNtt)

def outerOut : Prog isa :=
 let r := renThree true
 .seq (.block ([mov .x2 .x0,.movz .x .x5 8 0] ++ hoistedInit)) <|
 .loop (.block (
  (dataRegs.zipIdx.flatMap fun (v,i) => [.ldrq v .x11 (128*i)]) ++ r.code ++
  (r.data.toList.zipIdx.flatMap fun (v,i) => [.strq v .x2 (128*i)]) ++
  [.addImm .x .x2 .x2 16,.addImm .x .x11 .x11 16,.subImm .x .x5 .x5 1])) (.nonzero .x .x5)

def outNtt : Prog isa :=
 .seq (.block [.addImm .x .x11 .x1 0,.adrSym .x1 "VG_MLDSA_NTT_EXPANDED"])
 (.seq (.block fastConsts) (.seq outerOut renFive))

end VG.Impl.MlDsa.AArch64.Optimized.Ntt
