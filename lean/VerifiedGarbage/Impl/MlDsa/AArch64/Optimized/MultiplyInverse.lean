import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ProductBank

namespace VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith
open VG.Impl.MlKem.AArch64 (mov)
open VG.Impl.MlDsa.AArch64.Optimized Inverse

def firstBlock : List Instr :=
 let ld := inverseProductLoads
 let packedCode := [1,2].flatMap (fun len => (List.range 4).flatMap (fun j => rootAt (if len=1 then .x3 else .x4) (16*j/len) len ++ packed (vr (2*j)) (vr (2*j+1)) len))
 let st : CS := {code := ld++packedCode}
 let st := [4,8,16].foldl (fun st len => (List.range (16/len)).foldl (fun st b =>
   batch {st with code := st.code++rootAt (if len=4 then .x5 else if len=8 then .x6 else .x7) (4*b) len}
    ((List.range (len/4)).map (fun j => (b*len/2+j,b*len/2+j+len/4)))) st) st
 st.code ++ (List.range 8).map (fun j => Instr.strq st.regs[j]! .x0 (16*j)) ++
 [.addImm .x .x13 .x13 128,.addImm .x .x14 .x14 128,.addImm .x .x0 .x0 128,.addImm .x .x1 .x1 480,.subImm .x .x11 .x11 1]
def rawFinalBody : List Instr :=
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

def core (raw : Bool) : Prog isa :=
 .seq (.block (movW .x10 4236238847 ++ [.vop (.dup .s4 .v30 .x10)] ++ movW .x9 8380417 ++ [.vop (.dup .s4 .v31 .x9),mov .x3 .x1,
  .addImm .x .x4 .x1 512,.addImm .x .x5 .x1 768,.addImm .x .x6 .x1 896,.addImm .x .x7 .x1 960,.movz .x .x11 8 0])) <|
 .seq (.loop (.block firstBlock) (.nonzero .x .x11)) <|
 .seq (.block ([.subImm .x .x0 .x0 1024,mov .x2 .x0,.movz .x .x12 8 0,
  .ldrq .v22 .x1 0,.ldrq .v23 .x1 16,.ldrq .v28 .x1 32,.ldrq .v29 .x1 48] ++
  cv .v30 [16382,bar 16382,(z 1*16382)%8380417,bar ((z 1*16382)%8380417)]))
 (.loop (.block (if raw then rawFinalBody else Inverse.finalBody)) (.nonzero .x .x12))

def staticCode (raw : Bool) : Prog isa :=
  .seq (.block [mov .x13 .x1,mov .x14 .x2,.adrSym .x1 "VG_MLDSA_INV_FOLDED"]) (core raw)

end VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse
