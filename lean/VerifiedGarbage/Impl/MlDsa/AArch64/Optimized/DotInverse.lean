import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Dot

namespace VG.Impl.MlDsa.AArch64.Optimized.DotInverse
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith
open VG.Impl.MlKem.AArch64 (mov)
open Inverse

/-- The unchanged first five inverse layers, starting with eight resident vectors. -/
def firstArithmetic : List Instr :=
  let packedCode := [1,2].flatMap fun len => (List.range 4).flatMap fun j =>
    rootAt (if len=1 then .x3 else .x4) (16*j/len) len ++ packed (vr (2*j)) (vr (2*j+1)) len
  let st : CS := {code:=packedCode}
  let st := [4,8,16].foldl (fun st len => (List.range (16/len)).foldl (fun st b =>
    batch {st with code:=st.code++rootAt (if len=4 then .x5 else if len=8 then .x6 else .x7) (4*b) len}
      ((List.range (len/4)).map fun j => (b*len/2+j,b*len/2+j+len/4))) st) st
  st.code ++ (List.range 8).map fun j => Instr.strq st.regs[j]! .x0 (16*j)

def firstAdvance : List Instr :=
  [.addImm .x .x13 .x13 128,.addImm .x .x14 .x14 128,.addImm .x .x0 .x0 128,
   .addImm .x .x1 .x1 480,.subImm .x .x11 .x11 1]

def firstBlock (count : Nat) : List Instr :=
  inverseDotLoads count ++ firstArithmetic ++ firstAdvance

def setup : List Instr :=
  movW .x10 4236238847 ++ ([.vop (.dup .s4 .v30 .x10)] : List Instr) ++ movW .x9 8380417 ++
  ([.vop (.dup .s4 .v31 .x9),mov .x3 .x1,.addImm .x .x4 .x1 512,
   .addImm .x .x5 .x1 768,.addImm .x .x6 .x1 896,.addImm .x .x7 .x1 960,.movz .x .x11 8 0] : List Instr)

def finalSetup : List Instr :=
  ([.subImm .x .x0 .x0 1024,mov .x2 .x0,.movz .x .x12 8 0,
   .ldrq .v22 .x1 0,.ldrq .v23 .x1 16,.ldrq .v28 .x1 32,.ldrq .v29 .x1 48] : List Instr) ++
  cv .v30 [16382,bar 16382,(z 1*16382)%8380417,bar ((z 1*16382)%8380417)]

def core (count : Nat) : Prog isa :=
  .seq (.block setup) <| .seq (.loop (.block (firstBlock count)) (.nonzero .x .x11)) <|
    .seq (.block finalSetup) (.loop (.block Inverse.finalBody) (.nonzero .x .x12))

/-- dst, contiguous input families, unused scratch; the immutable folded table
and all arithmetic match the measured dot4/dot5/dot7 inverse helpers. -/
def staticCode (count : Nat) : Prog isa :=
  .seq (.block [mov .x13 .x1,mov .x14 .x2,.adrSym .x1 "VG_MLDSA_INV_FOLDED"]) (core count)

end VG.Impl.MlDsa.AArch64.Optimized.DotInverse
