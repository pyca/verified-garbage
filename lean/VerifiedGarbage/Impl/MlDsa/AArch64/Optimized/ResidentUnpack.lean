import VerifiedGarbage.Impl.MlDsa.AArch64.Pack.Stream

namespace VG.Impl.MlDsa.AArch64.Optimized.ResidentMask.Unpack
open VG VG.AArch64
open VG.Impl.MlKem.AArch64 (movImm mov)
open VG.Impl.MlDsa.AArch64.Pack

def vector (r : VReg) (vals : List Nat) : List Instr :=
 movImm .x9 (BitVec.ofNat 64 vals[0]!) ++ ([.vop (.dup .s4 r .x9)] : List Instr) ++
 ((List.range 3).flatMap fun i => movImm .x9 (BitVec.ofNat 64 vals[i+1]!) ++ ([.vop (.ins .s4 r (i+1) .x9)] : List Instr))
def byteIndices (r : VReg) (xs : List Nat) : List Instr :=
 let lo := ((List.range 8).map fun i => xs[i]! * 2^(8*i)).foldl (·+·) 0
 let hi := ((List.range 8).map fun i => xs[i+8]! * 2^(8*i)).foldl (·+·) 0
 movImm .x9 (BitVec.ofNat 64 lo) ++ ([.vop (.dup .d2 r .x9)] : List Instr) ++
 movImm .x9 (BitVec.ofNat 64 hi) ++ ([.vop (.ins .d2 r 1 .x9)] : List Instr)
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
  vector .v21 [2^(d-1),2^(d-1),2^(d-1),2^(d-1)]) ++ ([.movz .x .x11 16 0] : List Instr)
def one (d i : Nat) : List Instr :=
 let r := outRegs[i]!
 ([.vop (.tblN false (if d=10 then 2 else 3) r .v0 idxRegs[i]!),
  .vop (.mul r r .v23),.vop (.shift .ushr .s4 r r (if d=20 then 4 else 6)),
  .vop (.logic .and r r .v22)] : List Instr) ++
 (if d=10 then [.vop (.shift .shl .s4 r r 13)] else
  [.vop (.sub .s4 r .v21 r),.vop (.shift .sshr .s4 .v24 r 31),
   .vop (.logic .and .v24 .v24 .v20),.vop (.add .s4 r r .v24)]) ++ ([.strq r .x4 (16*i)] : List Instr)
def body (d : Nat) : List Instr :=
 ([.ldrq .v0 .x0 0] : List Instr) ++
 (if d=10 then [.addImm .x .x9 .x0 4,.ldrq .v1 .x9 0]
  else [.ldrq .v1 .x0 16,.addImm .x .x9 .x0 (2*d-16),.ldrq .v2 .x9 0]) ++
 (List.range 4).flatMap (one d) ++
 ([.addImm .x .x0 .x0 (2*d),.addImm .x .x4 .x4 64,.subImm .x .x11 .x11 1] : List Instr)
end VG.Impl.MlDsa.AArch64.Optimized.ResidentMask.Unpack
