import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.ExpandMask
import VerifiedGarbage.Variants.Keccak.AArch64.Sha3
import VerifiedGarbage.Impl.MlDsa.AArch64.Pack.Encode
import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.TCB.AArch64.Print
open VG VG.AArch64
open VG.Impl.MlKem.AArch64 (movImm mov)
namespace WindowUnpack
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


namespace CombSingleMask
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlKem.AArch64 (mov)
def parse (c : Nat) : Prog isa :=
 .seq (.block [.addImm .x .x0 .x25 840,mov .x4 .x26]) (WindowUnpack.unpack c)
def tail (c : VG.Impl.Sha3.AArch64.Callee) : Prog isa :=
 .seq (spongeWith c 136 640) <|
 .seq (.seq (.block [.lsr .x .x9 .x27 18]) (.ite (.zero .x .x9) (parse 18) (parse 20))) (.block epi)
def code (c : VG.Impl.Sha3.AArch64.Callee) : Prog isa :=
 .seq (.block (pro .x3 .x2 (.addImm .w .x27 .x1 0) (.movz .x .x4 66 0))) (tail c)
end CombSingleMask


namespace CombResidentMask
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlKem.AArch64 (mov)
def save : List Instr := (List.range 8).map (fun i => .strq (vreg (8+i)) .x25 (16*i))
def restore : List Instr := (List.range 8).map (fun i => .ldrq (vreg (8+i)) .x25 (16*i))
def first : List Instr :=
 (List.range 4).flatMap (fun i => [.ldrq (vreg (2*i)) .x0 (16*i),
 .vop (.ext (vreg (2*i+1)) (vreg (2*i)) (vreg (2*i)) 8)]) ++
 [.ldrb .x6 .x0 64,.ldrb .x7 .x0 65,.lsl .x .x7 .x7 8,.add .x .x6 .x6 .x7,
 .movz .x .x7 31 1,.add .x .x6 .x6 .x7,.vop (.dup .d2 .v8 .x6)] ++
 (List.range 7).map (fun i => .vop (.movi0 (vreg (9+i)))) ++
 [.movz .x .x6 0x8000 3,.vop (.dup .d2 .v16 .x6)] ++
 (List.range 8).map (fun i => .vop (.movi0 (vreg (17+i))))
def output (n : Nat) : List Instr :=
 (List.range (n/16)).flatMap (fun i => [.vop (.perm .zip1 .d2 .v25 (vreg (2*i)) (vreg (2*i+1))),.strq .v25 .x5 (16*i)]) ++
 (if n%16=8 then [.umov .x .x6 (vreg (n/8-1)) 0,.str .x .x6 .x5 (n-8)] else [])
def code : Prog isa :=
 .seq (.block (pro .x3 .x2 (.addImm .w .x27 .x1 0) (.movz .x .x4 66 0) ++ save ++ first ++
 [.addImm .x .x5 .x25 840,.movz .x .x4 4 0])) <|
 .seq (.loop (.block (rounds ++ output 136 ++ [.addImm .x .x5 .x5 136,.subImm .x .x4 .x4 1])) (.nonzero .x .x4)) <|
 .seq (.block (rounds ++ output 96 ++ [.lsr .x .x9 .x27 18])) <|
 .seq (.ite (.zero .x .x9) (CombSingleMask.parse 18) (CombSingleMask.parse 20)) (.block (restore ++ epi))
end CombResidentMask

def main : IO Unit := do
 IO.FS.writeFile "/tmp/comb-singlemask-resident_sha3.body" (String.join ((printer.function CombResidentMask.code).map (Rust.line printer.call)))
