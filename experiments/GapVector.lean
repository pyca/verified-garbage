-- UNPROVED prototype; requires FEAT_SHA3. Only run on hosts checked to support it.
-- Every instruction and the feature directive come from the existing Lean ISA/printer.
import VerifiedGarbage.Artifacts.TripleDesCbc.AArch64
import VerifiedGarbage.TCB.Rust
open VG VG.AArch64
namespace GapVector
open VG.Impl.CmacTripleDes.AArch64

def vecSaved : List VReg := [.v8,.v9,.v10,.v11,.v12,.v13,.v14]
def saveVec : List Instr := vecSaved.zipIdx.map fun (v,i) => .strq v .x15 (464+16*i)
def restoreVec : List Instr := vecSaved.zipIdx.map fun (v,i) => .ldrq v .x15 (464+16*i)

def complements : List Instr := pGroups.zipIdx.flatMap fun (g,k) =>
  movImm (maskReg k) (g.2 ^^^ (2^64-1))

def input (b : VReg) (down : Bool) : List Instr :=
  [.ldr .x .x5 .x10 0, if down then .subImm .x .x10 .x10 8 else .addImm .x .x10 .x10 8,
   .vop (.dup .d2 .v0 .x5), .vop (.logic .eor .v0 .v0 b),
   .vop (.logic .eor .v1 .v0 .v4), .vop (.logic .eor .v2 .v0 .v5), .vop (.logic .eor .v3 .v0 .v6)]

def output : List Instr := (VG.Impl.Tbl.AArch64.select true)

def groupsVec (dst initial : VReg) (gs : List (Nat × Reg)) : List Instr :=
  gs.zipIdx.flatMap fun ((r,m),i) =>
    [.vop (.dup .d2 .v13 m), .vop (.xar .v14 .v0 .v9 r),
     .vop (.bcax dst (if i == 0 then initial else dst) .v14 .v13)]

def round (a b : VReg) (down : Bool) : List Instr := input b down ++ output ++
  groupsVec .v10 .v9 (pGroupsR.take 4) ++
  groupsVec .v11 .v9 ((pGroupsR.drop 4).take 4) ++
  groupsVec .v12 a (pGroupsR.drop 8) ++ [.vop (.eor3 a .v10 .v11 .v12)]

def pass (down : Bool) : Prog isa :=
  .seq (.block [.movz .x .x16 8 0]) <|
    .loop (.block (round .v7 .v8 down ++ round .v8 .v7 down ++ [.subImm .x .x16 .x16 1])) (.nonzero .x .x16)

def tail (d : Nat) : List Instr :=
  [.addImm .x .x10 .x10 d, .vop (.logic .orr .v10 .v7 .v7),
   .vop (.logic .orr .v7 .v8 .v8), .vop (.logic .orr .v8 .v10 .v10)]

def enc : Prog isa :=
  .seq (.block (ipCode ++ [mov .x10 .x15, .vop (.dup .d2 .v7 .x11), .vop (.dup .d2 .v8 .x12), .vop (.logic .eor .v9 .v9 .v9)])) <|
  .seq (.seq (pass false) (.block (tail 120))) <|
  .seq (.seq (pass true) (.block (tail 136))) <|
  .seq (pass false) (.block ([.umov .x .x11 .v7 0, .umov .x .x12 .v8 0] ++ fpCode))

def candidate : Prog isa :=
  .seq (.block [mov .x14 .x0, mov .x15 .x4]) <|
  .ite (.zero .x .x3) (.block []) <|
  .seq (.block saveVec) <| .seq prep <| .seq (.block complements) <|
  .seq (.loop (.seq (.block chainIn) (.seq enc (.block Impl.TripleDes.AArch64.TablesCbc.store))) (.nonzero .x .x3))
    (.block (blockRestore ++ restoreVec))

def main (args : List String) : IO Unit := do
  let src ← IO.FS.readFile "../src/asm/aarch64/triple_des_cbc.rs"
  let some a := Artifacts.TripleDesCbc.AArch64.artifacts.find? (·.name == "vg_triple_des_cbc_encrypt_chained")
    | throw <| IO.userError "Missing CBC"
  let old := Rust.function a (fun _ => "triple_des")
  let c := Impl.StackScratch.AArch64.withStackScratchWiped 576 .x4 72 candidate
  let lines := (target.printer.enableFeature "sha3").map Line.text ++ target.printer.function c
  let new := Rust.function.functionOf a lines (fun _ => "triple_des")
  unless (src.splitOn old).length == 2 do throw <| IO.userError "Cannot match CBC"
  IO.FS.writeFile (args.headD "../src/asm/aarch64/triple_des_cbc.rs") (src.replace old new)
end GapVector

def main := GapVector.main
