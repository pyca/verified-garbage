import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector
import VerifiedGarbage.Impl.MlDsa.AArch64.Call
import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.TCB.Rust
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
def main : IO Unit := do
 for (wlen,olen) in [(768,32),(768,48),(1024,64)] do
  WindowShared.emit ("/tmp/vg-window-shared-commit"++toString olen++".body") (CommitHash.hash wlen olen)
 IO.FS.writeFile "/tmp/vg-window-shared-resident.body" (String.join ((printer.function WindowShared.resident).map (Rust.line printer.call)))
