-- Unproved prototype: compact fixed IP/FP networks. No Artifact is constructed.
import VerifiedGarbage.Artifacts.TripleDesCbc.AArch64
import VerifiedGarbage.Impl.CmacTripleDes.AArch64
import VerifiedGarbage.TCB.Rust
open VG VG.AArch64
namespace GapPermutations
open VG.Impl.CmacTripleDes.AArch64

def swaps : List (Nat × Nat) := [(0,3),(1,4),(2,5),(3,4),(4,5)]
def swapMask (a b : Nat) : Nat := (List.range 64).foldl (fun v i =>
  if i.testBit a && !i.testBit b then v ||| (1 <<< i) else v) 0

def swap (a b : Nat) : List Instr :=
  let sh := 2^b-2^a
  movImm .x7 (swapMask a b) ++
  [.logicRor .eor .x .x6 .x5 .x5 sh, .logic .and .x .x6 .x6 .x7,
   .ror .x .x7 .x6 (64-sh), .logic .eor .x .x5 .x5 .x6, .logic .eor .x .x5 .x5 .x7]

def ipNet : List Instr := [.rev .x5 .x5] ++ swaps.flatMap (fun (a,b) => swap a b) ++ [.ror .x .x5 .x5 32]
def fpNetTail : List Instr := swaps.reverse.flatMap (fun (a,b) => swap a b) ++ [.rev .x5 .x5]

def spreadHalf (r : Reg) : List Instr :=
  [.ror .w r r (32-rot), .ror .w .x6 r 4, .lsl .x .x6 .x6 32,
   .logic .eor .x r r .x6, .logic .and .x r r .x7]

def ip : List Instr := ipNet ++ [.lsr .x .x11 .x5 32, .addImm .w .x12 .x5 0] ++
  movImm .x7 0x3f3f3f3f3f3f3f3f ++ spreadHalf .x11 ++ spreadHalf .x12

def unspread (src dst : Reg) : List Instr :=
  [.lsr .x .x6 src 28, .logic .and .x .x6 .x6 .x7, .addImm .w dst src 0,
   .logic .eor .x dst dst .x6, .ror .w dst dst rot]

def fp : List Instr := movImm .x7 0xc0c0c0c0 ++ unspread .x12 .x5 ++ unspread .x11 .x9 ++
  [.lsl .x .x9 .x9 32, .logic .eor .x .x5 .x5 .x9] ++ fpNetTail

def fuse : List Instr → List Instr
  | (.ror sz t src sh) :: (.logic .and sz' d n mask) :: rest =>
    if sz == sz' && t == d && t == n && t != mask then
      .logicRor .and sz d mask src sh :: fuse rest
    else .ror sz t src sh :: fuse (.logic .and sz' d n mask :: rest)
  | i :: rest => i :: fuse rest
  | [] => []
termination_by is => is.length

def roundOnly (is : List Instr) : List Instr :=
  if is.contains (.subImm .x .x16 .x16 1) then fuse is else is

def replace (is : List Instr) : List Instr :=
  if ipCode.isPrefixOf is then ip ++ is.drop ipCode.length
  else if fpCode.isPrefixOf is then fp ++ is.drop fpCode.length else is

def mapCode : Prog isa → Prog isa
  | .block is => .block (replace is)
  | .seq a b => .seq (mapCode a) (mapCode b)
  | .ite c a b => .ite c (mapCode a) (mapCode b)
  | .loop a c => .loop (mapCode a) c
  | .call n a => .call n (mapCode a)
  | .frame i a j => .frame i (mapCode a) j

def main (_ : List String) : IO Unit := do
  let src ← IO.FS.readFile "../src/asm/aarch64/triple_des_cbc.rs"
  let some a := Artifacts.TripleDesCbc.AArch64.artifacts.find? (·.name == "vg_triple_des_cbc_encrypt_chained")
    | throw <| IO.userError "Missing CBC"
  let old := Rust.function a (fun _ => "triple_des")
  let code := Impl.StackScratch.AArch64.withStackScratchWiped 464 .x4 58 Impl.TripleDes.AArch64.TablesCbc.encrypt
  let mode := "perm-round"
  let code := if mode == "round" then code else mapCode code
  let rec transform : Prog isa → Prog isa
    | .block is => .block (roundOnly is)
    | .seq a b => .seq (transform a) (transform b)
    | .ite c a b => .ite c (transform a) (transform b)
    | .loop a c => .loop (transform a) c
    | .call n a => .call n (transform a)
    | .frame i a j => .frame i (transform a) j
  let new := Rust.function.functionOf a (target.printer.function (transform code)) (fun _ => "triple_des")
  unless (src.splitOn old).length == 2 do throw <| IO.userError "Cannot match CBC"
  IO.FS.writeFile "../src/asm/aarch64/triple_des_cbc.rs" (src.replace old new)
  IO.println s!"IP {ipCode.length}->{ip.length}; FP {fpCode.length}->{fp.length}"
end GapPermutations

def main := GapPermutations.main
