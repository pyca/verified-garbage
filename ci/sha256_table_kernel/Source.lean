import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Impl.Sha256.PPC64LE
import VerifiedGarbage.Impl.Sha2.PPC64LE
open VG VG.PPC64LE
-- Unverified experiment; assembly comes from Lean's printer.
namespace Experiment

open VG.PPC64LE
open VG.Spec.Sha256 (K)

/-- The registers holding the working variables. -/
def work : List Reg := [.r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15]

/-- The register holding working variable `k` (`a = 0, …, h = 7`) at the start of round `t`. -/
def var (t k : Nat) : Reg := work.getD ((k + 8 - t % 8) % 8) .r7

/-- Volatile vector registers hold the working state throughout the rounds. -/
def vwork : List VReg := [.v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11]

def vvar (t k : Nat) : VReg := vwork.getD ((k + 8 - t % 8) % 8) .v4

/-- General-purpose temporaries for input loads and output updates. -/
def T0 : Reg := .r16
def T1 : Reg := .r17
def T2 : Reg := .r0
def T3 : Reg := .r19

/-- The nonvolatile registers used, in the order they are saved. -/
def saved (i : Nat) : Reg := [.r14, .r15, .r16, .r17, .r19].getD i .r14

/-- Save them in `scratch[128..168)`. -/
def save : List Instr := (List.range 5).flatMap fun i => [.store .d (saved i) .r6 (64 + 8 * i)]

/-- Restore them. -/
def restore : List Instr := (List.range 5).flatMap fun i => [.load .d (saved i) .r6 (64 + 8 * i)]

/-- The offset of `W[i mod 16]` in the scratch buffer. -/
def slot (i : Nat) : Nat := 8 * (i % 16)

def movImm32 (d : Reg) (v : BitVec 32) : List Instr :=
  [.lis d (v.extractLsb' 16 16), .ori d d (v.extractLsb' 0 16)]

export VG.Impl.Sha2.PPC64LE (pairs preg)

def schedulePair (n : Nat) : List Instr := VG.Impl.Sha2.PPC64LE.schedulePair false n

/-- The odd word was computed with its predecessor. -/
def schedule (t : Nat) : List Instr :=
  if t % 2 = 0 then schedulePair (t/2) ++ [.vop (.logic .or .v15 (preg (t/2)) (preg (t/2)))]
  else [.vop (.sldoi .v15 (preg (t/2)) (preg (t/2)) 8)]

/-- Bias the final working variable only while another round remains. -/
def roundBias (t : Nat) : Spec.Sha256.Word := if t < 64 then K t else 0

/-- Round constants, with two zero words for the last doubleword-pair load. -/
def kWords : List (BitVec 64) := Spec.Sha256.Ks.map (fun w => w.setWidth 64) ++ [0, 0]
def kSym : String := "VG_SHA512_PPC64LE_K"

/-- Byte offset of the next round constant. -/
def kIndex (t : Nat) : BitVec 64 := BitVec.ofNat 64 (8*(t+1))

/-- Round `t` starts with `h + Kₜ`. After choice consumes `g`, prepare it
as the next round's `h + Kₜ₊₁`, off the current round's sum chain. -/
def round (t : Nat) : List Instr :=
  let a := vvar t 0; let b := vvar t 1; let c := vvar t 2; let d := vvar t 3
  let e := vvar t 4; let f := vvar t 5; let g := vvar t 6; let h := vvar t 7
  [.lxvd2xTbl .v14 .r18 .r19 kSym kWords, .addi .r19 .r19 8,
   .vop (.sha256 .v12 e true 5), .vop (.sel .v13 g f e),
   .vop (.add false g g .v14), .vop (.sha256 .v14 a true 0),
   .vop (.add false .v15 h .v15), .vop (.add false .v15 .v15 .v13),
   .vop (.add false .v15 .v15 .v12), .vop (.add false d d .v15),
   .vop (.logic .xor .v12 a b), .vop (.sel .v12 b c .v12),
   .vop (.add false .v14 .v14 .v12), .vop (.add false h .v15 .v14)]

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (schedule n ++ round n))

def roundRange (start : Nat) : Nat → Prog isa
  | 0 => .block []
  | n+1 => .seq (roundRange start n) (.block (schedule (start+n) ++ round (start+n)))

def computedChunk : Prog isa := roundRange 16 16

def roundsLoop : Prog isa := .seq (rounds 16) (.seq (.block [.li .r14 3])
  (.loop (.seq computedChunk (.block [.subi .r14 .r14 1])) (.nonzero .d .r14)))

/-- Load the hash value (`64 % 8 = 0`, so the variables are in the same
registers after the 64 rounds). -/
def loadState : List Instr := (List.range 8).flatMap fun k =>
  [.load .w T1 .r3 (4 * k), .mtvsrd (vvar 0 k) T1]

/-- Start the first round with its constant already in `h`. -/
def load : List Instr := loadState ++ movImm32 T0 (roundBias 0) ++
  [.mtvsrd .v12 T0, .vop (.add false .v11 .v11 .v12), .li .r19 8]

/-- Add the hash value into the working variables (loading all of it before
storing any of it), and store the result. -/
def update : List Instr :=
  (List.range 8).map (fun k => .mfvsrd (var 0 k) (vvar 0 k)) ++
  (List.range 4).map (fun k => .load .w ([T0, T1, T2, T3].getD k T0) .r3 (4 * k)) ++
  (List.range 4).map (fun k => .add (var 0 k) (var 0 k) ([T0, T1, T2, T3].getD k T0)) ++
  (List.range 4).map (fun k => .load .w ([T0, T1, T2, T3].getD k T0) .r3 (4 * (k + 4))) ++
  (List.range 4).map (fun k => .add (var 0 (k + 4)) (var 0 (k + 4)) ([T0, T1, T2, T3].getD k T0)) ++
  (List.range 8).map (fun k => .store .w (var 0 k) .r3 (4 * k))

/-- Advance to the next block and decrement the count. -/
def advance : List Instr := [.addi .r4 .r4 64, .subi .r5 .r5 1]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq roundsLoop (.block (update ++ advance)))

/-- The blocks. -/
def blocks : Prog isa := .ite (.zero .d .r5) (.block []) (.loop body (.nonzero .d .r5))

def compressCore : Prog isa := .seq (.block save) (.seq blocks (.block restore))

-- Extra experimental table argument; not a production ABI.
def compress : Prog isa := .seq (.block [.store .d .r18 .r6 8, .logic .or .r18 .r7 .r7])
  (.seq compressCore (.block [.load .d .r18 .r6 8]))
end Experiment

def pushN (a : ByteArray) (n : Nat) (x : Nat) : ByteArray :=
  (List.range n).foldl (fun a j => a.push ((x / 256^j) % 256).toUInt8) a

def main : IO Unit := do
  let out := "/workspace/scratch/ppc64le-sha256-table-experiment/"
  let variants := [("scalar", Impl.Sha256.PPC64LE.compress), ("table_loop", Experiment.compress)]
  let mut asm := ".text\n.abiversion 2\n"
  for (name, code) in variants do
    asm := asm ++ s!".globl sha_{name}\n.type sha_{name},@function\nsha_{name}:\n"
    for line in printer.function code do
      match line with
      | .text x => asm := asm ++ x ++ "\n"
      | _ => throw (IO.userError "unexpected symbol")
  IO.FS.writeFile (out ++ "sha256-probe.s") asm
  let mut input := ByteArray.empty
  let mut expected := ByteArray.empty
  for c in List.range 32 do
    let n := c % 4
    let h : Spec.Sha256.HashValue := Vector.ofFn fun i =>
      BitVec.ofNat 32 (0x6a09e667 + 0x9e3779b9 * (i.val+c))
    let bytes : List Byte := (List.range (64*n)).map fun i => BitVec.ofNat 8 (17*i+3*c+49)
    input := pushN input 8 n
    for x in h.toList do input := pushN input 4 x.toNat
    input := bytes.foldl (fun a x => a.push x.toNat.toUInt8) input
    for x in (Spec.Sha256.compressList h bytes n).toList do expected := pushN expected 4 x.toNat
  IO.FS.writeBinFile (out ++ "input.bin") input
  IO.FS.writeBinFile (out ++ "expected.bin") expected
  let ks := Spec.Sha256.Ks.map fun x => s!"{x.toNat}ULL"
  let iv := Spec.Sha256.H0.toList.map fun x => s!"{x.toNat}U"
  IO.FS.writeFile (out ++ "constants.h")
    ("_Alignas(64) static const uint64_t kt[66] = {" ++ String.intercalate "," ks ++ ",0,0};\n" ++
     "static const uint32_t iv[8] = {" ++ String.intercalate "," iv ++ "};\n")
  IO.println "Generated unverified SHA-256 kernel experiment and 32 Spec-derived cases."
