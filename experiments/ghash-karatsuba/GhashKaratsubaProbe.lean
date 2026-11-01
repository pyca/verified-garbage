import VerifiedGarbage.Impl.Gcm.PPC64LE.Vpmsum
import VerifiedGarbage.TCB.PPC64LE.Print
open VG VG.PPC64LE
open VG.Impl.Gcm.PPC64LE.Vpmsum
namespace Karatsuba
-- Form each pair's two products and their Karatsuba cross product.
def products (loKey hiKey : VReg) : List Instr :=
 [.vop (.sldoi HI HI HI 8), .vop (.sldoi U A HI 8),
  .vop (.sldoi T HI A 8), .vop (.sldoi T T T 8),
  .vop (.logic .xor A U T), .vop (.logic .xor HI loKey hiKey),
  .vop (.pmsumd MID A HI), .vop (.pmsumd HI U hiKey), .vop (.pmsumd LO T loKey),
  .vop (.logic .xor MID MID HI), .vop (.logic .xor MID MID LO)]

def pair (j : Nat) : List Instr := packedRead j ++ products (keyLow j) (keyHigh j) ++ packedSave j

def body : List Instr := (List.range 4).flatMap pair ++ reduce Y ++ [.subi .r6 .r6 8]

def bulk : Prog isa := .seq (.block (preparePowers 8 ++ packedKeys))
 (.seq (.loop (.block (body ++ [.lsr .d .r10 .r6 3])) (.nonzero .d .r10))
  (.block [.vop (.sldoi A (keyLow 3) (keyLow 3) 8), .vop (.sldoi H (keyHigh 3) A 8)]))

def ghash : Prog isa := .ite (.zero .d .r6) (.block [])
 (.seq (.block (prologue ++ [.lsr .d .r10 .r6 4]))
  (.seq (.ite (.zero .d .r10) (.block []) bulk) VG.Impl.Gcm.PPC64LE.Vpmsum.finish))
end Karatsuba

def main : IO Unit := do
 let mut asm := ".text\n.abiversion 2\n.globl gh_karatsuba\n.type gh_karatsuba,@function\ngh_karatsuba:\n"
 for line in printer.function Karatsuba.ghash do
  match line with
  | .text x => asm := asm ++ x ++ "\n"
  | _ => throw (IO.userError "unexpected symbol")
 IO.FS.writeFile "/workspace/scratch/ghash-karatsuba.s" asm
