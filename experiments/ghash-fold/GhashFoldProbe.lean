import VerifiedGarbage.Impl.Gcm.PPC64LE.Vpmsum
import VerifiedGarbage.TCB.PPC64LE.Print
open VG VG.PPC64LE
open VG.Impl.Gcm.PPC64LE.Vpmsum
namespace FoldProbe
-- H^j / x is stored in the same adjusted layout as the baseline H.
def power : Nat → VReg
 | 1 => H | 2 => .v8 | 3 => .v9 | 4 => .v10
 | 5 => .v11 | 6 => .v12 | 7 => .v13 | _ => .v14

def powers (n : Nat) : List Instr := (List.range (n-1)).flatMap fun i =>
  [.vop (.sldoi A (power (i+1)) (power (i+1)) 8)] ++
  mul (power (i+2)) A H ++
  [.vop (.sldoi (power (i+2)) (power (i+2)) (power (i+2)) 8)]

def accs : List (VReg × VReg) := [(Y,LO),(.v15,MID),(.v17,HI)]
def folded (n : Nat) : List Instr :=
  (List.range n).flatMap (fun i =>
    loadRev A .r5 ++ (if i=0 then [.vop (.logic .xor A A Y)] else []) ++
    products A (power (n-i)) ++
    (if i=0 then accs.map (fun (acc,p) => .vop (.logic .or acc p p))
     else if i+1=n then accs.map (fun (acc,p) => .vop (.logic .xor p p acc))
     else accs.map (fun (acc,p) => .vop (.logic .xor acc acc p))) ++
    [.addi .r5 .r5 16]) ++ reduce Y ++ [.subi .r6 .r6 n]

def ghash (n shift : Nat) : Prog isa :=
 .ite (.zero .d .r6) (.block [])
  (.seq (.block (prologue ++ [.lsr .d .r10 .r6 shift]))
   (.seq (.ite (.zero .d .r10) (.block [])
    (.seq (.block (powers n))
      (.loop (.block (folded n ++ [.lsr .d .r10 .r6 shift])) (.nonzero .d .r10))))
    (.seq (.ite (.zero .d .r6) (.block []) (.loop (.block body) (.nonzero .d .r6))) (.block epilogue))))
end FoldProbe

def main : IO Unit := do
 let mut asm := ".text\n.abiversion 2\n"
 for (name,code) in [("gh_base",VG.Impl.Gcm.PPC64LE.Vpmsum.ghash),("gh_fold4",FoldProbe.ghash 4 2),("gh_fold8",FoldProbe.ghash 8 3)] do
  asm := asm ++ s!".globl {name}\n.type {name},@function\n{name}:\n"
  for line in printer.function code do
   match line with
   | .text x => asm := asm ++ x ++ "\n"
   | _ => throw (IO.userError "unexpected symbol")
 IO.FS.writeFile "/workspace/scratch/ghash-fold.s" asm
