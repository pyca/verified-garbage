import VerifiedGarbage.Impl.Aes.PPC64LE.Crypto
import VerifiedGarbage.TCB.PPC64LE.Print
open VG VG.PPC64LE
open VG.Impl.Aes.PPC64LE.Crypto
namespace Probe
-- Offset k occupies the last 32-bit lane; vector addition wraps that lane.
def offset : Nat → VReg
 | 1 => .v11 | 2 => .v12 | 3 => .v13 | 4 => .v14
 | 5 => .v15 | 6 => .v16 | 7 => .v17 | _ => .v18

def offsets : List Instr :=
  setMask (offset 1) 1 ++ (List.range 7).map (fun i =>
    .vop (.add false (offset (i+2)) (offset (i+1)) (offset 1)))

def counters (count : Nat) : List Instr :=
  (List.range count).map (fun i => if i = 0 then
      .vop (.logic .or (breg i) counterBase counterBase)
    else .vop (.add false (breg i) counterBase (offset i))) ++
  [.vop (.add false counterBase counterBase (offset count)), .addi .r8 .r8 count]

def group (count : Nat) : Prog isa :=
  let rs := batchRegs count
  .seq (.block (counters count))
    (.seq (aes false rs)
      (.block (rs.flatMap (writeBlock true) ++ [.subi .r7 .r7 rs.length])))

def batches : Prog isa :=
  .seq (.block [.lsr .d .r12 .r7 3])
    (.seq (.ite (.zero .d .r12) (.block [])
        (.loop (.seq (group 8) (.block [.lsr .d .r12 .r7 3])) (.nonzero .d .r12)))
      (.ite (.zero .d .r7) (.block []) (.loop (group 1) (.nonzero .d .r7))))

def ctr32 : Prog isa :=
  .ite (.zero .d .r7) (.block [])
    (.seq (.block (setup ++ offsets ++
      [.li .r11 12, .loadRev .w .r8 .r5 .r11] ++ load counterBase .r5))
      (.seq batches (.block [.storeRev .w .r8 .r5 .r11])))
end Probe

def main : IO Unit := do
  let mut asm := ".text\n.abiversion 2\n"
  for (name, code) in [("ctr_base", VG.Impl.Aes.PPC64LE.Crypto.ctr32), ("ctr_batch", Probe.ctr32)] do
    asm := asm ++ s!".globl {name}\n.type {name},@function\n{name}:\n"
    for line in printer.function code do
      match line with
      | .text x => asm := asm ++ x ++ "\n"
      | _ => throw (IO.userError "unexpected symbol")
  IO.FS.writeFile "/workspace/scratch/aes-ctr-batch.s" asm
