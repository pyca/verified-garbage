import VerifiedGarbage.Impl.Aes.PPC64LE.Crypto
import VerifiedGarbage.TCB.PPC64LE.Print
open VG VG.PPC64LE
open VG.Impl.Aes.PPC64LE.Crypto
namespace WideReuse
abbrev key : VReg := .v8
abbrev increment : VReg := .v9
abbrev base : VReg := .v18

def reg : Nat → VReg
 | 0 => .v0 | 1 => .v1 | 2 => .v2 | 3 => .v3
 | 4 => .v4 | 5 => .v5 | 6 => .v6 | 7 => .v7
 | 8 => .v10 | 9 => .v11 | 10 => .v12 | 11 => .v13
 | 12 => .v14 | 13 => .v15 | 14 => .v16 | _ => .v17

def rs : List VReg := (List.range 16).map reg

def counters : List Instr :=
 [.vop (.logic .xor .v0 .v0 .v0), .li .r11 0, .li .r12 1] ++
 VG.Impl.Vector.PPC64LE.pair increment .v1 .v0 .r11 .r12 ++
 [.vop (.add false key increment increment), .vop (.logic .or .v0 base base),
 .vop (.add false .v1 base increment)] ++
 (List.range 14).map (fun i => .vop (.add false (reg (i+2)) (reg i) key)) ++
 [.vop (.add false base (reg 14) key), .addi .r8 .r8 16]

def group : Prog isa := .seq (.block counters)
 (.seq (VG.Impl.Aes.PPC64LE.Crypto.aes false rs)
  (.block (rs.flatMap (writeBlock true) ++ [.subi .r7 .r7 16])))

def ctr32 : Prog isa := .ite (.zero .d .r7) (.block [])
 (.seq (.block (setup ++ [.li .r11 12,.loadRev .w .r8 .r5 .r11] ++ load base .r5 ++ [.lsr .d .r12 .r7 4]))
 (.seq (.ite (.zero .d .r12) (.block [])
  (.loop (.seq group (.block [.lsr .d .r12 .r7 4])) (.nonzero .d .r12)))
 (.seq (.ite (.zero .d .r7) (.block [])
  (.seq (.block (setMask counterMask counterControl ++ load counterBase .r5)) (batches false true)))
 (.block [.li .r11 12,.storeRev .w .r8 .r5 .r11]))))
end WideReuse

def main : IO Unit := do
 let mut asm := ".text\n.abiversion 2\n"
 for (name,code) in [("ctr_reuse",WideReuse.ctr32)] do
  asm := asm ++ s!".globl {name}\n.type {name},@function\n{name}:\n"
  for line in printer.function code do
   match line with
   | .text x => asm := asm ++ x ++ "\n"
   | _ => throw (IO.userError "unexpected symbol")
 IO.FS.writeFile "/workspace/scratch/aes-ctr-reuse.s" asm
