import VerifiedGarbage.Impl.Aes.PPC64LE.Crypto
import VerifiedGarbage.Impl.Gcm.Clmul
import VerifiedGarbage.Impl.Vector.PPC64LE
import VerifiedGarbage.TCB.PPC64LE.Print
open VG VG.PPC64LE
open VG.Impl.Aes.PPC64LE.Crypto
namespace Fused
abbrev Y : VReg := .v10
abbrev C : VReg := .v13
abbrev A : VReg := .v9
abbrev U : VReg := .v17
abbrev T : VReg := .v18
abbrev LO : VReg := .v14
abbrev MID : VReg := .v15
abbrev HI : VReg := .v16
abbrev H1 : VReg := .v11
abbrev H2 : VReg := .v12

def products (a key zero : VReg) : List Instr :=
 [.vop (.sldoi U a zero 8), .vop (.pmsumd HI U key),
  .vop (.sldoi U zero a 8), .vop (.pmsumd LO U key), .vop (.pmsumd MID a key)]

def reduce (d zero : VReg) : List Instr :=
 [.vop (.sldoi T LO zero 8), .vop (.pmsumd T T C),
  .vop (.sldoi LO LO LO 8), .vop (.logic .xor MID MID LO), .vop (.logic .xor MID MID T),
  .vop (.sldoi T MID zero 8), .vop (.pmsumd T T C),
  .vop (.sldoi HI HI HI 8), .vop (.logic .xor HI HI MID),
  .vop (.sldoi T T T 8), .vop (.logic .xor d HI T)]

def mul (d a key zero : VReg) : List Instr := products a key zero ++ reduce d zero

def saved : List (Reg × Nat) := [(.r14,0),(.r15,8),(.r16,16),(.r18,24),(.r19,32),(.r20,40)]

def entry : List Instr := saved.map (fun (r,o) => .store .d r .r10 o) ++
 [mov .r16 .r10, .addi .r16 .r16 64, mov .r14 .r9, mov .r15 .r6] ++ setup ++
 [.li .r20 16, .stxvd2x .v0 .r16 .r0] ++ setMask U 1 ++ [.stxvd2x U .r16 .r20] ++
 setMask C (Impl.Gcm.Clmul.poly ++ Impl.Gcm.Clmul.poly) ++
 setMask H1 (Impl.Gcm.Clmul.xInv2Hi ++ 3#64) ++ load A .r8 ++
 [.vop (.sldoi A A A 8)] ++ mul H1 A H1 .v0 ++
 [.vop (.sldoi H1 H1 H1 8), .vop (.sldoi A H1 H1 8)] ++ mul H2 A H1 .v0 ++
 [.vop (.sldoi H2 H2 H2 8), .vop (.sldoi A H1 H1 8),
  .vop (.sldoi T A H2 8), .vop (.sldoi T T T 8),
  .vop (.sldoi H1 H2 A 8), .vop (.logic .or H2 T T)] ++ load Y .r14 ++
 [.loadRev .d .r18 .r5 .r0, .li .r11 8, .loadRev .w .r19 .r5 .r11, .lsl .r19 .r19 32,
  .li .r11 12, .loadRev .w .r8 .r5 .r11]

def counters : List Instr :=
 [.lsl .r11 .r8 32, .lsr .d .r11 .r11 32, .logic .or .r11 .r19 .r11,
  .lxvd2x U .r16 .r0] ++ Impl.Vector.PPC64LE.pair A T U .r18 .r11 ++
 [.lxvd2x U .r16 .r20, .vop (.add false T U U),
  .vop (.logic .or .v0 A A), .vop (.add false .v1 A U)] ++
 (List.range 6).map (fun i => .vop (.add false (breg (i+2)) (breg i) T)) ++ [.addi .r8 .r8 8]

def ghPair : List Instr := load A .r15 ++ [.vop (.logic .xor A A Y),.addi .r15 .r15 16] ++
 load HI .r15 ++ [.addi .r15 .r15 16, .vop (.sldoi HI HI HI 8),
  .vop (.sldoi T A HI 8), .vop (.sldoi U HI A 8), .vop (.sldoi U U U 8),
  .vop (.pmsumd HI U H2), .vop (.pmsumd LO T H1),
  .vop (.pmsumd MID U H1), .vop (.pmsumd U T H2), .vop (.logic .xor MID MID U),
  .lxvd2x U .r16 .r0] ++ reduce Y U ++ [.vop (.sldoi Y Y Y 8)]

def stores : List Instr := regs.flatMap (writeBlock true) ++ [.subi .r7 .r7 8]

def prime : Prog isa := .seq (.block counters) (.seq (aes false regs) (.block stores))

def piped : Prog isa := .seq (.block counters)
 (.seq (.block (initialBody false regs ++ [.li .r12 4]))
 (.seq (.loop (.block (middleBody false regs ++ middleBody false regs ++ ghPair ++ [.subi .r12 .r12 1]))
    (.nonzero .d .r12))
 (.seq (.loop (.block (middleBody false regs)) (.nonzero .d .r10))
 (.block (round false true regs ++ stores)))))

def exit : List Instr := [.li .r11 12, .storeRev .w .r8 .r5 .r11] ++ store Y .r14 ++
 [.subi .r12 .r16 64] ++ saved.map (fun (r,o) => .load .d r .r12 o)

/-- Experimental bulk kernel: the nonzero block count is a multiple of eight. -/
def code : Prog isa := .ite (.zero .d .r7) (.block [])
 (.seq (.block entry) (.seq prime
 (.seq (.ite (.zero .d .r7) (.block []) (.loop piped (.nonzero .d .r7)))
 (.seq (.block [.li .r12 4])
 (.seq (.loop (.block (ghPair ++ [.subi .r12 .r12 1])) (.nonzero .d .r12)) (.block exit))))))
end Fused

def main : IO Unit := do
 let mut asm := ".text\n.abiversion 2\n.globl gcm_fused\n.type gcm_fused,@function\ngcm_fused:\n"
 for line in printer.function Fused.code do
  match line with
  | .text x => asm := asm ++ x ++ "\n"
  | _ => throw (IO.userError "unexpected symbol")
 IO.FS.writeFile "/workspace/scratch/gcm-fused.s" asm
