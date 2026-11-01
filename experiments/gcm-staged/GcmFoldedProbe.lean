import VerifiedGarbage.Impl.Aes.PPC64LE.Crypto
import VerifiedGarbage.Impl.Gcm.Clmul
import VerifiedGarbage.Impl.Vector.PPC64LE
import VerifiedGarbage.TCB.PPC64LE.Print
open VG VG.PPC64LE
open VG.Impl.Aes.PPC64LE.Crypto
namespace Folded
abbrev Y : VReg := .v10
abbrev U : VReg := .v17
abbrev T : VReg := .v18
abbrev LO : VReg := .v14
abbrev MID : VReg := .v15
abbrev HI : VReg := .v16

def reg : Nat → VReg
 | 0 => .v0 | 1 => .v1 | 2 => .v2 | 3 => .v3
 | 4 => .v4 | 5 => .v5 | 6 => .v6 | 7 => .v7
 | 8 => .v11 | 9 => .v12 | 10 => .v13 | _ => .v19

def rs (n : Nat) := (List.range n).map reg

def reduce (d zero poly : VReg) : List Instr :=
 [.vop (.sldoi T LO zero 8), .vop (.pmsumd T T poly),
  .vop (.sldoi LO LO LO 8), .vop (.logic .xor MID MID LO), .vop (.logic .xor MID MID T),
  .vop (.sldoi T MID zero 8), .vop (.pmsumd T T poly),
  .vop (.sldoi HI HI HI 8), .vop (.logic .xor HI HI MID),
  .vop (.sldoi T T T 8), .vop (.logic .xor d HI T)]

def mul (d a key zero poly : VReg) : List Instr :=
 [.vop (.sldoi U a zero 8), .vop (.pmsumd HI U key),
  .vop (.sldoi U zero a 8), .vop (.pmsumd LO U key), .vop (.pmsumd MID a key)] ++ reduce d zero poly

def saved : List (Reg × Nat) :=
 [(.r14,0),(.r15,8),(.r16,16),(.r18,24),(.r19,32),(.r20,40),
  (.r21,48),(.r22,56),(.r23,64),(.r24,72),(.r25,80)]

def foldSetup : List Instr :=
 [.li .r11 80, .lxvd2x .v11 .r16 .r11, .vop (.logic .or .v12 .v11 .v11),
  .li .r11 256, .stxvd2x .v11 .r16 .r11] ++
 (List.range 7).flatMap (fun i =>
  [.vop (.sldoi .v9 .v12 .v12 8)] ++ mul .v12 .v9 .v11 .v0 .v13 ++
  [.vop (.sldoi .v12 .v12 .v12 8), .li .r11 (256+16*(i+1)), .stxvd2x .v12 .r16 .r11]) ++
 (List.range 4).flatMap (fun j =>
  [.li .r11 (256+16*(7-2*j)), .lxvd2x .v11 .r16 .r11,
   .li .r11 (256+16*(6-2*j)), .lxvd2x .v12 .r16 .r11,
   .vop (.sldoi .v9 .v12 .v12 8), .vop (.sldoi T .v9 .v11 8),
   .vop (.sldoi T T T 8), .vop (.sldoi .v11 .v11 .v9 8),
   .li .r11 (128+32*j), .stxvd2x .v11 .r16 .r11,
   .li .r11 (144+32*j), .stxvd2x T .r16 .r11])

def entry : List Instr := saved.map (fun (r,o) => .store .d r .r10 o) ++
 [mov .r16 .r10, .addi .r16 .r16 128, mov .r14 .r9, mov .r15 .r6] ++ setup ++
 [.li .r20 16, .li .r21 48, .li .r22 64, .li .r23 32, .addi .r24 .r16 256,
  .li .r25 96, .stxvd2x .v0 .r16 .r0, .stxvd2x .v19 .r16 .r25] ++
 setMask U 1 ++ [.stxvd2x U .r16 .r20] ++
 setMask .v13 (Impl.Gcm.Clmul.poly ++ Impl.Gcm.Clmul.poly) ++
 [.stxvd2x .v13 .r16 .r23] ++
 setMask .v11 (Impl.Gcm.Clmul.xInv2Hi ++ 3#64) ++ load .v9 .r8 ++
 [.vop (.sldoi .v9 .v9 .v9 8)] ++ mul .v11 .v9 .v11 .v0 .v13 ++
 [.vop (.sldoi .v11 .v11 .v11 8), .li .r11 80, .stxvd2x .v11 .r16 .r11,
  .vop (.sldoi .v9 .v11 .v11 8)] ++ mul .v12 .v9 .v11 .v0 .v13 ++
 [.vop (.sldoi .v12 .v12 .v12 8), .vop (.sldoi .v9 .v11 .v11 8),
  .vop (.sldoi T .v9 .v12 8), .vop (.sldoi T T T 8),
  .vop (.sldoi .v11 .v12 .v9 8), .vop (.logic .or .v12 T T),
  .stxvd2x .v11 .r16 .r21, .stxvd2x .v12 .r16 .r22] ++ load Y .r14 ++
 [.loadRev .d .r18 .r5 .r0, .li .r11 8, .loadRev .w .r19 .r5 .r11, .lsl .r19 .r19 32,
  .li .r11 12, .loadRev .w .r8 .r5 .r11,
  mov .r9 .r3] ++ foldSetup ++ [mov .r11 .r24, .addi .r12 .r4 1]

def cache : Prog isa := .seq (.loop (.block (load .v8 .r9 ++
 [.stxvd2x .v8 .r11 .r0, .addi .r9 .r9 16, .addi .r11 .r11 16, .subi .r12 .r12 1]))
 (.nonzero .d .r12)) (.block [mov .r3 .r24])

def counters (n : Nat) : List Instr :=
 [.lsl .r11 .r8 32, .lsr .d .r11 .r11 32, .logic .or .r11 .r19 .r11,
  .lxvd2x U .r16 .r0] ++ Impl.Vector.PPC64LE.pair .v9 T U .r18 .r11 ++
 [.lxvd2x U .r16 .r20, .vop (.add false T U U),
  .vop (.logic .or .v0 .v9 .v9), .vop (.add false .v1 .v9 U)] ++
 (List.range (n-2)).map (fun i => .vop (.add false (reg (i+2)) (reg i) T)) ++ [.addi .r8 .r8 n]

def initial (n : Nat) : List Instr := keyStart false ++ [.lxvd2x .v8 .r9 .r0] ++
 (rs n).map (fun r => .vop (.logic .xor r r .v8)) ++ [keyStep false] ++ [.subi .r10 .r4 1]
def roundRaw (n : Nat) (last : Bool) : List Instr := [.lxvd2x .v8 .r9 .r0] ++
 (rs n).map (fun r => .vop (.cipher false last r r .v8))
def middle (n : Nat) : List Instr := roundRaw n false ++ [keyStep false] ++ [.subi .r10 .r10 1]

def ghPair (first last : Bool) : List Instr := [.lxvd2x .v9 .r16 .r25] ++
 Impl.Vector.PPC64LE.loadPerm LO .r15 .v9 ++
 (if first then [.vop (.logic .xor LO LO Y)] else []) ++ [.addi .r15 .r15 16] ++
 Impl.Vector.PPC64LE.loadPerm HI .r15 .v9 ++
 [.addi .r15 .r15 16, .lxvd2x .v8 .r16 .r21, .lxvd2x .v9 .r16 .r22,
  .addi .r21 .r21 32, .addi .r22 .r22 32,
  .vop (.sldoi HI HI HI 8), .vop (.sldoi T LO HI 8),
  .vop (.sldoi U HI LO 8), .vop (.sldoi U U U 8),
  .vop (.pmsumd HI U .v9), .vop (.pmsumd LO T .v8),
  .vop (.pmsumd MID U .v8), .vop (.pmsumd U T .v9), .vop (.logic .xor MID MID U)] ++
 (if first then
  [.vop (.logic .or Y LO LO), .vop (.logic .or .v11 MID MID), .vop (.logic .or .v12 HI HI)]
 else if last then
  [.vop (.logic .xor LO LO Y), .vop (.logic .xor MID MID .v11), .vop (.logic .xor HI HI .v12),
   .lxvd2x .v8 .r16 .r23, .lxvd2x U .r16 .r0] ++ reduce Y U .v8 ++ [.vop (.sldoi Y Y Y 8)]
 else [.vop (.logic .xor Y Y LO), .vop (.logic .xor .v11 .v11 MID), .vop (.logic .xor .v12 .v12 HI)])

def stores (n : Nat) : List Instr := [.lxvd2x .v8 .r16 .r25] ++ (rs n).flatMap (fun r =>
 Impl.Vector.PPC64LE.loadPerm .v9 .r6 .v8 ++
 [.vop (.logic .xor r r .v9), .vop (.perm r r r .v8), .stxvd2x r .r6 .r0, .addi .r6 .r6 16]) ++
 [.subi .r7 .r7 n]

def prime (n : Nat) : Prog isa := .seq (.block (counters n ++ initial n))
 (.seq (.loop (.block (middle n)) (.nonzero .d .r10)) (.block (roundRaw n true ++ stores n)))

def ghStart : List Instr := [.li .r21 128, .li .r22 144]
def twoRounds := middle 8 ++ middle 8

def piped : Prog isa := .seq (.block (counters 8 ++ initial 8 ++ ghStart ++ twoRounds ++ ghPair true false ++ [.li .r12 2]))
 (.seq (.loop (.block (twoRounds ++ ghPair false false ++ [.subi .r12 .r12 1])) (.nonzero .d .r12))
 (.seq (.block (twoRounds ++ ghPair false true))
 (.seq (.loop (.block (middle 8)) (.nonzero .d .r10)) (.block (roundRaw 8 true ++ stores 8)))))

def drain : Prog isa := .seq (.block (ghStart ++ ghPair true false ++ [.li .r12 2]))
 (.seq (.loop (.block (ghPair false false ++ [.subi .r12 .r12 1])) (.nonzero .d .r12))
 (.block (ghPair false true)))

def exit : List Instr := [.li .r11 12, .storeRev .w .r8 .r5 .r11, .lxvd2x .v8 .r16 .r25,
 .vop (.perm Y Y Y .v8), .stxvd2x Y .r14 .r0, .subi .r12 .r16 128] ++
 saved.map (fun (r,o) => .load .d r .r12 o)

def code : Prog isa := .ite (.zero .d .r7) (.block [])
 (.seq (.block entry) (.seq cache (.seq (prime 8)
 (.seq (.ite (.zero .d .r7) (.block []) (.loop piped (.nonzero .d .r7)))
 (.seq drain (.block exit))))))
end Folded

def main : IO Unit := do
 let mut asm := ".text\n.abiversion 2\n.globl gcm_fold8\n.type gcm_fold8,@function\ngcm_fold8:\n"
 for line in printer.function Folded.code do
  match line with
  | .text x => asm := asm ++ x ++ "\n"
  | _ => throw (IO.userError "unexpected symbol")
 IO.FS.writeFile "/workspace/scratch/gcm-folded.s" asm
