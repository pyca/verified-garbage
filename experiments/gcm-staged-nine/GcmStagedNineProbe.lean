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
 [(.r14,0),(.r15,8),(.r16,16),(.r20,40),
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
 [mov .r16 .r10, .addi .r16 .r16 128, mov .r14 .r9, .li .r15 112] ++ setup ++
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
 [.li .r11 12, .loadRev .w .r8 .r5 .r11, mov .r9 .r3] ++ foldSetup ++ [mov .r11 .r24, .addi .r12 .r4 1]

def cache : Prog isa := .seq (.loop (.block (load .v8 .r9 ++
 [.stxvd2x .v8 .r11 .r0, .addi .r9 .r9 16, .addi .r11 .r11 16, .subi .r12 .r12 1]))
 (.nonzero .d .r12)) (.block ([mov .r3 .r24, .li .r23 64, .li .r24 80] ++ load .v0 .r5 ++ [.stxvd2x .v0 .r16 .r15]))

def counters (n : Nat) : List Instr :=
 [.lxvd2x .v0 .r16 .r15, .lxvd2x U .r16 .r20, .vop (.add false T U U),
  .vop (.add false .v1 .v0 U)] ++
 (List.range (n-2)).map (fun i => .vop (.add false (reg (i+2)) (reg i) T)) ++
 [.vop (.add false T (reg (n-2)) T), .stxvd2x T .r16 .r15, .addi .r8 .r8 n]

def initial (n : Nat) : List Instr := keyStart false ++ [.lxvd2x .v8 .r9 .r0] ++
 (rs n).map (fun r => .vop (.logic .xor r r .v8)) ++ [keyStep false] ++ [.subi .r10 .r4 1]
def roundRaw (n : Nat) (last : Bool) : List Instr := [.lxvd2x .v8 .r9 .r0] ++
 (rs n).map (fun r => .vop (.cipher false last r r .v8))
def middle (n : Nat) : List Instr := roundRaw n false ++ [keyStep false] ++ [.subi .r10 .r10 1]

def ghPair (j : Nat) : List Instr :=
 (if j=0 then [.vop (.logic .xor .v0 .v0 Y)] else []) ++
 [.lxvd2x .v8 .r16 .r21, .lxvd2x .v9 .r16 .r22,
  .addi .r21 .r21 32, .addi .r22 .r22 32,
  .vop (.sldoi HI (reg (2*j+1)) (reg (2*j+1)) 8),
  .vop (.sldoi T (reg (2*j)) HI 8), .vop (.sldoi U HI (reg (2*j)) 8),
  .vop (.sldoi U U U 8),
  .vop (.pmsumd HI U .v9), .vop (.pmsumd LO T .v8),
  .vop (.pmsumd MID U .v8), .vop (.pmsumd U T .v9), .vop (.logic .xor MID MID U)] ++
 (if j=0 then
  [.vop (.logic .or Y LO LO), .vop (.logic .or .v11 MID MID), .vop (.logic .or .v12 HI HI)]
 else if j=3 then
  [.vop (.logic .xor LO LO Y), .vop (.logic .xor MID MID .v11), .vop (.logic .xor HI HI .v12),
   .vop (.logic .xor U U U)] ++ reduce Y U .v13 ++ [.vop (.sldoi Y Y Y 8)]
 else [.vop (.logic .xor Y Y LO), .vop (.logic .xor .v11 .v11 MID), .vop (.logic .xor .v12 .v12 HI)])

def dataRegs : List VReg := [.v8,.v9,.v11,.v12,.v14,.v15,.v16,.v17]
def dataOffsets : List Reg := [.r0,.r20,.r21,.r22,.r23,.r24,.r25,.r11]

def stores (n : Nat) : List Instr :=
 (dataRegs.zip dataOffsets).map (fun (v,r) => .lxvd2x v .r6 r) ++
 (dataRegs.zip (rs n)).flatMap (fun (v,r) =>
  [.vop (.perm v v v .v19), .vop (.logic .xor r r v)]) ++
 ((dataRegs.zip (rs n)).zip dataOffsets).flatMap (fun ((v,r),o) =>
  [.vop (.perm v r r .v19), .stxvd2x v .r6 o]) ++ [.addi .r6 .r6 128, .subi .r7 .r7 n]

def keyOffsets : List Reg := [.r20,.r21,.r22,.r23,.r24,.r25,.r11,.r12]

def firstEight : List Instr :=
 (keyOffsets.zipIdx).flatMap (fun (r,i) =>
  (if [.r21,.r22,.r11,.r12].contains r then [.li r (16*(i+1))] else []) ++
  [.lxvd2x dataRegs[i]! .r3 r]) ++
 [.addi .r9 .r3 144, .lxvd2x T .r9 .r0] ++
 (dataRegs ++ [T]).flatMap (fun k => (rs 8).map (fun v => .vop (.cipher false false v v k)))

def batch : Prog isa := .seq (.block (counters 8 ++ [.lxvd2x .v8 .r3 .r0] ++
 (rs 8).map (fun r => .vop (.logic .xor r r .v8)) ++ firstEight ++
 [.addi .r9 .r3 160, .subi .r10 .r4 10]))
 (.seq (.ite (.zero .d .r10) (.block []) (.loop (.block (middle 8)) (.nonzero .d .r10)))
 (.block (roundRaw 8 true ++ stores 8 ++ [.li .r21 128, .li .r22 144] ++
  (List.range 4).flatMap ghPair)))

def exit : List Instr := [.li .r11 12, .storeRev .w .r8 .r5 .r11, .lxvd2x .v8 .r16 .r25,
 .vop (.perm Y Y Y .v8), .stxvd2x Y .r14 .r0, .subi .r12 .r16 128] ++
 saved.map (fun (r,o) => .load .d r .r12 o)

def code : Prog isa := .ite (.zero .d .r7) (.block [])
 (.seq (.block entry) (.seq cache
 (.seq (.loop batch (.nonzero .d .r7)) (.block exit))))
end Folded

def main : IO Unit := do
 let mut asm := ".text\n.abiversion 2\n.globl gcm_staged8_nine\n.type gcm_staged8_nine,@function\ngcm_staged8_nine:\n"
 for line in printer.function Folded.code do
  match line with
  | .text x => asm := asm ++ x ++ "\n"
  | _ => throw (IO.userError "unexpected symbol")
 IO.FS.writeFile "/workspace/scratch/gcm-staged-nine.s" asm
