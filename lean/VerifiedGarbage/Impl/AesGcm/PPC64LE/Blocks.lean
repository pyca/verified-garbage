module

public import VerifiedGarbage.Impl.Aes.PPC64LE.Crypto
public import VerifiedGarbage.Impl.Gcm.PPC64LE.Vpmsum
public import VerifiedGarbage.Impl.Gcm.PPC64LE
public import VerifiedGarbage.Impl.Aes.PPC64LE.Ctr32

/-! # Fused POWER8 AES-CTR and GHASH bulk blocks

Eight ciphertext vectors are stored and then folded directly into GHASH.
The counter, hash powers and native-layout round keys use caller scratch.
The nonzero block count is a multiple of eight. This internal kernel is
not registered or used by the public API until its proof is complete.
-/

@[expose] public section

namespace VG.Impl.AesGcm.PPC64LE.Blocks
open VG.PPC64LE
open VG.Impl.Aes.PPC64LE.Crypto
abbrev Y : VReg := .v10
abbrev U : VReg := .v17
abbrev T : VReg := .v18
abbrev LO : VReg := .v14
abbrev MID : VReg := .v15
abbrev HI : VReg := .v16

abbrev reg := breg
abbrev rs := batchRegs

def reduce (d zero poly : VReg) : List Instr :=
 Impl.Gcm.PPC64LE.Vpmsum.reduceWith LO MID HI T zero poly d

def mul (d a key zero poly : VReg) : List Instr :=
 Impl.Gcm.PPC64LE.Vpmsum.productsWith U LO MID HI zero a key ++ reduce d zero poly

def saved : List (Reg × Nat) :=
 [(.r14,0),(.r15,8),(.r16,16),(.r20,40),
  (.r21,48),(.r22,56),(.r23,64),(.r24,72),(.r18,80)]

def packEven : List Instr :=
 [.vop (.sldoi .v9 .v8 .v8 8), .vop (.sldoi T .v9 .v12 8),
  .vop (.sldoi T T T 8), .vop (.sldoi .v8 .v12 .v9 8)]

def powerCopy (j : Nat) : List Instr :=
 if (j+2)%2=0 then [.vop (.logic .or .v8 .v12 .v12)] else []

def powerNext (j : Nat) : List Instr := powerCopy j ++
 [.vop (.sldoi .v9 .v12 .v12 8)] ++ mul .v12 .v9 .v11 .v0 .v13 ++
 [.vop (.sldoi .v12 .v12 .v12 8)]

def powerSave (v : VReg) (offset : Nat) : List Instr :=
 [.li .r11 offset,.stxvd2x v .r16 .r11]

def packSave (offset : Nat) : List Instr :=
 packEven ++ powerSave .v8 offset ++ powerSave T (offset+16)

def powerOffset (j : Nat) : Nat := 128+32*(4-(j+2)/2)

def powerStore (j : Nat) : List Instr :=
 if (j+2)%2=0 then packSave (powerOffset j) else []

def powerStep (j : Nat) : List Instr := powerNext j ++ powerStore j

def foldSetup : List Instr := [.vop (.logic .or .v12 .v11 .v11)] ++
 (List.range 7).flatMap powerStep

def entry : List Instr := saved.map (fun (r,o) => .store .d r .r10 o) ++
 [mov .r16 .r10, .addi .r16 .r16 128, mov .r14 .r9, .li .r15 112] ++ setup ++
 [.li .r20 16, .addi .r24 .r16 256, .li .r18 96] ++
 setMask U 1 ++ [.stxvd2x U .r16 .r20] ++
 setMask .v13 (Impl.Gcm.Clmul.poly ++ Impl.Gcm.Clmul.poly) ++
 setMask .v11 (Impl.Gcm.Clmul.xInv2Hi ++ 3#64) ++ load .v9 .r8 ++
 [.vop (.sldoi .v9 .v9 .v9 8)] ++ mul .v11 .v9 .v11 .v0 .v13 ++
 [.vop (.sldoi .v11 .v11 .v11 8)] ++ load Y .r14 ++
 [.li .r11 12, .loadRev .w .r8 .r5 .r11, mov .r9 .r3] ++ foldSetup ++ [mov .r11 .r24, .addi .r12 .r4 1]

def copyKey : List Instr := load .v8 .r9 ++ [.stxvd2x .v8 .r11 .r0]
def cacheStep : List Instr := copyKey ++ [.addi .r9 .r9 16, .addi .r11 .r11 16, .subi .r12 .r12 1]

def cache : Prog isa := .seq (.loop (.block cacheStep) (.nonzero .d .r12))
 (.block ([mov .r3 .r24, .li .r23 64, .li .r24 80] ++ load .v0 .r5 ++ [.stxvd2x .v0 .r16 .r15]))

def counterStart : List Instr :=
 [.lxvd2x .v0 .r16 .r15, .lxvd2x U .r16 .r20, .vop (.add false T U U),
  .vop (.add false .v1 .v0 U)]

def counterNext (n : Nat) : List Instr :=
 [.vop (.add false T (reg (n-2)) T), .stxvd2x T .r16 .r15, .addi .r8 .r8 n]

def counters (n : Nat) : List Instr := counterStart ++
 (List.range (n-2)).map (fun i => .vop (.add false (reg (i+2)) (reg i) T)) ++
 counterNext n

def roundRaw (n : Nat) (last : Bool) : List Instr := [.lxvd2x .v8 .r9 .r0] ++
 cipherRegs false last .v8 (rs n)
def middle (n : Nat) : List Instr := roundRaw n false ++ [keyStep false] ++ [.subi .r10 .r10 1]

def ghAcc (j : Nat) : List Instr :=
 if j=0 then
  [.vop (.logic .or Y LO LO), .vop (.logic .or .v11 MID MID), .vop (.logic .or .v12 HI HI)]
 else if j=3 then
  [.vop (.logic .xor LO LO Y), .vop (.logic .xor MID MID .v11), .vop (.logic .xor HI HI .v12)]
 else [.vop (.logic .xor Y Y LO), .vop (.logic .xor .v11 .v11 MID), .vop (.logic .xor .v12 .v12 HI)]

def ghRead : List Instr :=
 [.lxvd2x .v8 .r16 .r21, .lxvd2x .v9 .r16 .r22,
  .addi .r21 .r21 32, .addi .r22 .r22 32]

def ghInject (j : Nat) : List Instr :=
 if j=0 then [.vop (.logic .xor .v0 .v0 Y)] else []

def ghPair (j : Nat) : List Instr :=
 ghInject j ++
 ghRead ++ Impl.Gcm.PPC64LE.Vpmsum.packedProductsWith
  (reg (2*j)) (reg (2*j+1)) U T LO MID HI .v8 .v9 true ++ ghAcc j

def ghFinish : List Instr := [.vop (.logic .xor U U U)] ++ reduce Y U .v13 ++
 [.vop (.sldoi Y Y Y 8)]

def dataRegs : List VReg := [.v8,.v9,.v11,.v12,.v14,.v15,.v16,.v17]
def dataOffsets : List Reg := [.r0,.r20,.r21,.r22,.r23,.r24,.r18,.r11]

def dataReg (i : Nat) : VReg := dataRegs.getD i .v8
def dataOffset (i : Nat) : Reg := dataOffsets.getD i .r0

def dataLoad : List Instr := (List.range 8).flatMap (fun i => [.lxvd2x (dataReg i) .r6 (dataOffset i)])

def dataMix : List Instr := (List.range 8).flatMap (fun i =>
 [.vop (.perm (dataReg i) (dataReg i) (dataReg i) .v19),
  .vop (.logic .xor (reg i) (reg i) (dataReg i))])

def dataWrite : List Instr := (List.range 8).flatMap (fun i => storePerm (dataReg i) (reg i) .r6 (dataOffset i))

def stores : List Instr := dataLoad ++ dataMix ++ dataWrite ++ [.addi .r6 .r6 128, .subi .r7 .r7 8]

def keyOffsets : List Reg := [.r20,.r21,.r22,.r23,.r24,.r18,.r11,.r12]

def roundKeyRegs : List VReg := dataRegs ++ [T]

def keyOffset (i : Nat) : Reg := keyOffsets.getD i .r0

def keyOffsetRegs : List Reg := [.r21,.r22,.r11,.r12]

def keyRead (i : Nat) : List Instr :=
 (if keyOffsetRegs.contains (keyOffset i) then [.li (keyOffset i) (16*(i+1))] else []) ++
 [.lxvd2x (dataReg i) .r3 (keyOffset i)]

def keyReads : List Instr := (List.range 8).flatMap keyRead ++
 [.addi .r9 .r3 144, .lxvd2x T .r9 .r0]

def keyRounds : List Instr := roundKeyRegs.flatMap (fun k => cipherRegs false false k (rs 8))

def firstNine : List Instr := keyReads ++ keyRounds

def aesInitial : List Instr := [.lxvd2x .v8 .r3 .r0] ++ xorKey (rs 8)

def aesRemaining : List Instr := [.addi .r9 .r3 160, .subi .r10 .r4 10]

def aes8 : Prog isa := .seq (.block (aesInitial ++ firstNine ++ aesRemaining))
 (.seq (.ite (.zero .d .r10) (.block []) (.loop (.block (middle 8)) (.nonzero .d .r10)))
 (.block (roundRaw 8 true)))

def batch : Prog isa := .seq (.block (counters 8))
 (.seq aes8 (.block (stores ++ [.li .r21 128, .li .r22 144] ++
  (List.range 4).flatMap ghPair ++ ghFinish)))

def exit : List Instr := [.li .r11 12, .storeRev .w .r8 .r5 .r11] ++ store Y .r14 ++
 [.subi .r12 .r16 128] ++
 saved.map (fun (r,o) => .load .d r .r12 o)

def code : Prog isa := .ite (.zero .d .r7) (.block [])
 (.seq (.block entry) (.seq cache
 (.seq (.loop batch (.nonzero .d .r7)) (.block exit))))
/-! The existing whole-block API emits the bulk kernel once. Its callers
reuse it with a call; short inputs and the tail use the existing primitives.
The seven nonvolatile argument registers are outside the bulk kernel's set. -/

def wrapperSaved : List (Reg × Nat) :=
 [(.r25,0),(.r26,8),(.r27,16),(.r28,24),(.r29,32),(.r30,40),(.r31,48)]

def wrapperEntry : List Instr := wrapperSaved.map (fun (r,o) => .store .d r .r9 o) ++
 [.mflr .r0, .store .d .r0 .r9 56, mov .r29 .r3, mov .r28 .r4, mov .r27 .r5,
  mov .r26 .r6, mov .r30 .r7, mov .r25 .r8, mov .r31 .r9, .lsr .d .r12 .r25 5]

def bulkArgs : List Instr :=
 [mov .r3 .r29, mov .r4 .r28, mov .r5 .r27, mov .r6 .r30, .li .r0 7,
  .logic .and .r11 .r25 .r0, .sub .r7 .r25 .r11, .addi .r8 .r29 240,
  mov .r9 .r26, .addi .r10 .r31 64]

def bulkRest : List Instr :=
 [.li .r0 7, .logic .and .r11 .r25 .r0, .sub .r12 .r25 .r11, .lsl .r12 .r12 4,
  .add .r30 .r30 .r12, mov .r25 .r11]

def tailCtrArgs : List Instr :=
 [mov .r3 .r29, mov .r4 .r28, mov .r5 .r27, mov .r6 .r30, mov .r7 .r25, .addi .r8 .r31 64]

def tailGhArgs : List Instr :=
 [.addi .r3 .r29 240, mov .r4 .r26, mov .r5 .r30, mov .r6 .r25, .addi .r7 .r31 64]

def tail : Prog isa := .ite (.zero .d .r25) (.block [])
 (.seq (.block tailCtrArgs)
 (.seq (.call "vg_aes_ctr32" Impl.Aes.PPC64LE.ctr32)
 (.seq (.block tailGhArgs) (.call "vg_ghash" Impl.Gcm.PPC64LE.ghash))))

def wrapperExit : List Instr :=
 [.load .d .r0 .r31 56, .mtlr .r0, mov .r12 .r31] ++
 wrapperSaved.map (fun (r,o) => .load .d r .r12 o)

/-- `vg_aes_gcm_encrypt_blocks(ctx, Nr, counter, y, data, n, scratch)`.
The signature grants 2112 scratch bytes: 64 for the wrapper, 2048 for its code. -/
def encrypt : Prog isa := .ite (.zero .d .r8) (.block [])
 (.seq (.block wrapperEntry)
 (.seq (.ite (.zero .d .r12) (.block [])
   (.seq (.block bulkArgs) (.seq code (.block bulkRest))))
 (.seq tail (.block wrapperExit))))

end VG.Impl.AesGcm.PPC64LE.Blocks
