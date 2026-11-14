module

public import VerifiedGarbage.Impl.Aes.PPC64LE.Crypto

/-! # POWER8 AES key expansion

FIPS 197's word loop, with `vsbox` for SubWord. Pointers and word counts
stay in volatile GPRs; the scratch argument is unused. The previous word
stays in `r9` from one iteration to the next, loaded once before the loop,
so that no iteration waits for the word the one before it stored. Word operations
explicitly zero-extend the low 32 bits after extracting the substituted
word from the vector register.
-/

@[expose] public section
namespace VG.Impl.Aes.PPC64LE.Crypto
open VG.PPC64LE

def copyBody : List Instr :=
  [.load .d .r8 .r3 0, .store .d .r8 .r5 0,
   .addi .r3 .r3 8, .addi .r5 .r5 8, .subi .r4 .r4 8]

def wordSetup : List Instr :=
  [.sub .r10 .r5 .r7, .subi .r11 .r5 4, .li .r12 0, .lsr .d .r4 .r7 2,
   .add .r8 .r4 .r4, .add .r4 .r4 .r8, .addi .r4 .r4 28, .li .r6 1]

def subWord : List Instr :=
  [.mtvsrd .v0 .r9, .vop (.sbox .v0 .v0), .mfvsrd .r9 .v0, .rotr .w .r9 .r9 0]

def rotTail : List Instr :=
  [.rotr .w .r9 .r9 8, .logic .xor .r9 .r9 .r6,
   .lsr .d .r0 .r6 7, .li .r8 0, .sub .r0 .r8 .r0, .li .r8 0x1b, .logic .and .r0 .r0 .r8,
   .add .r6 .r6 .r6, .logic .xor .r6 .r6 .r0, .li .r8 0xff, .logic .and .r6 .r6 .r8]

def tempWord : Prog isa :=
  .ite (.zero .d .r12) (.block (subWord ++ rotTail))
    (.seq (.block [.subi .r0 .r12 16])
      (.ite (.zero .d .r0)
        (.seq (.block [.subi .r0 .r7 32]) (.ite (.zero .d .r0) (.block subWord) (.block [])))
        (.block [])))

def wordStore : List Instr :=
  [.load .w .r8 .r10 0, .logic .xor .r9 .r9 .r8, .store .w .r9 .r11 4,
   .addi .r11 .r11 4, .addi .r10 .r10 4, .addi .r12 .r12 4, .sub .r0 .r12 .r7]

def wordEnd : Prog isa :=
  .seq (.ite (.zero .d .r0) (.block [.li .r12 0]) (.block [])) (.block [.subi .r4 .r4 1])

def wordBody : Prog isa :=
  .seq tempWord (.seq (.block wordStore) wordEnd)

/-- The 24-byte keys' word loop. -/
def wordTail : Prog isa :=
  .seq (.block wordSetup) (.seq (.block [.load .w .r9 .r11 0]) (.loop wordBody (.nonzero .d .r4)))

/-- `vperm`'s controls: each word the last word of the first operand,
rotated by a byte; the same, not rotated; the low byte of each word byte 7
of the first operand (the low byte of the GPR `mtvsrd` moved there), the
others zero (byte 0 of the second operand, `v4`). -/
def rotCtl : BitVec 64 := 0x0300010203000102
def subCtl : BitVec 64 := 0x0001020300010203
def rcCtl : BitVec 64 := 0x1010100710101007

def setCtl (d : VReg) (x : BitVec 64) : List Instr :=
  Impl.Vector.PPC64LE.const64 .r8 x ++ Impl.Vector.PPC64LE.pair d .v3 .v4 .r8 .r8

/-- Four words from the schedule at `p` (with `r12 = 0`). -/
def loadKey (d : VReg) (p : Reg) : List Instr := [.lxvd2x d p .r12, .vop (.sldoi d d d 8)]

def vecSetup : List Instr :=
  [.sub .r11 .r5 .r7, .li .r12 0] ++ loadKey .v1 .r11 ++ [.addi .r10 .r11 16] ++ loadKey .v2 .r10 ++
    [.vop (.logic .xor .v4 .v4 .v4)] ++ setCtl .v5 rotCtl ++ setCtl .v6 subCtl ++ setCtl .v7 rcCtl ++
    [.li .r6 1]

/-- The round constant `r6` in the low byte of every word of `v8`, and the
next round constant in `r6`. -/
def rcSplat : List Instr := [.mtvsrd .v8 .r6, .vop (.perm .v8 .v8 .v4 .v7)]
def rcStep : List Instr :=
  [.lsr .d .r0 .r6 7, .li .r8 0, .sub .r0 .r8 .r0, .li .r8 0x1b, .logic .and .r0 .r0 .r8,
   .add .r6 .r6 .r6, .logic .xor .r6 .r6 .r0, .li .r8 0xff, .logic .and .r6 .r6 .r8]

/-- `d ⊕ (d ≪ 32)`, then that `⊕` itself `≪ 64`: the prefix XORs of `d`'s words. -/
def prefixXor (d : VReg) : List Instr :=
  [.vop (.sldoi .v3 d .v4 4), .vop (.logic .xor d d .v3), .vop (.sldoi .v3 d .v4 8),
   .vop (.logic .xor d d .v3)]

/-- The next four words in `d`, from the four in `d` and `temp` from the last word of `t`:
SubWord(RotWord) and the round constant, or SubWord alone. -/
def stepRot (d t : VReg) : List Instr :=
  [.vop (.perm .v0 t t .v5), .vop (.sbox .v0 .v0), .vop (.logic .xor .v0 .v0 .v8)] ++ prefixXor d ++
    [.vop (.logic .xor d d .v0)]
def stepSub (d t : VReg) : List Instr :=
  [.vop (.perm .v0 t t .v6), .vop (.sbox .v0 .v0)] ++ prefixXor d ++ [.vop (.logic .xor d d .v0)]

def storeKey (d : VReg) : List Instr := [.vop (.sldoi .v9 d d 8), .stxvd2x .v9 .r5 .r12, .addi .r5 .r5 16]

def rotRound (d t : VReg) : List Instr := rcSplat ++ rcStep ++ stepRot d t ++ storeKey d

/-- 16-byte keys: ten rounds of four words. -/
def body128 : List Instr := rotRound .v1 .v1 ++ [.subi .r4 .r4 1]
def loop128 : Prog isa := .seq (.block [.li .r4 10]) (.loop (.block body128) (.nonzero .d .r4))

/-- 32-byte keys: six rounds of eight words, then four. -/
def body256 : List Instr := rotRound .v1 .v2 ++ stepSub .v2 .v1 ++ storeKey .v2 ++ [.subi .r4 .r4 1]
def loop256 : Prog isa :=
  .seq (.block [.li .r4 6]) (.seq (.loop (.block body256) (.nonzero .d .r4)) (.block (rotRound .v1 .v2)))

def vecTail : Prog isa :=
  .seq (.block vecSetup) (.seq (.block [.subi .r0 .r7 16]) (.ite (.zero .d .r0) loop128 loop256))

def expandKey : Prog isa :=
  .seq (.block [mov .r7 .r4])
    (.seq (.loop (.block copyBody) (.nonzero .d .r4))
      (.seq (.block [.subi .r0 .r7 24]) (.ite (.zero .d .r0) wordTail vecTail)))

end VG.Impl.Aes.PPC64LE.Crypto
