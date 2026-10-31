module

public import VerifiedGarbage.Impl.Aes.PPC64LE.Crypto

/-! # POWER8 AES key expansion

FIPS 197's word loop, with `vsbox` for SubWord. Pointers and word counts
stay in volatile GPRs; the scratch argument is unused. Word operations
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
  .seq (.block [.load .w .r9 .r11 0]) (.seq tempWord (.seq (.block wordStore) wordEnd))

def expandKey : Prog isa :=
  .seq (.block [mov .r7 .r4])
    (.seq (.loop (.block copyBody) (.nonzero .d .r4))
      (.seq (.block wordSetup) (.loop wordBody (.nonzero .d .r4))))

end VG.Impl.Aes.PPC64LE.Crypto
