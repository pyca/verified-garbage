module

public import VerifiedGarbage.Impl.Dsa.AArch64.Random

/-! Randomized DSA signing with AAPCS64 arguments and a preserved link register. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.RandomSign
open VG VG.AArch64 VG.Impl.Bignum.AArch64 Random

def oLink : Nat := 232

def entryHeader : List Instr :=
  store oOut .x0 ++ store oOutLen .x1 ++ store oUsedPtr .x2 ++
  store oKey .x3 ++ store oKeyLen .x4 ++ store oPLen .x5 ++
  store oQLen .x6 ++ store oDigest .x7 ++ store oLink .x30 ++
  [.add .x .x4 .x3 .x5] ++ store oQ .x4 ++
  [movi .x0 0] ++ store oUsed .x0 ++ [movi .x0 8] ++ store oAttempts .x0

def incomingSlots : List (Nat × Nat) :=
  [(256, oDigestLen), (264, oRand), (272, oRandLen), (280, oScratch), (288, oScratchLen)]

def entry : List Instr := entryHeader ++ incomingSlots.flatMap (fun p => copySlot p.1 p.2)

def callArgs : List Instr :=
  [(oDigestLen, 0), (oScratch, 8), (oScratchLen, 16)].flatMap (fun p => copySlot p.1 p.2) ++
  [.ldrSp .x0 oOut, .ldrSp .x1 oOutLen, .ldrSp .x2 oKey, .ldrSp .x3 oKeyLen,
   .ldrSp .x4 oPLen, .addSp .x5 oNonce, .ldrSp .x6 oQLen, .ldrSp .x7 oDigest]

def callFinish : Prog isa :=
  .seq (.block ([.ldrSp .x30 oLink, .logic .orr .w .x0 .x0 .x0] ++ store oStatus .x0))
    (.ite (.zero .x .x0)
      (.seq (.block ([.ldrSp .x0 oAttempts, .subImm .x .x0 .x0 1] ++ store oAttempts .x0))
        (.ite (.nonzero .x .x0) (.block ([movi .x0 4] ++ store oStatus .x0)) (.block [])))
      (.block []))

def attempt (name : String) (signer : Prog isa) : Prog isa :=
  .seq sample (.seq (.block [.subImm .x .x4 .x0 1])
    (.ite (.zero .x .x4) (.seq (.block callArgs) (.seq (.call name signer) callFinish)) (.block [])))

def zeroOut : Prog isa :=
  .seq (.block [.ldrSp .x12 oOut, .ldrSp .x9 oOutLen, movi .x0 0])
    (.loop (.block [.strb .x0 .x12 0, .addImm .x .x12 .x12 1,
      .subImm .x .x9 .x9 1]) (.nonzero .x .x9))

def finish : Prog isa :=
  .seq (.block (statusTest 1))
    (.seq (.ite (.nonzero .x .x4) zeroOut (.block []))
      (.block (clearNonce ++ [.ldrSp .x2 oUsedPtr, .ldrSp .x0 oUsed,
        .str .x .x0 .x2 0, .ldrSp .x0 oStatus])))

def body (name : String) (signer : Prog isa) : Prog isa :=
  .seq (.block entry) (.seq prepare
    (.seq (.ite (.zero .x .x0) (.block (store oStatus .x0))
      (.loop (.seq (attempt name signer) (.block (statusTest 4))) (.zero .x .x4))) finish))

def code (name : String) (signer : Prog isa) : Prog isa :=
  .frame (.alloc frameBytes) (body name signer) (.free frameBytes)

end VG.Impl.Dsa.AArch64.RandomSign
