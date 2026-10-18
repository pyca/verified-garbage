module

public import VerifiedGarbage.Impl.Dsa.AArch64.RandomSign
public import VerifiedGarbage.Impl.Dsa.AArch64.Generate

/-! # Complete DSA key generation with AAPCS64 arguments

Check the domain before sampling, reuse the randomized signer's bounded
scalar sampler, then derive the packed key. The caller's link register is
saved across both calls. Each arithmetic backend supplies both callees.
-/

@[expose] public section
namespace VG.Impl.Dsa.AArch64.GenerateKey
open VG VG.AArch64 VG.Impl.Bignum.AArch64 Random

def entryHeader : List Instr :=
  store oOut .x0 ++ store oOutLen .x1 ++ store oUsedPtr .x2 ++
  store oKey .x3 ++ store oKeyLen .x4 ++ store oPLen .x5 ++
  store oQLen .x6 ++ store oRand .x7 ++ store RandomSign.oLink .x30 ++
  [.add .x .x4 .x3 .x5] ++ store oQ .x4 ++
  [movi .x0 0] ++ store oUsed .x0 ++ store oStatus .x0

def incomingSlots : List (Nat × Nat) :=
  [(256, oRandLen), (264, oScratch), (272, oScratchLen)]

def entry : List Instr := entryHeader ++ incomingSlots.flatMap (fun p => copySlot p.1 p.2)

def checkArgs : List Instr :=
  [.ldrSp .x0 oKey, .ldrSp .x1 oKeyLen, .ldrSp .x2 oPLen,
    .ldrSp .x3 oQLen, .ldrSp .x4 oScratch, .ldrSp .x5 oScratchLen]

def deriveArgs : List Instr :=
  copySlot oScratchLen 0 ++
  [.ldrSp .x0 oOut, .ldrSp .x1 oOutLen, .ldrSp .x2 oKey,
    .ldrSp .x3 oKeyLen, .ldrSp .x4 oPLen, .addSp .x5 oNonce,
    .ldrSp .x6 oQLen, .ldrSp .x7 oScratch]

def keepStatus : List Instr :=
  [.ldrSp .x30 RandomSign.oLink, .logic .orr .w .x0 .x0 .x0] ++ store oStatus .x0

def generate (derive : String) (deriveKey : Prog isa) : Prog isa :=
  .seq prepare
    (.ite (.zero .x .x0) (.block (store oStatus .x0))
      (.seq sample
        (.seq (.block (store oStatus .x0 ++ [.subImm .x .x4 .x0 1]))
          (.ite (.zero .x .x4)
            (.seq (.block deriveArgs) (.seq (.call derive deriveKey) (.block keepStatus)))
            (.block [])))))

def body (check derive : String) (checkParameters deriveKey : Prog isa) : Prog isa :=
  .seq (.block (entry ++ checkArgs))
    (.seq (.call check checkParameters)
      (.seq (.block [.ldrSp .x30 RandomSign.oLink, .logic .orr .w .x0 .x0 .x0])
        (.seq (.ite (.zero .x .x0) (.block []) (generate derive deriveKey)) RandomSign.finish)))

def code (check derive : String) (checkParameters deriveKey : Prog isa) : Prog isa :=
  .frame (.alloc frameBytes) (body check derive checkParameters deriveKey) (.free frameBytes)

end VG.Impl.Dsa.AArch64.GenerateKey
