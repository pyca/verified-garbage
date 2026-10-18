module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Hash
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.SeedAdd
public import VerifiedGarbage.Impl.Dsa.AArch64.Random

/-! Wrapped-seed hash contributions in descending contribution order. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)

def seedInputArgs (j : Nat) : List Instr :=
  [.ldrSp .x1 8, .ldrSp .x2 24, .ldrSp .x0 16, .addImm .x .x0 .x0 j]

def useWrappedSeed : List Instr :=
  [.ldrSp .x0 24, .strSp .x0 sLab]

def hashCopyArgs (len count j : Nat) : List Instr :=
  [.ldrSp .x12 sScr, .addImm .x .x12 .x12 oDig,
   .ldrSp .x2 32, .addImm .x .x2 .x2 ((count - j) * len), movi .x9 len]

def pSeedHash (H : Hash) (len j : Nat) : Prog isa :=
  .seq (.block (seedInputArgs j)) (.seq (seedAdd len) (hashLabel H oDig))

def pHashOne (H : Hash) (len count j : Nat) : Prog isa :=
  .seq (pSeedHash H len j) (.seq (.block (hashCopyArgs len count j)) Random.copyRest)

def pHashPrefix (H : Hash) (len count : Nat) : Nat → Prog isa
  | 0 => .block []
  | k + 1 => .seq (pHashPrefix H len count k) (pHashOne H len count k)

def pHashes (H : Hash) (len count : Nat) : Prog isa :=
  pHashPrefix H len count (count + 1)

end VG.Impl.Dsa.AArch64.Generation
