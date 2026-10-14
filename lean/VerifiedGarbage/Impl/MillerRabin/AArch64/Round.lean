module

public import VerifiedGarbage.Impl.MillerRabin.AArch64.Core

/-! # Callable shared Miller–Rabin round on AArch64 -/

@[expose] public section

namespace VG.Impl.MillerRabin.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate

/-- Return the passing flag as 0 or 1, without branching on it. -/
def returnFlag : List Instr :=
  [ldh .x3 kFlag, movi .x4 1, .logic .and .x .x0 .x3 .x4]

/-- `(ws = x0, ws_len = x1)`: one round from the prepared workspace. -/
def round (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (seqs (preparedRound mul)) (.block returnFlag)

end VG.Impl.MillerRabin.AArch64
