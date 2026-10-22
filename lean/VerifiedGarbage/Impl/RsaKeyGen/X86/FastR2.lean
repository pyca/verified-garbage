module

public import VerifiedGarbage.Impl.Mont.X86.Power
public import VerifiedGarbage.Impl.Rsa.X86.KeyWs

/-! # Short R² setup for RSA candidates and other odd moduli

Starting at the top bit, n + 1 modular doublings reach 2^n R. Six
Montgomery squarings then reach R². This is the x86-64 key generation
strategy, with native paired-word arithmetic on i686. `codeAt` starts at
any power `2^e` below the modulus, with `65 n − e` doublings, for a modulus
narrower than its words.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.FastR2
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

/-- The seed `2^e`, below the modulus. -/
def seedAt (n e out : Nat) : Prog isa := setConstW (2 * n) out (2 ^ e)

/-- From the seed `2^e`, `65 n − e` doublings reach `2^n R`. -/
def doublesAt (M : Mod) (e acc out : Nat) : Prog isa :=
  .seq (seedAt M.n e out) (.seq (.block [.mov .esi (.imm (BitVec.ofNat 32 (M.n + 64 * M.n - e)))])
    (doubleLoop M acc out))

def codeAt (M : Mod) (e acc out : Nat) (square : Prog isa) : Prog isa :=
  .seq (doublesAt M e acc out) (VG.Impl.Rsa.X86.Keys.seqs (List.replicate 6 square))

/-- A full-width modulus: the seed is its top bit. -/
def seed (n out : Nat) : Prog isa := seedAt n (64 * n - 1) out

def doubles (M : Mod) (acc out : Nat) : Prog isa := doublesAt M (64 * M.n - 1) acc out

def code (M : Mod) (acc out : Nat) (square : Prog isa) : Prog isa := codeAt M (64 * M.n - 1) acc out square

end VG.Impl.RsaKeyGen.X86.FastR2
