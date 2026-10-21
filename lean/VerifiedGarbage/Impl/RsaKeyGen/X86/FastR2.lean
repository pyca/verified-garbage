module

public import VerifiedGarbage.Impl.Mont.X86.Power
public import VerifiedGarbage.Impl.Rsa.X86.KeyWs

/-! # Short R² setup for full-width RSA candidates

Starting at the top bit, n + 1 modular doublings reach 2^n R. Six
Montgomery squarings then reach R². This is the x86-64 key generation
strategy, with native paired-word arithmetic on i686.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.FastR2
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

def seed (n out : Nat) : Prog isa := setConstW (2 * n) out (2 ^ (64 * n - 1))

def doubles (M : Mod) (acc out : Nat) : Prog isa :=
  .seq (seed M.n out) (.seq (.block [.mov .esi (.imm (BitVec.ofNat 32 (M.n + 1)))])
    (doubleLoop M acc out))

def code (M : Mod) (acc out : Nat) (square : Prog isa) : Prog isa :=
  .seq (doubles M acc out) (VG.Impl.Rsa.X86.Keys.seqs (List.replicate 6 square))

end VG.Impl.RsaKeyGen.X86.FastR2
