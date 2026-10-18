module

public import VerifiedGarbage.Impl.Rsa.AArch64.Keys

/-! Initialize the shared primality workspace from arbitrary scratch contents. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys

def workspaceHead (w : Nat) : List Instr :=
  [movi .x12 w, sth .x12 sW, movi .x3 0, sth .x3 sMinv]

def workspaceStride (w : Nat) : List Instr :=
  [movi .x3 (8 * (w + 2)), sth .x3 sStride]

def workspace (w : Nat) : Prog isa :=
  .seq (.block (workspaceHead w)) (.seq (.block setBases) (.block (workspaceStride w)))

end VG.Impl.Dsa.AArch64.Generation
