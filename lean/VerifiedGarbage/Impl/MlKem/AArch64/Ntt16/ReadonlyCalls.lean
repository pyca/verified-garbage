module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Readonly
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Fast

@[expose] public section
namespace VG.Impl.MlKem.AArch64.Ntt16.Readonly
open VG.AArch64 VG.Impl.MlKem.AArch64

/-- The transforms of the polynomial stored with 16-bit coefficients at `off` from `x28`, with
working space at `ns`: the forward transform a call of `vg_mlkem16_ntt`. -/
def nttAtWithW (off ns : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 off ++ ptrTo .x1 .x28 ns)) (.call "vg_mlkem16_ntt" Fast.fwdFast)
def nttInvAtWithW (off ns : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 off ++ ptrTo .x1 .x28 ns)) invW

end VG.Impl.MlKem.AArch64.Ntt16.Readonly
