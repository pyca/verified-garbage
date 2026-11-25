module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Readonly
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Forward
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Inverse

@[expose] public section
namespace VG.Impl.MlKem.AArch64.Ntt16.Readonly
open VG.AArch64 VG.Impl.MlKem.AArch64

/-- The transforms of the polynomial stored with 16-bit coefficients at `off` from `x28`: calls of
`vg_mlkem16_ntt` and `vg_mlkem16_inv_ntt`. They need no working space, which their callers have at
the second offset. -/
def nttAtWithW (off _ns : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 off)) (.call "vg_mlkem16_ntt" Forward.code)
def nttInvAtWithW (off _ns : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 off)) (.call "vg_mlkem16_inv_ntt" Inverse.code)

end VG.Impl.MlKem.AArch64.Ntt16.Readonly
