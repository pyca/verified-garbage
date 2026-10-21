module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Readonly
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Fast

@[expose] public section
namespace VG.Impl.MlKem.AArch64.Ntt16.Readonly
open VG.AArch64 VG.Impl.MlKem.AArch64

def fwdName : String := "vg_mlkem_ntt_readonly"
def invName : String := "vg_mlkem_inv_ntt_readonly"
def fwdConsts := [("VG_MLKEM_NTT16_ZETAS",words 16 tableHalves)]
def invConstsTable := [("VG_MLKEM_INTT16_ZETAS",words 16 invTableHalves)]

def nttAtWith (off ns : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 off ++ ptrTo .x1 .x28 ns)) fwd
def nttInvAtWith (off ns : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 off ++ ptrTo .x1 .x28 ns)) inv
/-- `nttAtWith` and `nttInvAtWith` of a polynomial stored with 16-bit coefficients: the
forward transform a call of `vg_mlkem16_ntt`. -/
def nttAtWithW (off ns : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 off ++ ptrTo .x1 .x28 ns)) (.call "vg_mlkem16_ntt" Fast.fwdFast)
def nttInvAtWithW (off ns : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 off ++ ptrTo .x1 .x28 ns)) invW
def nttAt (off : Nat) : Prog isa := nttAtWith off KEM.NS
def nttInvAt (off : Nat) : Prog isa := nttInvAtWith off KEM.NS

end VG.Impl.MlKem.AArch64.Ntt16.Readonly
