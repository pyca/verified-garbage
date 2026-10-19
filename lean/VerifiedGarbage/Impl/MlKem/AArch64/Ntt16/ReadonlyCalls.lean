module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Readonly
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem

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
/-- `nttAtWith` and `nttInvAtWith` of a polynomial stored with 16-bit coefficients. -/
def nttAtWithW (off ns : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 off ++ ptrTo .x1 .x28 ns)) fwdW
def nttInvAtWithW (off ns : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 off ++ ptrTo .x1 .x28 ns)) invW
/-- The transform of a polynomial stored with 16-bit coefficients (`w16`) or 32-bit ones. -/
def nttAtR (w16 : Bool) : Nat → Nat → Prog isa := if w16 then nttAtWithW else nttAtWith
def nttInvAtR (w16 : Bool) : Nat → Nat → Prog isa := if w16 then nttInvAtWithW else nttInvAtWith
def nttAt (off : Nat) : Prog isa := nttAtWith off KEM.NS
def nttInvAt (off : Nat) : Prog isa := nttInvAtWith off KEM.NS

end VG.Impl.MlKem.AArch64.Ntt16.Readonly
