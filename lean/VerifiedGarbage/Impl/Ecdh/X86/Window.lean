module

public import VerifiedGarbage.Impl.Ecdh.X86
public import VerifiedGarbage.Impl.Weierstrass.X86.Window

/-! # Shared x86 P-256 variable-base window code for ECDH and verification -/

@[expose] public section

namespace VG.Impl.Ecdh.X86
open VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Impl.Ecdsa.X86
namespace Cfg
variable (c : Impl.Ecdsa.X86.Cfg)

/-- The table of the bits of the recoded scalar (320 bytes): past the
tables of bits of `bitsAt`. -/
def windowBits : Nat := 4880

/-- The eight projective points and recoding buffers fit in the existing scratch area,
below the field arithmetic's own working space. The exponent tables and saved
fixed-base result remain intact. -/
def windowCfg : WinCfg where
  M := c.MP'
  S := { c.rcbSlots with b3 := c.sl EM }
  P := c.pt Impl.Ecdh.X86.PX Impl.Ecdh.X86.PY ONEP
  R := c.pt RX RY RZ
  E := c.pt TX TY TZ
  D := c.pt DX DY DZ
  neg := c.sl PT
  zero := c.sl ZERO
  bits := windowBits
  tbl := 2640
  J := 65
  one := c.mont 1

end Cfg
end VG.Impl.Ecdh.X86
