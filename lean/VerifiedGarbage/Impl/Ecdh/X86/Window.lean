import VerifiedGarbage.Impl.Ecdh.X86
import VerifiedGarbage.Impl.Weierstrass.X86.Window

/-! # Shared x86 P-256 variable-base window code for ECDH and verification -/
namespace VG.Impl.Ecdh.X86
open VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Impl.Ecdsa.X86
namespace Cfg
variable (c : Impl.Ecdsa.X86.Cfg)

/-- The eight projective points and recoding buffers fit in the existing scratch area.
The exponent tables and saved fixed-base result remain intact. -/
def windowCfg : WinCfg where
  M := c.MP'
  S := { c.rcbSlots with b3 := c.sl EM }
  P := c.pt Impl.Ecdh.X86.PX Impl.Ecdh.X86.PY ONEP
  R := c.pt RX RY RZ
  E := c.pt TX TY TZ
  D := c.pt DX DY DZ
  neg := c.sl PT
  zero := c.sl ZERO
  bits := 3700
  tbl := 2640
  J := 65
  one := c.mont 1

/-- Pad the scalar to 320 bits, add the signed-window bias, then expand its bits.
The extra high word retains the carry from the original 256-bit scalar. -/
def windowPrep (src : Nat) : Prog isa :=
  .seq (.block (copy 8 3520 src ++ setConst 1 3552 0 ++
    setConst 5 3560 (WinCfg.offset 65) ++
    chain { c.MP' with n := 5 } .add .adc 3600 3520 3560))
    (bits 3600 3700 40)

/-- Variable-base multiplication for P-256; `b` is initialized independently
of the fixed-base comb's choice of implementation. -/
def windowMul (src : Nat) : Prog isa :=
  .seq (.block (setConst c.n (c.sl EM) (c.mont c.C.b))) <|
  .seq (windowPrep c src) (WinCfg.window (windowCfg c) 4040)

/-- ECDH with signed windows for the variable-base product. -/
def exchangeWindow : Prog isa :=
  .seq (prefix' c) <| .seq (.block (peer c)) <| .seq (validate c) <|
  .seq (windowMul c (c.sl K)) <| .seq (pow c.powP c.wk) (middle c)

end Cfg
end VG.Impl.Ecdh.X86
