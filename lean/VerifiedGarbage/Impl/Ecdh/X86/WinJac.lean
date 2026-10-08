import VerifiedGarbage.Impl.Ecdh.X86.Window
import VerifiedGarbage.Impl.Weierstrass.X86.WinJac

/-! P-256 ECDH's constant-time Jacobian windows in the existing 8192-byte scratch area. -/
namespace VG.Impl.Ecdh.X86
open VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Impl.Ecdsa.X86
namespace Cfg
variable (c : Impl.Ecdsa.X86.Cfg)

/-- The selected entry is below the field workspace. The two packed tables
occupy 5200..7760, beyond the exponent and scalar bit tables. -/
def jwinCfg : JacWinCfg where
  M := c.MP'
  F := c.SP
  S := { c.rcbSlots with b3 := c.sl EM }
  P := c.pt Impl.Ecdh.X86.PX Impl.Ecdh.X86.PY ONEP
  R := c.pt RX RY RZ
  D := c.pt DX DY DZ
  T := 2640
  neg := c.sl PT
  zero := c.sl ZERO
  bits := windowBits
  tbl := 5200
  J := 52
  one := c.mont 1

/-- Extend the scalar, add the width-five signed-digit bias, and expand
its bits. Fifty-two digits hold all 256 scalar bits and the recoding carry. -/
def jwinPrep : Prog isa :=
  .seq (.block (copy 8 3520 (c.sl K) ++ setConst 1 3552 0 ++
    setConst 5 3560 (JacWinCfg.offset 52) ++
    chain { c.MP' with n := 5 } .add .adc 3600 3520 3560))
    (bits 3600 windowBits 40)

def jwinMul : Prog isa :=
  .seq (.block (setConst c.n (c.sl EM) (c.mont c.C.b))) <|
  .seq (jwinPrep c) (jwinCfg c).window

def exchangeJacWindow : Prog isa :=
  .seq (prefix' c) <| .seq (.block (peer c)) <| .seq (validate c) <|
  .seq (jwinMul c) <| .seq c.pPow (middle c)

end Cfg
end VG.Impl.Ecdh.X86
