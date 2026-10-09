import VerifiedGarbage.Impl.Ecdsa.AArch64
import VerifiedGarbage.Spec.P192

/-! # p192 on AArch64, using complete general addition -/

namespace VG.Impl.Ecdsa.AArch64

open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

/-- Four-word arithmetic without a precomputed comb table. -/
def p192 : Cfg := ⟨4, Spec.P192.curve, [], (0, 0), "", true⟩

namespace P192

/-- Slot 12 is free during point multiplication. The general formulas need
`3b`, while the shared setup retains `b` for peer validation. -/
def slots : RcbSlots := { p192.rcbSlots with b3 := p192.sl EXPP }

def ladderCfg : LadderCfg where
  M := p192.MP'
  S := slots
  G := p192.pt GX GY ONEP
  R := p192.pt RX RY RZ
  D := p192.pt DX DY DZ
  T := p192.pt TX TY TZ
  bits := bitsAt p192.n 0
  nbits := 256

def gMul : Prog isa :=
  .seq (.block (setConst 4 (p192.sl EXPP) (p192.mont (3 * p192.C.b))))
    (ladder ladderCfg)

end P192

/-- `vg_ecdsa_p192_sign`. -/
def signP192 : Prog isa := p192.signWith P192.gMul

end VG.Impl.Ecdsa.AArch64
