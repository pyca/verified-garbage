import VerifiedGarbage.Impl.Ecdsa.AArch64
import VerifiedGarbage.Spec.Secp256k1

/-! # secp256k1 on AArch64, using complete general addition -/

namespace VG.Impl.Ecdsa.AArch64

open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

/-- Four-word arithmetic without a precomputed comb table. -/
def secp256k1 : Cfg := ⟨4, Spec.Secp256k1.curve, [], (0, 0), "", true⟩

namespace Secp256k1

/-- Slot 12 is free during point multiplication. The general formulas need
`3b`, while the shared setup retains `b` for peer validation. -/
def slots : RcbSlots := { secp256k1.rcbSlots with b3 := secp256k1.sl EXPP }

def ladderCfg : LadderCfg where
  M := secp256k1.MP'
  S := slots
  G := secp256k1.pt GX GY ONEP
  R := secp256k1.pt RX RY RZ
  D := secp256k1.pt DX DY DZ
  T := secp256k1.pt TX TY TZ
  bits := bitsAt secp256k1.n 0
  nbits := 256

def gMul : Prog isa :=
  .seq (.block (setConst 4 (secp256k1.sl EXPP) (secp256k1.mont (3 * secp256k1.C.b))))
    (ladder ladderCfg)

end Secp256k1

/-- `vg_ecdsa_secp256k1_sign`. -/
def signSecp256k1 : Prog isa := secp256k1.signWith Secp256k1.gMul

end VG.Impl.Ecdsa.AArch64
