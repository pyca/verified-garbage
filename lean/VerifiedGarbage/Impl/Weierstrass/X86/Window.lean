module

public import VerifiedGarbage.Impl.Weierstrass.X86.TComb
public import VerifiedGarbage.Impl.Weierstrass.JacMul

/-!
# Signed four-bit variable-base multiplication on 32-bit x86

Build [1..8]P in scratch memory. Each recoded digit uses four Jacobian
doublings, a constant-time scan of all eight projective points, conditional
negation, and a complete addition. The scalar is recoded by adding
`8 * ((16^J - 1) / 15)` before producing its table of bits.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.X86

open VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass

namespace WinCfg

variable (K : WinCfg) (F : Impl.Weierstrass.Mont.Modulus)

/-- The window method as the comb sees it, for the digits and their
negation: windows of 4 bits at `bits`. -/
def tc : TCombCfg where
  M := K.M
  F := F
  ptr := 0
  S := K.S
  A := K.R
  E := K.E
  D := K.D
  neg := K.neg
  zero := K.zero
  bits := K.bits
  kbytes := 4 * K.J
  tsym := ""
  w := 4
  J := K.J
  start := (0, 0)
  one := K.one

/-- The slots of zero, as a point (`toJ` and `fromJ` add zero to copy). -/
def zeroPt : Pt := ⟨K.zero, K.zero, K.zero⟩

end WinCfg

end VG.Impl.Weierstrass.X86
