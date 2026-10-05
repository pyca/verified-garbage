import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
import VerifiedGarbage.Proof.Ecdsa.X86.P521.Verified
import VerifiedGarbage.Proof.Ecdsa.X86.P521.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# Deterministic ECDSA on x86 (32-bit): P-521

P-521 as the proof's curve (`p521`): scalars of 9 64-bit words and 66
bytes, longer than any hash function's output (`wide`), the order `n` of
521 bits, so that the signature drops 7 bits of a 66-byte digest, and
`vg_ecdsa_p521_sign`, proven correct (given the group law) and constant time
against its contract (`coreK` at P-521's sizes, which is
`Proof.Ecdsa.X86.P521.signX86`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86

/-- P-521, with the group law `hL`. -/
def p521 (hL : Weierstrass.Law Spec.P521.curve) : RfcCurve where
  E := Impl.Ecdsa.X86.p521
  inst := Spec.Ecdsa.P521.inst
  curve := rfl
  wide := true
  sizes := ⟨rfl, rfl, Proof.Ecdsa.X86.P521.p521_nBits⟩
  n_lt := by decide +kernel
  sh := 7
  sh_eq := Proof.Ecdsa.X86.P521.p521_sh
  coreN := Spec.Ecdsa.P521.signApi.name
  coreC := Impl.Ecdsa.X86.signP521
  coreX := Proof.Ecdsa.X86.P521.sign_x86 hL
  coreCT := Proof.Ecdsa.X86.P521.sign_ct
  coreNs := NoSp.of_all (by lit_decide)
  coreStack := by lit_decide
  reduceT := nofun

end VG.Proof.Ecdsa.Rfc6979.X86
