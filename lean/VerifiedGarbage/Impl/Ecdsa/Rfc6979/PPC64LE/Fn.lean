module

public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.PPC64LE
public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.P192.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.P224.PPC64LEComb
public import VerifiedGarbage.Impl.Ecdsa.P256.PPC64LEComb
public import VerifiedGarbage.Impl.Ecdsa.P384.PPC64LEComb
public import VerifiedGarbage.Impl.Ecdsa.P521.PPC64LEComb
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.PPC64LEComb
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.PPC64LEComb
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.PPC64LEComb
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.PPC64LEComb
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.PPC64LEComb
public import VerifiedGarbage.Spec.P192
public import VerifiedGarbage.Spec.P224
public import VerifiedGarbage.Spec.P256
public import VerifiedGarbage.Spec.P384
public import VerifiedGarbage.Spec.P521
public import VerifiedGarbage.Spec.Secp256k1
public import VerifiedGarbage.Spec.BrainpoolP256r1
public import VerifiedGarbage.Spec.BrainpoolP320r1
public import VerifiedGarbage.Spec.BrainpoolP384r1
public import VerifiedGarbage.Spec.BrainpoolP512r1

/-! # Deterministic ECDSA (RFC 6979) on PPC64LE: the functions as emitted

`vg_ecdsa_<curve>_sign`: its code (`Impl.Ecdsa.Rfc6979.PPC64LE.Cfg.sign`),
which calls HMAC through its table (the functions `f` an indirect call of the
table's may reach) and the curve's `vg_ecdsa_<curve>_sign_k`, then its
cleanup (`Impl.Scrub.PPC64LE.scrubAll`): the volatile registers cleared but
the 32 bits of its result, and the 784 bytes of stack its frames (640) and
the functions it calls (144: HMAC's `init` for a key of any length, its
table's word 0, for a key longer than a block) use zeroed.
Each curve's configuration (`<curve>Cfg`) gives the code's parameters. -/

@[expose] public section

namespace VG.Impl.Ecdsa.Rfc6979.PPC64LE.Fn

open VG VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrubAll)
open VG.Impl.RsaOaep.PPC64LE (Fns)

/-- `vg_ecdsa_<curve>_sign` as emitted, with the configuration `c`. -/
def sign (c : Cfg) : Prog isa := scrubAll 32 784 .all c.sign

/-- P-192's configuration, with the functions `f` its table's may be. -/
def p192Cfg (f : Fns) : Cfg where
  f := f
  w := 3
  len := 24
  n := Spec.P192.curve.n
  tries := 8
  coreN := "vg_ecdsa_p192_sign_k"
  coreC := Impl.Ecdsa.PPC64LE.signP192

/-- `vg_ecdsa_p192_sign`, with the functions `f` its table's may be. -/
def p192 (f : Fns) : Prog isa := sign (p192Cfg f)

/-- P-224's configuration, with the functions `f` its table's may be. -/
def p224Cfg (f : Fns) : Cfg where
  f := f
  w := 4
  len := 28
  n := Spec.P224.curve.n
  tries := 8
  coreN := "vg_ecdsa_p224_sign_k"
  coreC := Impl.Ecdsa.PPC64LE.signP224Comb

/-- `vg_ecdsa_p224_sign`, with the functions `f` its table's may be. -/
def p224 (f : Fns) : Prog isa := sign (p224Cfg f)

/-- P-256's configuration, with the functions `f` its table's may be. -/
def p256Cfg (f : Fns) : Cfg where
  f := f
  w := 4
  len := 32
  n := Spec.P256.curve.n
  tries := 8
  coreN := "vg_ecdsa_p256_sign_k"
  coreC := Impl.Ecdsa.PPC64LE.signP256Comb

/-- `vg_ecdsa_p256_sign`, with the functions `f` its table's may be. -/
def p256 (f : Fns) : Prog isa := sign (p256Cfg f)

/-- P-384's configuration, with the functions `f` its table's may be. -/
def p384Cfg (f : Fns) : Cfg where
  f := f
  w := 6
  len := 48
  n := Spec.P384.curve.n
  tries := 8
  coreN := "vg_ecdsa_p384_sign_k"
  coreC := Impl.Ecdsa.PPC64LE.signP384Comb

/-- `vg_ecdsa_p384_sign`, with the functions `f` its table's may be. -/
def p384 (f : Fns) : Prog isa := sign (p384Cfg f)

/-- P-521's configuration, with the functions `f` its table's may be. -/
def p521Cfg (f : Fns) : Cfg where
  f := f
  w := 9
  len := 66
  big := true
  sh := 7
  n := Spec.P521.curve.n
  tries := 8
  coreN := "vg_ecdsa_p521_sign_k"
  coreC := Impl.Ecdsa.PPC64LE.signP521Comb

/-- `vg_ecdsa_p521_sign`, with the functions `f` its table's may be. -/
def p521 (f : Fns) : Prog isa := sign (p521Cfg f)

/-- secp256k1's configuration, with the functions `f` its table's may be. -/
def secp256k1Cfg (f : Fns) : Cfg where
  f := f
  w := 4
  len := 32
  n := Spec.Secp256k1.curve.n
  tries := 8
  coreN := "vg_ecdsa_secp256k1_sign_k"
  coreC := Impl.Ecdsa.PPC64LE.signSecp256k1Comb

/-- `vg_ecdsa_secp256k1_sign`, with the functions `f` its table's may be. -/
def secp256k1 (f : Fns) : Prog isa := sign (secp256k1Cfg f)

/-- brainpoolP256r1's configuration, with the functions `f` its table's may be. -/
def brainpoolp256r1Cfg (f : Fns) : Cfg where
  f := f
  w := 4
  len := 32
  n := Spec.BrainpoolP256r1.curve.n
  tries := 128
  coreN := "vg_ecdsa_brainpoolp256r1_sign_k"
  coreC := Impl.Ecdsa.PPC64LE.signBrainpoolP256r1Comb

/-- `vg_ecdsa_brainpoolp256r1_sign`, with the functions `f` its table's may be. -/
def brainpoolp256r1 (f : Fns) : Prog isa := sign (brainpoolp256r1Cfg f)

/-- brainpoolP320r1's configuration, with the functions `f` its table's may be. -/
def brainpoolp320r1Cfg (f : Fns) : Cfg where
  f := f
  w := 5
  len := 40
  n := Spec.BrainpoolP320r1.curve.n
  tries := 128
  coreN := "vg_ecdsa_brainpoolp320r1_sign_k"
  coreC := Impl.Ecdsa.PPC64LE.signBrainpoolP320r1Comb

/-- `vg_ecdsa_brainpoolp320r1_sign`, with the functions `f` its table's may be. -/
def brainpoolp320r1 (f : Fns) : Prog isa := sign (brainpoolp320r1Cfg f)

/-- brainpoolP384r1's configuration, with the functions `f` its table's may be. -/
def brainpoolp384r1Cfg (f : Fns) : Cfg where
  f := f
  w := 6
  len := 48
  n := Spec.BrainpoolP384r1.curve.n
  tries := 128
  coreN := "vg_ecdsa_brainpoolp384r1_sign_k"
  coreC := Impl.Ecdsa.PPC64LE.signBrainpoolP384r1Comb

/-- `vg_ecdsa_brainpoolp384r1_sign`, with the functions `f` its table's may be. -/
def brainpoolp384r1 (f : Fns) : Prog isa := sign (brainpoolp384r1Cfg f)

/-- brainpoolP512r1's configuration, with the functions `f` its table's may be. -/
def brainpoolp512r1Cfg (f : Fns) : Cfg where
  f := f
  w := 8
  len := 64
  n := Spec.BrainpoolP512r1.curve.n
  tries := 128
  coreN := "vg_ecdsa_brainpoolp512r1_sign_k"
  coreC := Impl.Ecdsa.PPC64LE.signBrainpoolP512r1Comb

/-- `vg_ecdsa_brainpoolp512r1_sign`, with the functions `f` its table's may be. -/
def brainpoolp512r1 (f : Fns) : Prog isa := sign (brainpoolp512r1Cfg f)

end VG.Impl.Ecdsa.Rfc6979.PPC64LE.Fn
