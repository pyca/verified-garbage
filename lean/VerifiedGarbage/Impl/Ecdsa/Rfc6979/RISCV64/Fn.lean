module

public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Sign
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.P192
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.P224
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.P521
public import VerifiedGarbage.Impl.Ecdsa.P192.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.P224.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.P256.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.P384.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.P521.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.RISCV64.Ecdsa
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.RISCV64.Ecdsa
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.RISCV64.Ecdsa
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.RISCV64.Ecdsa
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.RISCV64.Ecdsa
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-! # Deterministic ECDSA (RFC 6979) on RISC-V: the functions as emitted

`vg_ecdsa_<curve>_sign`: its code, which calls HMAC through its table (the
functions `f` an indirect call of the table's may reach) and the curve's
`vg_ecdsa_<curve>_sign_k`, then its cleanup (`Impl.Scrub.RISCV64.scrubAll`): the
caller-saved registers cleared but the 32 bits of its result, and the 1024
bytes of stack it uses zeroed (its frame of 512 bytes, and at most 512 below
it for the functions it calls). Each curve's configuration (`<curve>Cfg`)
gives the code's parameters. -/

@[expose] public section

namespace VG.Impl.Ecdsa.Rfc6979.RISCV64.Fn

open VG VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrubAll)

/-- `vg_ecdsa_<curve>_sign` as emitted, with the configuration `c`. -/
def sign (c : Cfg) : Prog isa := scrubAll 32 1024 c.sign

/-- P-192's configuration, with the functions `f` its table's may be. -/
def p192Cfg (f : Fns) : Cfg where
  f := f
  FN := Impl.Ecdsa.RISCV64.p192Order
  coreN := "vg_ecdsa_p192_sign_k"
  coreC := Impl.Ecdsa.RISCV64.P192.signP192
  tries := 8
  nw := 4
  Q := 24
  G := 24

/-- `vg_ecdsa_p192_sign`, with the functions `f` its table's may be. -/
def p192 (f : Fns) : Prog isa := sign (p192Cfg f)

/-- P-224's configuration, with the functions `f` its table's may be. -/
def p224Cfg (f : Fns) : Cfg where
  f := f
  FN := Impl.Ecdsa.RISCV64.p224Order
  coreN := "vg_ecdsa_p224_sign_k"
  coreC := Impl.Ecdsa.RISCV64.P224.signP224
  tries := 8
  nw := 4
  Q := 28
  G := 28

/-- `vg_ecdsa_p224_sign`, with the functions `f` its table's may be. -/
def p224 (f : Fns) : Prog isa := sign (p224Cfg f)

/-- P-256's configuration, with the functions `f` its table's may be. -/
def p256Cfg (f : Fns) : Cfg where
  f := f
  FN := Impl.Ecdsa.RISCV64.p256Order
  coreN := "vg_ecdsa_p256_sign_k"
  coreC := Impl.Ecdsa.RISCV64.Sign.signP256
  tries := 8
  nw := 4
  Q := 32
  G := 32

/-- `vg_ecdsa_p256_sign`, with the functions `f` its table's may be. -/
def p256 (f : Fns) : Prog isa := sign (p256Cfg f)

/-- P-384's configuration, with the functions `f` its table's may be. -/
def p384Cfg (f : Fns) : Cfg where
  f := f
  FN := Impl.Ecdsa.RISCV64.p384Order
  coreN := "vg_ecdsa_p384_sign_k"
  coreC := Impl.Ecdsa.RISCV64.Sign.signP384
  tries := 8
  nw := 6
  Q := 48
  G := 48

/-- `vg_ecdsa_p384_sign`, with the functions `f` its table's may be. -/
def p384 (f : Fns) : Prog isa := sign (p384Cfg f)

/-- P-521's configuration, with the functions `f` its table's may be. -/
def p521Cfg (f : Fns) : Cfg where
  f := f
  FN := Impl.Ecdsa.RISCV64.p521Order
  coreN := "vg_ecdsa_p521_sign_k"
  coreC := Impl.Ecdsa.RISCV64.P521.signP521
  tries := 8
  nw := 9
  Q := 66
  big := true
  G := 64

/-- `vg_ecdsa_p521_sign`, with the functions `f` its table's may be. -/
def p521 (f : Fns) : Prog isa := sign (p521Cfg f)

/-- secp256k1's configuration, with the functions `f` its table's may be. -/
def secp256k1Cfg (f : Fns) : Cfg where
  f := f
  FN := Impl.Ecdsa.RISCV64.secp256k1Order
  coreN := "vg_ecdsa_secp256k1_sign_k"
  coreC := Impl.Ecdsa.RISCV64.signSecp256k1
  tries := 8
  nw := 4
  Q := 32
  G := 32

/-- `vg_ecdsa_secp256k1_sign`, with the functions `f` its table's may be. -/
def secp256k1 (f : Fns) : Prog isa := sign (secp256k1Cfg f)

/-- brainpoolP256r1's configuration, with the functions `f` its table's may be. -/
def brainpoolp256r1Cfg (f : Fns) : Cfg where
  f := f
  FN := Impl.Ecdsa.RISCV64.brainpoolp256r1Order
  coreN := "vg_ecdsa_brainpoolp256r1_sign_k"
  coreC := Impl.Ecdsa.RISCV64.signBrainpoolP256r1
  tries := 128
  nw := 4
  Q := 32
  G := 32

/-- `vg_ecdsa_brainpoolp256r1_sign`, with the functions `f` its table's may be. -/
def brainpoolp256r1 (f : Fns) : Prog isa := sign (brainpoolp256r1Cfg f)

/-- brainpoolP320r1's configuration, with the functions `f` its table's may be. -/
def brainpoolp320r1Cfg (f : Fns) : Cfg where
  f := f
  FN := Impl.Ecdsa.RISCV64.brainpoolp320r1Order
  coreN := "vg_ecdsa_brainpoolp320r1_sign_k"
  coreC := Impl.Ecdsa.RISCV64.signBrainpoolP320r1
  tries := 128
  nw := 5
  Q := 40
  G := 40

/-- `vg_ecdsa_brainpoolp320r1_sign`, with the functions `f` its table's may be. -/
def brainpoolp320r1 (f : Fns) : Prog isa := sign (brainpoolp320r1Cfg f)

/-- brainpoolP384r1's configuration, with the functions `f` its table's may be. -/
def brainpoolp384r1Cfg (f : Fns) : Cfg where
  f := f
  FN := Impl.Ecdsa.RISCV64.brainpoolp384r1Order
  coreN := "vg_ecdsa_brainpoolp384r1_sign_k"
  coreC := Impl.Ecdsa.RISCV64.signBrainpoolP384r1
  tries := 128
  nw := 6
  Q := 48
  G := 48

/-- `vg_ecdsa_brainpoolp384r1_sign`, with the functions `f` its table's may be. -/
def brainpoolp384r1 (f : Fns) : Prog isa := sign (brainpoolp384r1Cfg f)

/-- brainpoolP512r1's configuration, with the functions `f` its table's may be. -/
def brainpoolp512r1Cfg (f : Fns) : Cfg where
  f := f
  FN := Impl.Ecdsa.RISCV64.brainpoolp512r1Order
  coreN := "vg_ecdsa_brainpoolp512r1_sign_k"
  coreC := Impl.Ecdsa.RISCV64.signBrainpoolP512r1
  tries := 128
  nw := 8
  Q := 64
  G := 64

/-- `vg_ecdsa_brainpoolp512r1_sign`, with the functions `f` its table's may be. -/
def brainpoolp512r1 (f : Fns) : Prog isa := sign (brainpoolp512r1Cfg f)

end VG.Impl.Ecdsa.Rfc6979.RISCV64.Fn
