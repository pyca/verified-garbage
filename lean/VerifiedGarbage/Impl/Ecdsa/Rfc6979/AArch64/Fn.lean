module

public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.AArch64
public import VerifiedGarbage.Impl.P256.Booth
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.AArch64.Comb
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.AArch64.Comb
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.AArch64.Comb
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.AArch64.Comb
public import VerifiedGarbage.Impl.Ecdsa.P192.AArch64
public import VerifiedGarbage.Impl.Ecdsa.P224.AArch64
public import VerifiedGarbage.Impl.Ecdsa.P384.AArch64
public import VerifiedGarbage.Impl.Ecdsa.P384.AArch64.Cfg
public import VerifiedGarbage.Impl.Ecdsa.P521.AArch64
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.AArch64
public import VerifiedGarbage.Impl.Residue.AArch64.Writes

/-! # Deterministic ECDSA (RFC 6979) on AArch64: the functions as emitted

`vg_ecdsa_<curve>_sign`: its code, which calls HMAC through its table and the
curve's `vg_ecdsa_<curve>_sign_k`, then its cleanup: the registers the code
may write cleared, and its stack zeroed (`scrubOf`). -/

@[expose] public section

namespace VG.Impl.Ecdsa.Rfc6979.AArch64.Fn

open VG VG.AArch64
open VG.Impl.Residue.AArch64 (scrubOf)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns)

/-- For each of the HMAC functions the code calls through its table, that
function of each of the hash functions `hs`: what an indirect call may
reach. -/
def fnsOf (hs : List Hash) : Fns :=
  ⟨hs.map fun h => (h.hmacInitN, h.hmacInit), hs.map fun h => (h.updN, h.updC),
    hs.map fun h => (h.hmacFinN, h.hmacFin)⟩

/-- The code's parameters on the curve `E`: whether its scalars are longer
than every digest (`big`, with the shift `sh`), at most `tries` candidates,
and the signature with a given `k` (`coreC`, named `coreN`). -/
def cfg (E : Impl.Ecdsa.AArch64.Cfg) (big : Bool) (sh tries : Nat) (coreN : String) (coreC : Prog isa)
    (hs : List Hash) : Cfg :=
  ⟨fnsOf hs, E.n, E.C.len, big, sh, E.C.n, tries, coreN, coreC⟩

/-- `vg_ecdsa_<curve>_sign` as emitted: its frame of 256 bytes and the 48
words it pushes. -/
def sign (E : Impl.Ecdsa.AArch64.Cfg) (big : Bool) (sh tries : Nat) (coreN : String)
    (coreC : Prog isa) (hs : List Hash) : Prog isa :=
  scrubOf 640 32 (signCode (cfg E big sh tries coreN coreC hs))

/-- `vg_ecdsa_p256_sign`, with the tables of `hs`. -/
def p256 (hs : List Hash) : Prog isa :=
  sign Impl.Ecdsa.AArch64.p256 false 0 8
    "vg_ecdsa_p256_sign_k" Impl.P256.Booth.sign hs

/-- `vg_ecdsa_p384_sign`, with the tables of `hs`. -/
def p384 (hs : List Hash) : Prog isa :=
  sign Impl.Ecdsa.AArch64.p384 false 0 8
    "vg_ecdsa_p384_sign_k" Impl.Ecdsa.AArch64.signP384 hs

/-- `vg_ecdsa_p521_sign`, with the tables of `hs`. -/
def p521 (hs : List Hash) : Prog isa :=
  sign Impl.Ecdsa.AArch64.p521 true 7 8
    "vg_ecdsa_p521_sign_k" Impl.Ecdsa.AArch64.signP521 hs

/-- `vg_ecdsa_p224_sign`, with the tables of `hs`. -/
def p224 (hs : List Hash) : Prog isa :=
  sign Impl.Ecdsa.AArch64.p224 false 0 8
    "vg_ecdsa_p224_sign_k" Impl.Ecdsa.AArch64.signP224 hs

/-- `vg_ecdsa_p192_sign`, with the tables of `hs`. -/
def p192 (hs : List Hash) : Prog isa :=
  sign Impl.Ecdsa.AArch64.p192 false 0 8
    "vg_ecdsa_p192_sign_k" Impl.Ecdsa.AArch64.signP192 hs

/-- `vg_ecdsa_secp256k1_sign`, with the tables of `hs`. -/
def secp256k1 (hs : List Hash) : Prog isa :=
  sign Impl.Ecdsa.AArch64.secp256k1 false 0 8
    "vg_ecdsa_secp256k1_sign_k" Impl.Ecdsa.AArch64.signSecp256k1 hs

/-- `vg_ecdsa_brainpoolp256r1_sign`, with the tables of `hs`. -/
def brainpoolp256r1 (hs : List Hash) : Prog isa :=
  sign Impl.Ecdsa.AArch64.BrainpoolP256r1.combCfg false 0 128
    "vg_ecdsa_brainpoolp256r1_sign_k" Impl.Ecdsa.AArch64.BrainpoolP256r1.signComb hs

/-- `vg_ecdsa_brainpoolp320r1_sign`, with the tables of `hs`. -/
def brainpoolp320r1 (hs : List Hash) : Prog isa :=
  sign Impl.Ecdsa.AArch64.BrainpoolP320r1.combCfg false 0 128
    "vg_ecdsa_brainpoolp320r1_sign_k" Impl.Ecdsa.AArch64.BrainpoolP320r1.signComb hs

/-- `vg_ecdsa_brainpoolp384r1_sign`, with the tables of `hs`. -/
def brainpoolp384r1 (hs : List Hash) : Prog isa :=
  sign Impl.Ecdsa.AArch64.BrainpoolP384r1.combCfg false 0 128
    "vg_ecdsa_brainpoolp384r1_sign_k" Impl.Ecdsa.AArch64.BrainpoolP384r1.signComb hs

/-- `vg_ecdsa_brainpoolp512r1_sign`, with the tables of `hs`. -/
def brainpoolp512r1 (hs : List Hash) : Prog isa :=
  sign Impl.Ecdsa.AArch64.BrainpoolP512r1.combCfg false 0 128
    "vg_ecdsa_brainpoolp512r1_sign_k" Impl.Ecdsa.AArch64.BrainpoolP512r1.signComb hs

end VG.Impl.Ecdsa.Rfc6979.AArch64.Fn
