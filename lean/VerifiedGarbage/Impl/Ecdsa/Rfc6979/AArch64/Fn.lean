module

public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.AArch64
public import VerifiedGarbage.Impl.P256.Booth
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
than every digest (`big`, with the shift `sh`), at most 8 candidates, and
the signature with a given `k` (`coreC`, named `coreN`). -/
def cfg (E : Impl.Ecdsa.AArch64.Cfg) (big : Bool) (sh : Nat) (coreN : String) (coreC : Prog isa)
    (hs : List Hash) : Cfg :=
  ⟨fnsOf hs, E.n, E.C.len, big, sh, E.C.n, 8, coreN, coreC⟩

/-- `vg_ecdsa_<curve>_sign` as emitted: its frame of 256 bytes and the 48
words it pushes. -/
def sign (E : Impl.Ecdsa.AArch64.Cfg) (big : Bool) (sh : Nat) (coreN : String) (coreC : Prog isa)
    (hs : List Hash) : Prog isa :=
  scrubOf 640 32 (signCode (cfg E big sh coreN coreC hs))

/-- `vg_ecdsa_p256_sign`, with the tables of `hs`. -/
def p256 (hs : List Hash) : Prog isa :=
  sign Impl.Ecdsa.AArch64.p256 false 0 "vg_ecdsa_p256_sign_k" Impl.P256.Booth.sign hs

end VG.Impl.Ecdsa.Rfc6979.AArch64.Fn
