module

public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Generic
public import VerifiedGarbage.Spec.HashId

/-!
# Deterministic ECDSA over any curve, with the hash function as an argument: the contracts, on every target

**Trusted** (as every file in `Spec/`). For a curve's `Instance` of
`Spec/Ecdsa/Rfc6979/Generic.lean` (its curve, its bound on candidates and
its working space; its hash function is not used),
`vg_ecdsa_<curve>_rfc6979_sign`, in the module `ecdsa_<curve>_rfc6979`,
signs as `vg_ecdsa_<curve>_<hash>_sign` does (`Rfc6979.sign`), with the hash
function passed as a public `usize` argument, `hash`, rather than fixed by the
function's name: the number `HashId.hmac` gives the hash function, one of
`hashIds` (SHA-1 and the SHA-2 functions). The digest is a slice of `hLen`
octets rather than an array.

That `hash` is in `hashIds` and that the digest is its `hLen` octets are
preconditions. The hash function is public (an argument marked so,
`Sig.contract`), and may affect timing; nothing else changes.
-/

@[expose] public section

namespace VG.Spec.Ecdsa.Rfc6979

open Weierstrass

/-- The numbers (`HashId.hmac`) of the hash functions these functions take:
SHA-1, SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224 and SHA-512/256. -/
def hashIds : List Nat := [1, 2, 3, 4, 5, 6, 7]

namespace Instance

variable (I : Instance)

/-- `(out: *mut [u8; 2 len], d: *const [u8; len], digest: *const u8,
digest_len: usize, scratch: *mut [u64; I.scratchWords], hash: usize) -> u32`. -/
def signAnySig : Sig where
  params := [("out", .array true .u8 (2 * I.ecdsa.curve.len)),
    ("d", .array false .u8 I.ecdsa.curve.len), ("digest", .slice false .u8 "digest_len"),
    ("scratch", .array true .u64 I.scratchWords), ("hash", .int .usize true)]
  ret := some .u32

/-- RFC 6979's signature of the `digestLen` octets at `digest` with the
private key `d` and HMAC with the hash function `hash` names, and the number
of candidates tried; `none` if `hash` names none. -/
def anyResult (m : Mem) (d digest : Addr) (digestLen hash : Nat) :
    Option (Option (Nat × Nat) × Nat) :=
  (HashId.hmac hash).map fun H =>
    sign I.ecdsa.curve H digestLen I.tries (ofBytes (bytesAt m d I.ecdsa.curve.len))
      (bytesAt m digest digestLen)

/-- `signContract` of the instance with the hash function `hash` names
(`hashIds`), with the digest `digest_len = hLen` octets: the deterministic
signature of `digest` with the private key `d`, if there is one; then the
function returns 1 and writes it (`encode`) to `out`; otherwise it returns 0
and writes zeros to `out`. Constant time but for the hash function and the
number of candidates tried. -/
def signAnyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  I.signAnySig.contract A
    (pre := fun _out _d _digest digestLen _scratch hash _ =>
      hash.toNat ∈ hashIds ∧
        ∀ H, HashId.mgf1 hash.toNat = some H → digestLen.toNat = H.len)
    (post := fun out d digest digestLen _scratch hash m m' r =>
      match I.anyResult m d digest digestLen.toNat hash.toNat with
      | some (some rs, _) =>
        r = 1 ∧ bytesAt m' out (2 * I.ecdsa.curve.len) = encode I.ecdsa.curve rs
      | _ => r = 0 ∧ bytesAt m' out (2 * I.ecdsa.curve.len) =
          List.replicate (2 * I.ecdsa.curve.len) 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun _out d digest digestLen _scratch hash m =>
      [((I.anyResult m d digest digestLen.toNat hash.toNat).map (·.2)).getD 0])

/-- `vg_ecdsa_<curve>_rfc6979_sign` on every target. -/
def signAnyApi : Api where
  module := s!"ecdsa_{I.ecdsa.name}_rfc6979"
  name := s!"vg_ecdsa_{I.ecdsa.name}_rfc6979_sign"
  sig := I.signAnySig
  writeArgs := true
  contracts := some fun A stack => I.signAnyContract A stack
  summary := s!"Deterministic ECDSA signature generation over {I.ecdsa.title} with HMAC \
    with the hash function `hash` names (RFC 6979 §3.2; FIPS 186-5 §6.4.1): with the \
    private key `d` ({I.ecdsa.curve.len} bytes, most significant first), signs the hash \
    `digest` (`hLen` bytes, the length of `hash`'s values), deriving the per-message secret \
    number `k` from the key and the hash. Returns 1 and writes `r` then `s` \
    ({I.ecdsa.curve.len} bytes each, most significant first) to `*out`; or returns 0 and \
    writes zeros to `*out` if `d` is not in `[1, n-1]`, or if none of the first {I.tries} \
    candidates for `k` is suitable (which does not happen in practice). `hash` names the \
    hash function: {HashId.sha12Doc}.\n\n\
    Contract: `VG.Spec.Ecdsa.Rfc6979.Instance.signAnyContract`. Constant time but for the \
    number of candidates for `k` tried (almost always 1): timing may depend on the \
    pointers, `hash`, `digest_len` and that number, not otherwise on the key or the hash."
  safety := ["`hash` must be one of 1..=7.", HashId.lenSafety "digest_len" "hash",
    "The contents of `scratch` on return are unspecified and may contain secrets; \
    the caller must destroy them after use."]

end Instance

end VG.Spec.Ecdsa.Rfc6979
