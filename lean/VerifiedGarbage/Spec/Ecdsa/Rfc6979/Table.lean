module

public import VerifiedGarbage.Spec.Ecdsa.Rfc6979
public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.HmacTable

/-!
# Deterministic ECDSA with its HMAC given as a table

**Trusted** (as every file in `Spec/`). A `TableInstance` is a curve's
`Ecdsa.Instance` and the bound on candidates: `vg_ecdsa_<curve>_sign`, in
the module `ecdsa_<curve>`, signs as RFC 6979 does (`Rfc6979.sign`), with
the hash function given at run time: a last parameter `hmac`, a table of
the interface `Hmac` (`Spec/HmacTable.lean`), naming the hash function `H`
(`HmacTable.hashAt`) whose output `digest` is, and the HMAC over it
(`HmacTable.hmacOf H`, with `H`'s block size) that RFC 6979 uses, through
the table's functions. So one function serves every hash function, with
every implementation of its HMAC, rather than a function for each.

It takes the private key `d` (`len` octets, most significant first) and the
hash `digest`, a slice of `digest_len` octets, which must be `H`'s length (a
precondition, on a public length: which table `hmac` is is public,
`Abi.withTables`). It returns 1 and writes the signature (`encode`), or
returns 0 and writes zeros if `d` is not in `[1, n-1]` or none of the first
`tries` candidates is suitable.

The signature determines memory validity, separation and that the pointers
are public, through `Sig.contract`; the contents of every buffer are secret,
and the table's own memory is read-only. The number of candidates tried may
affect timing (`leak`), and which table `hmac` is: an implementation may
stop at the first suitable candidate. That number is 0 for an invalid key
and almost always 1 otherwise; the key and the hash may not affect timing
in any other way. `scratch` is `8 * scratchWords` bytes of working space
(8 KiB by default), whose contents on return are unspecified. `stack` is the
number of bytes below the stack pointer that an implementation's calls and
frames use. The function may overwrite its arguments passed in memory,
where the calling convention allows it (`writeArgs`).
-/

@[expose] public section

namespace VG.Spec.Ecdsa.Rfc6979

open Weierstrass
open Mgf1 (Hash)

/-- A curve and the bound on candidates, and their names in the Rust
interface. -/
structure TableInstance where
  ecdsa : Ecdsa.Instance
  /-- The most candidates `sign` tries. -/
  tries : Nat
  /-- Working space in `u64`s. -/
  scratchWords : Nat := Ecdsa.scratchWords

namespace TableInstance

variable (I : TableInstance)

/-- `(out: *mut [u8; 2 len], d: *const [u8; len], digest: *const u8,
digest_len: usize, scratch: *mut [u64; I.scratchWords],
hmac: *const [usize; 6]) -> u32`. -/
def signSig : Sig where
  params := [("out", .array true .u8 (2 * I.ecdsa.curve.len)),
    ("d", .array false .u8 I.ecdsa.curve.len), ("digest", .slice false .u8 "digest_len"),
    ("scratch", .array true .u64 I.scratchWords), ("hmac", HmacTable.param)]
  ret := some .u32

/-- RFC 6979's signature of `digest` with the private key `d` and HMAC over
`F`, of `H`'s digests, and the number of candidates tried. -/
def result (H : Hash) (F : Hmac.HashFunction) (m : Mem) (d digest : Addr) :
    Option (Nat × Nat) × Nat :=
  sign I.ecdsa.curve F H.len I.tries (ofBytes (bytesAt m d I.ecdsa.curve.len))
    (bytesAt m digest H.len)

/-- The number of candidates tried, which the function may reveal: that of
`result` for the hash function the table at `hmac` names. -/
def tried (ptrBits : Nat) (m : Mem) (d digest hmac : Addr) : Nat :=
  match HmacTable.hashAt ptrBits m hmac with
  | some H => match HmacTable.hmacOf H with
    | some F => (I.result H F m d digest).2
    | none => 0
  | none => 0

/-- For the hash function `hmac` names, the deterministic signature of
`digest` with the private key `d`, if there is one (`Rfc6979.sign`): then
the function returns 1 and writes it (`encode`) to `out`; otherwise it returns 0 and writes zeros to `out`. Constant time but for the
number of candidates tried and which table `hmac` is. -/
def signContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  I.signSig.contract A
    (pre := fun _out _d _digest digestLen _scratch hmac m =>
      ∀ H, HmacTable.hashAt A.ptrBits m hmac = some H →
        digestLen.toNat = H.len ∧ (HmacTable.hmacOf H).isSome)
    (post := fun out d digest _digestLen _scratch hmac m m' r =>
      ∀ H F, HmacTable.hashAt A.ptrBits m hmac = some H → HmacTable.hmacOf H = some F →
        match (I.result H F m d digest).1 with
        | some rs => r = 1 ∧ bytesAt m' out (2 * I.ecdsa.curve.len) = encode I.ecdsa.curve rs
        | none => r = 0 ∧ bytesAt m' out (2 * I.ecdsa.curve.len) =
            List.replicate (2 * I.ecdsa.curve.len) 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun _out d digest _digestLen _scratch hmac m =>
      [I.tried A.ptrBits m d digest hmac])

/-- `vg_ecdsa_<curve>_sign` on every target. -/
def signApi : Api where
  module := s!"ecdsa_{I.ecdsa.name}"
  name := s!"vg_ecdsa_{I.ecdsa.name}_sign"
  sig := I.signSig
  writeArgs := true
  contracts := some fun A stack => I.signContract A stack
  summary := s!"Deterministic ECDSA signature generation over {I.ecdsa.title} with HMAC \
    over the hash function of the table `hmac` (RFC 6979 §3.2; FIPS 186-5 §6.4.1): with the \
    private key `d` ({I.ecdsa.curve.len} bytes, most significant first), signs the hash at \
    `digest` (`digest_len` bytes, the hash function's output), deriving the per-message \
    secret number `k` from the key and the hash. Returns 1 and writes `r` then `s` \
    ({I.ecdsa.curve.len} bytes each, most significant first) to `*out`; or returns 0 and \
    writes zeros to `*out` if `d` is not in `[1, n-1]`, or if none of the first {I.tries} \
    candidates for `k` is suitable (which does not happen in practice).\n\n\
    Contract: `VG.Spec.Ecdsa.Rfc6979.TableInstance.signContract`. Constant time but for the \
    number of candidates for `k` tried (almost always 1) and which table `hmac` is: timing \
    may depend on the pointers, that number and the table, not otherwise on the key or the \
    hash."
  safety := ["`digest_len` must be the digest length of the hash function `hmac` names.",
    "The contents of `scratch` on return are unspecified and may contain secrets; the caller \
      must destroy them after use.",
    "`hmac` is a table of HMAC over the hash function of the digest, which RFC 6979 uses: \
      the one of `VG.Spec.Mgf1.hashes` at the index in its first word of data (the HMAC \
      tables of this crate, `fn_tables`, say which they name)."]

end TableInstance

end VG.Spec.Ecdsa.Rfc6979
