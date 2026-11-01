module

public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.TCB.Artifact

/-!
# ECDSA over any curve: the contract of its internal signature

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

`vg_ecdsa_<name>_sign` is the signature with a given per-message secret
number `k`, which the deterministic signatures of
`Spec/Ecdsa/Rfc6979/Generic.lean` call once they have derived `k`.

`sign` takes the private key `d`, the hash and the per-message secret
number `k`, each as `len` octets, most significant first. The hash is
`len` octets whose leftmost `N` bits (`N` the bit length of `n`, `nBits`)
are FIPS 186-5's `e`, as `hashToInt` reads them: its leftmost `len` octets
if it is longer. A shorter hash is padded on the left with zeros, which
leaves its integer value unchanged, when `n` has `8 len` bits (P-256,
P-384); otherwise its integer is shifted left by the `8 len - N` bits that
`hashToInt` drops (P-521: 7). `digestDoc` says which.

The signature determines memory validity, separation and that the pointers
are public, through `Sig.contract`; the contents of every buffer are secret.
`sign` returns 1 and writes the signature, or returns 0 and writes zeros:
the return value depends on secrets (though for an honest `k`, it is 0 with
negligible probability). `scratch` is 8 KiB of working space, whose contents
on return are unspecified. `stack` is the number of bytes below the stack
pointer that an implementation's calls and frames use. The functions may
overwrite their arguments passed in memory, where the calling convention
allows it (`writeArgs`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa

open VG.Spec VG.Spec.Ecdsa VG.Spec.Weierstrass

namespace Instance

variable (I : Spec.Ecdsa.Instance)

/-- `(out: *mut [u8; 2 len], d: *const [u8; len], digest: *const [u8; len],
k: *const [u8; len], scratch: *mut [u64; 1024]) -> u32`. -/
def signSig : Sig where
  params := [("out", .array true .u8 (2 * I.curve.len)), ("d", .array false .u8 I.curve.len),
    ("digest", .array false .u8 I.curve.len), ("k", .array false .u8 I.curve.len),
    ("scratch", .array true .u64 scratchWords)]
  ret := some .u32

/-- The signature of `digest` with the private key `d` and the
per-message secret number `k`, if there is one (`signWith`): then the
function returns 1 and writes it (`encode`) to `out`; otherwise it returns 0
and writes zeros to `out`. Constant time: no buffer contents may affect
timing. -/
def signContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (signSig I).contract A
    (post := fun out d digest k _scratch m m' r =>
      match signWith I.curve (ofBytes (bytesAt m d I.curve.len))
          (hashToInt I.curve (bytesAt m digest I.curve.len)) (ofBytes (bytesAt m k I.curve.len)) with
      | some rs => r = 1 ∧ bytesAt m' out (2 * I.curve.len) = encode I.curve rs
      | none => r = 0 ∧ bytesAt m' out (2 * I.curve.len) = List.replicate (2 * I.curve.len) 0)
    (writeArgs := true) (stack := stack)

end Instance

end VG.Proof.Ecdsa
