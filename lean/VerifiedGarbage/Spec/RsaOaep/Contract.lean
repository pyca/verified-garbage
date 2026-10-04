import VerifiedGarbage.Spec.RsaOaep
import VerifiedGarbage.Spec.RsaPss.Contract

/-!
# RSAES-OAEP: the contracts, on every target

**Trusted** (as every file in `Spec/`). For the hash function `H` and MGF1
with the hash function `G` (any two of `Mgf1.hashes`), in the module
`rsa_oaep_<H>_mgf1_<G>`:

* `vg_rsa_oaep_<H>_mgf1_<G>_encrypt`: `RSAES-OAEP-ENCRYPT` of a message with
  a label and a seed (`RsaOaep.encrypt`).

Numbers are as in `Spec/Rsa/Contract.lean`: slices of octets, most
significant first, with the modulus `n` of `n_len` octets, from 64 to 1024,
and `e` of at most `n_len`. The seed is `hLen` octets, an array. These are
preconditions, on the public lengths; everything about the values is
checked: the function returns 1 and writes the ciphertext, or returns 0 and
writes zeros.

The signature determines memory validity, separation and that the pointers
and lengths (among them the message's and the label's) are public, through
`Sig.contract`. The public key, `n` and `e`, is public too, and may affect
timing (`leak`). Nothing else is: the message, the label, the seed and
everything computed from them.

`scratch` is working space of at least `RsaPss.scratchWords n_len` `u64`s,
whose contents on return are unspecified. `stack` is the number of bytes
below the stack pointer that an implementation's calls and frames use. The
functions may overwrite their arguments passed in memory, where the calling
convention allows it (`writeArgs`).
-/

namespace VG.Spec.RsaOaep

open Mgf1 (Hash)
open Rsa (bytesAt lenValid written)
open RsaPss (scratchWords scratchSafety)

variable (H G : Hash)

/-! ## `vg_rsa_oaep_<H>_mgf1_<G>_encrypt` -/

/-- `vg_rsa_oaep_<H>_mgf1_<G>_encrypt(out: *mut u8, out_len: usize,
n: *const u8, n_len: usize, e: *const u8, e_len: usize, label: *const u8,
label_len: usize, msg: *const u8, msg_len: usize, seed: *const [u8; hLen],
scratch: *mut u64, scratch_len: usize) -> u32`. -/
def encryptSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("n", .slice false .u8 "n_len"),
    ("e", .slice false .u8 "e_len"), ("label", .slice false .u8 "label_len"),
    ("msg", .slice false .u8 "msg_len"), ("seed", .array false .u8 H.len),
    ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- `RSAES-OAEP-ENCRYPT` of the message with the label and the seed, with the
public key `(n, e)` (`encrypt`). Constant time but for the public key and
the lengths. -/
def encryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (encryptSig H).contract A
    (pre := fun _out outLen _n nLen _e eLen _label _labelLen _msg _msgLen _seed _scratch
        scratchLen _ =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ 1 ≤ eLen.toNat ∧
        eLen.toNat ≤ nLen.toNat ∧ scratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun out _outLen n nLen e eLen label labelLen msg msgLen seed _scratch _scratchLen
        m m' r =>
      written m' out nLen.toNat r
        (encrypt H G (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat)
          (bytesAt m label labelLen.toNat) (bytesAt m msg msgLen.toNat) (bytesAt m seed H.len)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen n nLen e eLen _label _labelLen _msg _msgLen _seed _scratch
        _scratchLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat))

/-- `vg_rsa_oaep_<H>_mgf1_<G>_encrypt` on every target. -/
def encryptApi : Api where
  module := s!"rsa_oaep_{H.rust}_mgf1_{G.rust}"
  name := s!"vg_rsa_oaep_{H.rust}_mgf1_{G.rust}_encrypt"
  sig := encryptSig H
  writeArgs := true
  contracts := some fun A stack => encryptContract H G A stack
  summary := s!"RSAES-OAEP encryption (RFC 8017 §7.1.1) with {H.name} and MGF1 with {G.name}. \
    With the modulus `n` (`n_len` bytes, most significant first, odd, from 512 to 8192 bits, \
    its first byte not zero) and the public exponent `e` (`e_len` bytes, most significant \
    first), writes the encryption of the message `msg` with the label `label` and the \
    {H.len}-byte seed `*seed` (`n_len` bytes, most significant first) to `out` and returns 1; \
    or writes zeros and returns 0 if `n` is not such a modulus or the message is longer than \
    `n_len - {2 * H.len + 2}` bytes. The seed must be fresh random bytes for each encryption.\n\n\
    Contract: `VG.Spec.RsaOaep.encryptContract` of `VG.Spec.Mgf1.{H.lean}` and \
    `VG.Spec.Mgf1.{G.lean}`. Constant time but for the public key: timing may depend on the \
    pointers, the lengths and the contents of `n` and `e`, not on the message, the label or \
    the seed."
  safety := ["`n_len` must be in 64..=1024.", "`out_len` must be `n_len`.",
    "`e_len` must be in 1..=`n_len`."] ++ scratchSafety

end VG.Spec.RsaOaep
