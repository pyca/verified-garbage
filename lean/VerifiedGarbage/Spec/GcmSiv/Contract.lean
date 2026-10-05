import VerifiedGarbage.Spec.GcmSiv
import VerifiedGarbage.TCB.Artifact

/-!
# AES-GCM-SIV: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of one-shot
AES-GCM-SIV encryption and decryption, in terms of `Spec/GcmSiv.lean`, for
any target: `A` is the target's calling convention. The signatures fix
where the arguments are, the memory each function may access,
disjointness, and that the pointers, the lengths and the number of rounds
are public (see `TCB/Sig.lean`); the contracts add the rest. Everything else
(key schedules, nonces, additional data, texts and tags) is secret.

AES-GCM-SIV derives its keys from the key-generating key per nonce (RFC 8452
§4), so all a caller keeps of a key is the key schedule of the
key-generating key, as `vg_aes_expand_key` writes it
(`VG.Spec.Aes.expandKeyContract`), with its number of rounds: 10 for a
16-byte key, 14 for a 32-byte key. The functions compute with the cipher of
the schedule they are given, for the number of rounds they are given
(`ctxCiph`, `keyLen`): with the schedule of a key, that is AES-GCM-SIV with
that key (`encryptWith_ctx`, `decryptWith_ctx`).

* `vg_aes_gcm_siv_seal` is encryption (`encryptWith`): it encrypts the data
  in place and writes the 16-byte tag.
* `vg_aes_gcm_siv_open` is decryption (`decryptWith`): given the encrypted
  plaintext in place and the tag, it decrypts, and if the tag is wrong
  overwrites the data with zeros, so that the unauthenticated plaintext is
  never released (§5). Whether the tag is right is public: `open` may leak
  it (it is the result), and nothing else secret.

The functions check no length (which are public): the caller checks the
lengths of §6 (`supported`: at most 2³⁶ bytes of plaintext and of
additional data). The nonce is 12 bytes (§6), the tag 16: `seal` writes the
tag to the 16 bytes at `tag`, and `open` reads the received tag from the 16
bytes at `tag`. The functions keep their working space on the stack. The
postconditions (and `open`'s leak) are stated for `rounds` of 10 or 14,
which the preconditions require, so that they read only the buffers (the
key schedule's round keys for those rounds).

Every contract takes the number of bytes of stack below the stack pointer
that an implementation's calls and frames use (`stack`, see `Sig.contract`),
0 for one that uses none; the functions may overwrite their arguments passed
in memory, where the calling convention allows it (`writeArgs`), to pass
arguments to the functions they call.
-/

namespace VG.Spec.GcmSiv

/-- `vg_aes_gcm_siv_seal(schedule: *const [u8; 240], rounds: usize, nonce: *const [u8; 12], aad: *const u8, aad_len: usize, data: *mut u8, len: usize, tag: *mut [u8; 16])`.
`rounds` is public. -/
def sealSig : Sig where
  params := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
    ("nonce", .array false .u8 12), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("tag", .array true .u8 16)]

/-- `vg_aes_gcm_siv_seal`'s precondition: `rounds` is 10 or 14. -/
def sealPre (pb : Nat) : Curry (sealSig.words pb) (Mem → Prop) :=
  fun _schedule rounds _nonce _aad _aadLen _data _len _tag _ =>
    rounds.toNat = 10 ∨ rounds.toNat = 14

/-- For `rounds` of 10 or 14, with the key schedule of the key-generating key
in the first `16 (rounds + 1)` bytes at `schedule`: the `len` bytes at
`data` are encrypted, with the 12-byte nonce at `nonce` and the `aad_len`
bytes of additional data at `aad` (`encryptWith`), and the 16-byte tag is
at `tag`. -/
def sealPost (pb : Nat) : sealSig.Post pb :=
  fun schedule rounds nonce aad aadLen data len tag m m' _ =>
    (rounds.toNat = 10 ∨ rounds.toNat = 14) →
    encryptWith (ctxCiph m schedule rounds.toNat) (keyLen rounds.toNat) (Aes.bytesAt m nonce 12)
        (Aes.bytesAt m data len.toNat) (Aes.bytesAt m aad aadLen.toNat) =
      (Aes.bytesAt m' data len.toNat, Aes.bytesAt m' tag 16)

/-- For `rounds` of 10 or 14, with the key schedule of the key-generating key
in the first `16 (rounds + 1)` bytes at `schedule`: encrypts the `len` bytes
at `data` in place, with the 12-byte nonce at `nonce` and the `aad_len`
bytes of additional data at `aad` (`encryptWith`), and writes the 16-byte
tag to `tag`. -/
def sealContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealSig.contract A (pre := sealPre A.ptrBits) (post := sealPost A.ptrBits)
    (writeArgs := true)
    (stack := stack)

/-- `vg_aes_gcm_siv_seal` on every target. -/
def sealApi : Api where
  module := "aes_gcm_siv"
  name := "vg_aes_gcm_siv_seal"
  sig := sealSig
  writeArgs := true
  contracts := some fun A stack => sealContract A stack
  summary := "AES-GCM-SIV authenticated encryption (RFC 8452 §4): with the key schedule of the \
    key-generating key in the first `16 * (rounds + 1)` bytes of `*schedule`, as \
    `vg_aes_expand_key` writes it (`rounds` is 10 for a 16-byte key, 14 for a 32-byte key), \
    encrypts the `len` bytes at `data` in place, under the 12-byte nonce `*nonce`, and writes \
    the 16-byte tag of the plaintext and the `aad_len` bytes of additional data at `aad` to \
    `*tag`. The RFC's ciphertext is the encrypted data followed by the tag.\n\n\
    The function checks no length. AES-GCM-SIV is defined for at most `2^36` bytes of data and \
    at most `2^36` bytes of additional data (§6), which the caller must ensure.\n\n\
    Contract: `VG.Spec.GcmSiv.sealContract`. Constant time: only the pointers, `rounds` and the \
    lengths may affect timing, not the key schedule, the nonce, the additional data or the data."
  safety := ["`rounds` must be 10 or 14."]

/-- `vg_aes_gcm_siv_open(schedule: *const [u8; 240], rounds: usize, nonce: *const [u8; 12], aad: *const u8, aad_len: usize, data: *mut u8, len: usize, tag: *const [u8; 16]) -> u32`.
`rounds` is public. -/
def openSig : Sig where
  params := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
    ("nonce", .array false .u8 12), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("tag", .array false .u8 16)]
  ret := some .u32

/-- `vg_aes_gcm_siv_open`'s precondition: `vg_aes_gcm_siv_seal`'s. -/
def openPre (pb : Nat) : Curry (openSig.words pb) (Mem → Prop) :=
  fun _schedule rounds _nonce _aad _aadLen _data _len _tag _ =>
    rounds.toNat = 10 ∨ rounds.toNat = 14

/-- For `rounds` of 10 or 14, with the key schedule of the key-generating key
in the first `16 (rounds + 1)` bytes at `schedule` and the received tag the
16 bytes at `tag`: if the tag is right for the `len` bytes of encrypted
plaintext at `data`, the 12-byte nonce at `nonce` and the `aad_len` bytes of
additional data at `aad` (`decryptWith`), the result is 1 and the plaintext
is at `data`; otherwise the result is 0 and zeros are at `data`. -/
def openPost (pb : Nat) : openSig.Post pb :=
  fun schedule rounds nonce aad aadLen data len tag m m' r =>
    (rounds.toNat = 10 ∨ rounds.toNat = 14) →
    match decryptWith (ctxCiph m schedule rounds.toNat) (keyLen rounds.toNat)
        (Aes.bytesAt m nonce 12) (Aes.bytesAt m data len.toNat) (Aes.bytesAt m aad aadLen.toNat)
        (Aes.bytesAt m tag 16) with
    | some pt => r = 1 ∧ Aes.bytesAt m' data len.toNat = pt
    | none => r = 0 ∧ Aes.bytesAt m' data len.toNat = zeros len.toNat

/-- What `vg_aes_gcm_siv_open` may leak, for `rounds` of 10 or 14: whether it
returns 1 (`decryptWith`'s outcome). -/
def openLeak (pb : Nat) : Curry (openSig.words pb) (Mem → List Nat) :=
  fun schedule rounds nonce aad aadLen data len tag m =>
    if ¬(rounds.toNat = 10 ∨ rounds.toNat = 14) then [] else
    [if (decryptWith (ctxCiph m schedule rounds.toNat) (keyLen rounds.toNat)
        (Aes.bytesAt m nonce 12) (Aes.bytesAt m data len.toNat) (Aes.bytesAt m aad aadLen.toNat)
        (Aes.bytesAt m tag 16)).isSome
      then 1 else 0]

/-- For `rounds` of 10 or 14, with the key schedule of the key-generating key
in the first `16 (rounds + 1)` bytes at `schedule` and the received tag the
16 bytes at `tag`: if the tag is right for the `len` bytes of encrypted
plaintext at `data`, the 12-byte nonce at `nonce` and the `aad_len` bytes of
additional data at `aad` (`decryptWith`), returns 1 and leaves the plaintext
at `data`; otherwise returns 0 and leaves zeros at `data`. May leak which
(`decryptWith`'s outcome). -/
def openContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openSig.contract A (pre := openPre A.ptrBits) (post := openPost A.ptrBits)
    (writeArgs := true)
    (stack := stack)
    (leak := some (openLeak A.ptrBits))

/-- `vg_aes_gcm_siv_open` on every target. -/
def openApi : Api where
  module := "aes_gcm_siv"
  name := "vg_aes_gcm_siv_open"
  sig := openSig
  writeArgs := true
  contracts := some fun A stack => openContract A stack
  summary := "AES-GCM-SIV authenticated decryption (RFC 8452 §5): with the key schedule of the \
    key-generating key in the first `16 * (rounds + 1)` bytes of `*schedule`, as \
    `vg_aes_expand_key` writes it (`rounds` is 10 for a 16-byte key, 14 for a 32-byte key), and \
    the received 16-byte tag `*tag`, decrypts the `len` bytes of encrypted plaintext at `data` \
    in place, under the 12-byte nonce `*nonce`, and returns 1 if the tag is that of the \
    plaintext and the `aad_len` bytes of additional data at `aad`; otherwise returns 0 and \
    overwrites the `len` bytes at `data` with zeros. The tags are compared without a branch.\n\n\
    The function checks no length. AES-GCM-SIV is defined for at most `2^36` bytes of data and \
    at most `2^36` bytes of additional data (§6), which the caller must check.\n\n\
    Contract: `VG.Spec.GcmSiv.openContract`. Constant time but for the result: only the \
    pointers, `rounds`, the lengths and whether the function returns 1 or 0 may affect timing, \
    not the key schedule, the nonce, the additional data, the data or the tag."
  safety := ["`rounds` must be 10 or 14."]

end VG.Spec.GcmSiv
