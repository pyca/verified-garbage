module

public import VerifiedGarbage.Spec.Cbc
public import VerifiedGarbage.Spec.Rc2
public import VerifiedGarbage.TCB.Artifact

/-!
# RC2-CBC: contracts on every target

**Trusted.** CBC is NIST SP 800-38A §6.2's, `Cbc.encrypt` and `Cbc.decrypt`
(`Spec/Cbc.lean`, defined for any block cipher), with RC2's encryption and
decryption (`Spec/Rc2.lean`) on 8-byte blocks (this does not assert that RC2
is a NIST-approved cipher).

Initialization (`initWithEffectiveBits`) follows issue #1's
`init(key, iv, direction)`, taking the effective bit count explicitly (issue
#1's default is eight times the key length). Unpadded CBC rejects a partial
block (`Error.incompleteBlock`) in either direction; padding is the caller's
responsibility.

The signatures derive memory validity, non-overlap, permitted
writes and public pointers/lengths from `Sig.contract`. Key bytes, expanded
key words, IV contents and data are secret. Effective key bits are a public
algorithm parameter, independent of the key's byte length.

`stack` describes an implementation's frames and calls.

## Initialization

`vg_rc2_cbc_init` implements `initWithEffectiveBits` on a context in memory,
`contextAt`: the key schedule, the chaining value and the pending partial
block, all secret, which the chained functions below continue from. The
context's public parts are not stored in it: the caller keeps the direction
and the number of pending bytes (0 after `init`). A context therefore holds
nothing an implementation may branch on, as constant time requires.

`init` checks the key length, the effective key bits and the IV length
itself, in `initWithEffectiveBits`'s order, and returns `Error.code` of the
first that fails, or 0: so the verified code decides every outcome of
initialization, although the lengths are public and the caller could check
them.

`init` keeps its working space on the stack, and zeroes it before
returning. It may overwrite its arguments passed in memory, where the
calling convention allows it (`writeArgs`), to pass arguments to the
function it calls.
-/

@[expose] public section

namespace VG.Spec.Rc2

/-! ## The model -/

/-- RC2 encryption as CBC's forward function `CIPH_K` (`Spec/Cbc.lean`), under
the schedule `k`, on blocks as lists of 8 bytes. -/
def cipher (k : Schedule) : Cbc.Cipher := fun b =>
  (encryptBlock k (Vector.ofFn fun i => b.getD i.val 0)).toList

/-- RC2 decryption as CBC's inverse function `CIPH⁻¹_K`, under the schedule
`k`, on blocks as lists of 8 bytes. -/
def invCipher (k : Schedule) : Cbc.Cipher := fun b =>
  (decryptBlock k (Vector.ofFn fun i => b.getD i.val 0)).toList

structure Context where
  schedule : Schedule
  direction : Direction
  iv : Block
  pending : List Byte := []

inductive Error | invalidKeyLength | invalidEffectiveBits | invalidIvLength | incompleteBlock
  deriving DecidableEq, Repr

/-- Initialize CBC with explicitly selected effective key bits (1–1024). -/
def initWithEffectiveBits (key iv : List Byte) (direction : Direction) (effectiveBits : Nat) :
    Except Error Context := do
  unless 1 ≤ key.length ∧ key.length ≤ 128 do throw .invalidKeyLength
  unless 1 ≤ effectiveBits ∧ effectiveBits ≤ 1024 do throw .invalidEffectiveBits
  unless iv.length = 8 do throw .invalidIvLength
  return {
    schedule := expandKey key effectiveBits
    direction := direction
    iv := Vector.ofFn fun i => iv.getD i 0 }

/-! ## The context in memory -/

/-- The context at `p` (`[u8; 144]`), for the direction `direction`
and `pendingLen` pending bytes, both of which the caller keeps: the key
schedule in bytes 0–127 (as `scheduleAt`), the chaining value in bytes
128–135, and the pending input in the first `pendingLen` bytes of bytes
136–143. The rest of bytes 136–143 is unspecified. -/
def contextAt (m : Mem) (p : Addr) (direction : Direction) (pendingLen : Nat) : Context where
  schedule := scheduleAt m p
  direction := direction
  iv := blockAt m (p + 128)
  pending := bytesAt m (p + 136) pendingLen

/-- The value `vg_rc2_cbc_init` returns for each error; it returns 0 on
success. -/
def Error.code : Error → Nat
  | .invalidKeyLength => 1
  | .invalidEffectiveBits => 2
  | .invalidIvLength => 3
  | .incompleteBlock => 4

/-- `vg_rc2_cbc_init(key: *const u8, key_len: usize, effective_bits: usize,
iv: *const u8, iv_len: usize, ctx: *mut [u8; 144]) -> u32`.
`effective_bits` is public. -/
def cbcInitSig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("effective_bits", .int .usize true),
    ("iv", .slice false .u8 "iv_len"), ("ctx", .array true .u8 144)]
  ret := some .u32

/-- For any lengths: if `initWithEffectiveBits` of the `key_len` bytes at
`key`, the `iv_len` bytes at `iv` and `effective_bits` succeeds, returns 0
having written its context to `ctx` (`contextAt`, with no pending bytes, for
either direction: the direction is not stored); otherwise returns the code of
its error, and the contents of `ctx` are unspecified. -/
def cbcInitPost (pb : Nat) : cbcInitSig.Post pb := fun key keyLen effectiveBits iv ivLen ctx m m' r =>
  ∀ direction, match initWithEffectiveBits (bytesAt m key keyLen.toNat)
      (bytesAt m iv ivLen.toNat) direction effectiveBits.toNat with
    | .ok c => r = 0 ∧ contextAt m' ctx direction 0 = c
    | .error e => r.toNat = e.code

/-- `cbcInitPost`. -/
def cbcInitContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcInitSig.contract A (post := cbcInitPost A.ptrBits) (writeArgs := true) (stack := stack)

def cbcInitApi : Api where
  module := "rc2"
  name := "vg_rc2_cbc_init"
  sig := cbcInitSig
  writeArgs := true
  contracts := some fun A stack => cbcInitContract A stack
  summary := "Starts RC2-CBC without padding (RFC 2268, NIST SP 800-38A §6.2), in either \
    direction: checks that `key_len` is in 1..=128, then that `effective_bits` is in \
    1..=1024, then that `iv_len` is 8, and returns 1, 2 or 3 respectively for the first \
    that is not (`VG.Spec.Rc2.Error.code`). Otherwise writes to `*ctx` the context with the key \
    schedule of the `key_len` bytes at `key` with `effective_bits` effective key bits \
    (`VG.Spec.Rc2.expandKey`), the `iv_len` bytes at `iv` as the chaining value, and no \
    pending input (`VG.Spec.Rc2.contextAt`), and returns 0. Continue with \
    `vg_rc2_cbc_encrypt_chained` or `vg_rc2_cbc_decrypt_chained` on the schedule at the \
    start of `*ctx` and the chaining value at `ctx + 128`. Effective bits are independent of the supplied key length.\n\n\
    Contract: `VG.Spec.Rc2.cbcInitContract`. Constant time: only the pointers, `key_len`, \
    `effective_bits` and `iv_len` may affect timing, not the key or the IV."
  safety := [
    "If the function returns nonzero, the contents of `ctx` on return are unspecified."]

/-! ## In-place CBC

The chained functions process whole blocks in place and replace `iv` with
`Cbc.next`, so subsequent calls continue the message. Empty input leaves
both buffers unchanged. Neither function buffers partial blocks or adds
or removes padding.

Both directions read the same 128-byte schedule (`scheduleAt`), as written
at the start of the context by `vg_rc2_cbc_init`, which chooses the effective
key size. The schedule, IV and data are separate buffers. Only pointers
and the block count are public; the schedule, IV and data remain secret.
-/
/-- The `n` 8-byte blocks at `p`, as lists of bytes. -/
def cbcBlocksAt (m : Mem) (p : Addr) (n : Nat) : List (List Byte) :=
  (blocksAt m p n).map Vector.toList

/-- `vg_rc2_cbc_encrypt_chained(schedule: *const [u8; 128], iv: *mut [u8; 8], data: *mut [u8; 8], n: usize)`,
and `vg_rc2_cbc_decrypt_chained` with the same signature. -/
def cbcChainedSig : Sig where
  params := [("schedule", .array false .u8 128), ("iv", .array true .u8 8),
    ("data", .slice true (.array .u8 8) "n")]

/-- Replaces the `n` blocks at `data` with their RC2-CBC encryption from
`iv`, under the schedule at `schedule`, and `iv` with the last ciphertext
block (unchanged if `n = 0`). -/
def cbcEncryptChainedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcChainedSig.contract A
    (post := fun schedule iv data n m m' _ =>
      let cs := Cbc.encrypt (cipher (scheduleAt m schedule)) (bytesAt m iv 8)
        (cbcBlocksAt m data n.toNat)
      cbcBlocksAt m' data n.toNat = cs ∧
        bytesAt m' iv 8 = Cbc.next (bytesAt m iv 8) cs)
    (writeArgs := true) (stack := stack)

/-- Replaces the `n` blocks at `data` with their RC2-CBC decryption from
`iv`, under the schedule at `schedule`, and `iv` with the last input
ciphertext block (unchanged if `n = 0`). -/
def cbcDecryptChainedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcChainedSig.contract A
    (post := fun schedule iv data n m m' _ =>
      let cs := cbcBlocksAt m data n.toNat
      cbcBlocksAt m' data n.toNat =
          Cbc.decrypt (invCipher (scheduleAt m schedule)) (bytesAt m iv 8) cs ∧
        bytesAt m' iv 8 = Cbc.next (bytesAt m iv 8) cs)
    (writeArgs := true) (stack := stack)

/-- `vg_rc2_cbc_encrypt_chained` on every target. -/
def cbcEncryptChainedApi : Api where
  module := "rc2_cbc"
  name := "vg_rc2_cbc_encrypt_chained"
  sig := cbcChainedSig
  writeArgs := true
  contracts := some fun A stack => cbcEncryptChainedContract A stack
  summary := "RC2-CBC encryption (RFC 2268 §§3–4, NIST SP 800-38A §6.2) of whole blocks, in place: \
    replaces the `n` 8-byte blocks `P₁ … Pₙ` at `data` with `Cⱼ = CIPH_K(Pⱼ ⊕ Cⱼ₋₁)`, where `C₀` \
    is the block at `*iv`, and `*iv` with `Cₙ` (leaving it unchanged if `n = 0`), so that a \
    further call continues the message. `CIPH_K` is RC2 encryption under the 128-byte \
    little-endian schedule at `schedule`, as written at the start of the context by \
    `vg_rc2_cbc_init`. No padding is added.\n\n\
    Contract: `VG.Spec.Rc2.cbcEncryptChainedContract`. Constant time: only the pointers and `n` \
    may affect timing, not the schedule, the chaining value or the data."
  safety := []

/-- `vg_rc2_cbc_decrypt_chained` on every target. -/
def cbcDecryptChainedApi : Api where
  module := "rc2_cbc"
  name := "vg_rc2_cbc_decrypt_chained"
  sig := cbcChainedSig
  writeArgs := true
  contracts := some fun A stack => cbcDecryptChainedContract A stack
  summary := "RC2-CBC decryption (RFC 2268 §§3–4, NIST SP 800-38A §6.2) of whole blocks, in place: \
    replaces the `n` 8-byte blocks `C₁ … Cₙ` at `data` with `Pⱼ = CIPH⁻¹_K(Cⱼ) ⊕ Cⱼ₋₁`, where `C₀` \
    is the block at `*iv`, and `*iv` with `Cₙ`, the last block at `data` on entry (leaving it \
    unchanged if `n = 0`), so that a further call continues the message. `CIPH⁻¹_K` is RC2 \
    decryption under the same 128-byte little-endian schedule as encryption, as written at \
    the start of the context by `vg_rc2_cbc_init`. No padding is removed.\n\n\
    Contract: `VG.Spec.Rc2.cbcDecryptChainedContract`. Constant time: only the pointers and `n` \
    may affect timing, not the schedule, the chaining value or the data."
  safety := []

end VG.Spec.Rc2
