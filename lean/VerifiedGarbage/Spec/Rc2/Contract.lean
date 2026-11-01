module

public import VerifiedGarbage.Spec.Rc2
public import VerifiedGarbage.TCB.Artifact

/-!
# RC2-CBC: contracts on every target

**Trusted.** The signatures derive memory validity, non-overlap, permitted
writes and public pointers/lengths from `Sig.contract`. Key bytes, expanded
key words, IV contents and data are secret. Effective key bits are a public
algorithm parameter, independent of the key's byte length.

`stack` describes an implementation's frames and calls.

## Streaming

`vg_rc2_cbc_init`, `vg_rc2_cbc_encrypt_update` and
`vg_rc2_cbc_decrypt_update` implement the streaming model of `Spec/Rc2.lean`
(`initWithEffectiveBits` and `update`) on a context in memory, `contextAt`:
the key schedule, the chaining value and the pending partial block, all
secret. The context's public parts are not stored in it: the caller keeps the
direction (choosing the update function by it) and the number of pending
bytes (`pending_len`, 0 after `init` and `(pending_len + len) % 8` after
each update), and passes the latter to every update. A context therefore
holds nothing an implementation may branch on, as constant time requires.

`init` checks the key length, the effective key bits and the IV length
itself, in `initWithEffectiveBits`'s order, and returns `Error.code` of the
first that fails, or 0: so the verified code decides every outcome of
initialization, although the lengths are public and the caller could check
them. `finalize` has no primitive: `finalize` of a context is
`.ok []` exactly if its pending input is empty, which, by `contextAt`, is
`pending_len = 0`, a public length the caller holds. Unpadded CBC emits
nothing at finalization, and nothing secret is involved.

`init` and the updates keep their working space on the stack, and zero it
before returning. They may overwrite their arguments passed in memory,
where the calling convention allows it (`writeArgs`), to pass arguments to
the functions they call.
-/

@[expose] public section

namespace VG.Spec.Rc2

/-! ## Streaming -/

/-- The streaming context at `p` (`[u8; 144]`), for the direction `direction`
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
    `vg_rc2_cbc_encrypt_update` or `vg_rc2_cbc_decrypt_update` from 0 pending bytes. \
    Effective bits are independent of the supplied key length.\n\n\
    Contract: `VG.Spec.Rc2.cbcInitContract`. Constant time: only the pointers, `key_len`, \
    `effective_bits` and `iv_len` may affect timing, not the key or the IV."
  safety := [
    "If the function returns nonzero, the contents of `ctx` on return are unspecified."]

/-- The update functions:
`(ctx: *mut [u8; 144], pending_len: usize, data: *const u8, len: usize,
out: *mut u8, out_len: usize)`. `pending_len` is public. `out` is a separate
buffer: the output is longer than `data` when pending bytes complete a block,
so it cannot be `data` in place, and like every writable buffer it overlaps
no other. -/
def cbcUpdateSig : Sig where
  params := [("ctx", .array true .u8 144), ("pending_len", .int .usize true),
    ("data", .slice false .u8 "len"), ("out", .slice true .u8 "out_len")]

/-- For `pending_len < 8` and `out_len = (pending_len + len) / 8 * 8`: if
`ctx` holds the context `c` with `pending_len` pending bytes
(`contextAt`), then `update c` of the `len` bytes at `data` writes its
output, the `out_len` bytes of all complete blocks, to `out`, and leaves at
`ctx` its next context, with `(pending_len + len) % 8` pending bytes. -/
def cbcUpdatePre (pb : Nat) : Curry (cbcUpdateSig.words pb) (Mem → Prop) :=
  fun _ctx pendingLen _data len _out outLen _ =>
    pendingLen.toNat < 8 ∧ outLen.toNat = (pendingLen.toNat + len.toNat) / 8 * 8

/-- The postcondition, which also states `pending_len < 8` (the
precondition's), so that it reads only the context's 144 bytes. -/
def cbcUpdatePost (direction : Direction) (pb : Nat) : cbcUpdateSig.Post pb :=
  fun ctx pendingLen data len out outLen m m' _ => pendingLen.toNat < 8 →
    let result := update (contextAt m ctx direction pendingLen.toNat) (bytesAt m data len.toNat)
    contextAt m' ctx direction ((pendingLen.toNat + len.toNat) % 8) = result.1 ∧
      bytesAt m' out outLen.toNat = result.2

/-- `cbcUpdatePre` and `cbcUpdatePost`. -/
def cbcUpdateContract {M : ISA} (A : Abi M) (direction : Direction) (stack : Nat := 0) :
    Contract M :=
  cbcUpdateSig.contract A (pre := cbcUpdatePre A.ptrBits) (post := cbcUpdatePost direction A.ptrBits)
    (writeArgs := true) (stack := stack)

def cbcEncryptUpdateContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcUpdateContract A .encrypt stack

def cbcDecryptUpdateContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcUpdateContract A .decrypt stack

/-- The `# Safety` items the update functions share. -/
def cbcUpdateSafety : List String := [
  "`pending_len` must be less than 8.",
  "`out_len` must be `(pending_len + len) / 8 * 8`."]

def cbcEncryptUpdateApi : Api where
  module := "rc2"
  name := "vg_rc2_cbc_encrypt_update"
  sig := cbcUpdateSig
  writeArgs := true
  contracts := some fun A stack => cbcEncryptUpdateContract A stack
  summary := "Continues RC2-CBC encryption without padding: if `*ctx` is a context with \
    `pending_len` pending bytes (`VG.Spec.Rc2.contextAt`, written by `vg_rc2_cbc_init` and \
    updated by this function), encrypts the complete 8-byte blocks of the pending bytes \
    followed by the `len` bytes at `data`, `C[i] = RC2(schedule, P[i] XOR C[i-1])` from the \
    context's chaining value, writes them to `out` (`out_len` bytes), and leaves in `*ctx` \
    the last ciphertext block as the chaining value and the remaining \
    `(pending_len + len) % 8` bytes as the pending input. The caller keeps the number of \
    pending bytes; when the input ends, it is an incomplete block unless it is 0.\n\n\
    Contract: `VG.Spec.Rc2.cbcEncryptUpdateContract`. Constant time: only the pointers, \
    `pending_len`, `len` and `out_len` may affect timing, not the context or the data."
  safety := cbcUpdateSafety

def cbcDecryptUpdateApi : Api where
  module := "rc2"
  name := "vg_rc2_cbc_decrypt_update"
  sig := cbcUpdateSig
  writeArgs := true
  contracts := some fun A stack => cbcDecryptUpdateContract A stack
  summary := "Continues RC2-CBC decryption without padding: if `*ctx` is a context with \
    `pending_len` pending bytes (`VG.Spec.Rc2.contextAt`, written by `vg_rc2_cbc_init` and \
    updated by this function), decrypts the complete 8-byte blocks of the pending bytes \
    followed by the `len` bytes at `data`, `P[i] = RC2_inverse(schedule, C[i]) XOR C[i-1]` \
    from the context's chaining value, writes them to `out` (`out_len` bytes), and leaves in \
    `*ctx` the last input ciphertext block as the chaining value and the remaining \
    `(pending_len + len) % 8` bytes as the pending input. The caller keeps the number of \
    pending bytes; when the input ends, it is an incomplete block unless it is 0.\n\n\
    Contract: `VG.Spec.Rc2.cbcDecryptUpdateContract`. Constant time: only the pointers, \
    `pending_len`, `len` and `out_len` may affect timing, not the context or the data."
  safety := cbcUpdateSafety

end VG.Spec.Rc2
