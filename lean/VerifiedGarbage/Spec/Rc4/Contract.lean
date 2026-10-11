module

public import VerifiedGarbage.Spec.Rc4
public import VerifiedGarbage.TCB.Artifact

/-!
# RC4: contracts on every target

**Trusted.** `Sig.contract` derives validity, non-overlap, permitted writes
and public pointers/lengths. Key bytes, the table, `j` and data are secret.
Only `i` may leak on update: it is the total public byte count modulo 256
after initialization. This lets an implementation continue a public scan
of the table across updates without exposing a key-dependent index.

The context is `contextAt`'s 258 bytes. Each primitive keeps its working
space on its own stack and zeroes it before returning. `stack` accounts for
frames and calls, and `writeArgs` permits calls through stack-passed
arguments.
Initialization returns 0 on success or 1 on invalid key length, when the
context is unspecified. Update accepts any byte-valued context, including
zero-length input, and applies exactly `update`. Finalization needs no
primitive: the model emits no bytes and examines no secrets.
-/

@[expose] public section

namespace VG.Spec.Rc4

/-- `vg_rc4_init(key: *const u8, key_len: usize, ctx: *mut [u8; 258]) -> u32`. -/
def initSig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("ctx", .array true .u8 258)]
  ret := some .u32

/-- If `init` of the `key_len` bytes at `key` succeeds, returns 0 having
written its context to `ctx` (`contextAt`); otherwise returns 1. -/
def initPost (pb : Nat) : initSig.Post pb := fun key keyLen ctx m m' r =>
  match init (bytesAt m key keyLen.toNat) with
  | .ok c => r = 0 ∧ contextAt m' ctx = c
  | .error .invalidKeyLength => r = 1

/-- `initPost`. -/
def initContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initSig.contract A (post := initPost A.ptrBits) (writeArgs := true) (stack := stack)

def initApi : Api where
  module := "rc4"
  name := "vg_rc4_init"
  sig := initSig
  writeArgs := true
  contracts := some fun A stack => initContract A stack
  summary := "Starts raw RC4 (ARCFOUR draft §§3.1–3.2): for `key_len` in 1..=256, \
    schedules the bytes at `key`, writes the permutation and two zero PRGA indices \
    to `*ctx` (`VG.Spec.Rc4.contextAt`), and returns 0. Otherwise returns 1. \
    No initial stream bytes are discarded.\n\n\
    Contract: `VG.Spec.Rc4.initContract`. Constant time: only pointers and \
    `key_len` may affect timing, not the key or key-dependent table indices."
  safety := ["On failure, the contents of `ctx` on return are unspecified."]

/-- `vg_rc4_apply(ctx: *mut [u8; 258], data: *mut u8, len: usize)`. -/
def applySig : Sig where
  params := [("ctx", .array true .u8 258), ("data", .slice true .u8 "len")]

/-- `update` of the context at `ctx` (`contextAt`) and the `len` bytes at
`data` leaves its next context at `ctx` and its output at `data`. -/
def applyPost (pb : Nat) : applySig.Post pb := fun ctx data len m m' _ =>
  let result := update (contextAt m ctx) (bytesAt m data len.toNat)
  contextAt m' ctx = result.1 ∧ bytesAt m' data len.toNat = result.2

/-- The context's PRGA index `i`, which `vg_rc4_apply` may leak. -/
def applyLeak (pb : Nat) : Curry (applySig.words pb) (Mem → List Nat) :=
  fun ctx _data _len m => [(contextAt m ctx).i.toNat]

/-- `applyPost`, leaking `applyLeak`. -/
def applyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  applySig.contract A (post := applyPost A.ptrBits) (writeArgs := true) (stack := stack)
    (leak := some (applyLeak A.ptrBits))

def applyApi : Api where
  module := "rc4"
  name := "vg_rc4_apply"
  sig := applySig
  writeArgs := true
  contracts := some fun A stack => applyContract A stack
  summary := "Continues raw RC4 encryption or decryption: XORs the next `len` stream \
    bytes into `data` in place and preserves the next stream position in `*ctx` \
    (`VG.Spec.Rc4.contextAt`). Empty input leaves the context unchanged. There is \
    no nonce, padding, authentication, automatic discard or final output.\n\n\
    Contract: `VG.Spec.Rc4.applyContract`. Constant time: only pointers, `len` and \
    the initial PRGA index `i` (the public byte count modulo 256 for an initialized \
    context) may affect timing. Key bytes, the permutation, `j`, keystream \
    lookup indices and data remain secret. The function may leak `i`."
  safety := []

end VG.Spec.Rc4
