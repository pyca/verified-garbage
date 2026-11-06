module

public import VerifiedGarbage.Spec.Poly1305
public import VerifiedGarbage.TCB.Artifact

/-!
# Poly1305: the streaming contracts, with the length in the state

**Trusted** (as every file in `Spec/`). The contracts of streaming Poly1305
on a state that stores the length of the message so far (`Stream`), so
that the caller passes no length back, for any target: `A` is the target's
calling convention. They are those of `Spec/Poly1305/Contract.lean`'s
`initApi`, `updateApi` and `finalizeApi`, on the state `Buffered` followed by
the length, and without the `count` argument, and their Rust names are the
same: their registrations replace those functions'.

The state is 136 bytes (`[u64; 17]`): the 128 bytes of `Buffered` (the
accumulator, the key, the message's last bytes that do not fill a block,
and working space), then the length of the message in bytes, modulo 2⁶⁴,
a little-endian number (`storedLen`). The key, the accumulator and the
message are secret. The stored length is the length of the message so far,
public as the lengths of its pieces are: `update` and `finalize` may leak it
(`Sig.contract`'s `leak`), and nothing else secret.

Each contract takes the number of bytes of stack below the stack pointer
that an implementation's calls and frames use (`stack`, see
`Sig.contract`), 0 for one that uses none.
-/

@[expose] public section

namespace VG.Spec.Poly1305

/-- The length stored in the 136-byte state at `p`: bytes 128–135, a
little-endian number. -/
def storedLen (mem : Mem) (p : Addr) : Nat := leNum (bytesAt mem (p + 128) 8)

/-- The 136-byte state at `p` represents the message `msg` under the
one-time key `key`, with its length: its first 128 bytes as in `Buffered`,
and the length of `msg` in bytes, modulo 2⁶⁴, at bytes 128–135
(`storedLen`). -/
def Stream (mem : Mem) (p : Addr) (key msg : List Byte) : Prop :=
  Buffered mem p key msg ∧ storedLen mem p = msg.length % 2 ^ 64

/-- `vg_poly1305_init(state: *mut [u64; 17], key: *const [u8; 32])`. -/
def streamInitSig : Sig where
  params := [("state", .array true .u64 17), ("key", .array false .u8 32)]

/-- Makes the state at `state` represent the empty message, of length 0,
under the 32-byte one-time key at `key`. -/
def streamInitContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamInitSig.contract A
    (post := fun state key m m' _ => Stream m' state (bytesAt m key 32) []) (stack := stack)

/-- `vg_poly1305_init` on every target, on the state `Stream`. -/
def streamInitApi : Api where
  module := "poly1305"
  name := "vg_poly1305_init"
  sig := streamInitSig
  contracts := some fun A stack => streamInitContract A stack
  summary := "Starts a Poly1305 computation (RFC 8439 §2.5): makes the streaming state `*state` \
    represent the empty message under the 32-byte one-time key `*key`.\n\n\
    Contract: `VG.Spec.Poly1305.streamInitContract`. The streaming state is the accumulator, the \
    key, the message's last bytes that do not fill a block and the length of the message \
    (`VG.Spec.Poly1305.Stream`). Constant time: only the pointers may affect timing, not the key."
  safety := []

/-- `vg_poly1305_update(state: *mut [u64; 17], data: *const u8, len: usize)`. -/
def streamUpdateSig : Sig where
  params := [("state", .array true .u64 17), ("data", .slice false .u8 "len")]

/-- If the state at `state` represents a message `msg` under a key, with its
length, then afterwards it represents `msg` followed by the `len` bytes at
`data`, under the same key, with its length. -/
def streamUpdatePost (pb : Nat) : streamUpdateSig.Post pb := fun state data len m m' _ =>
  ∀ key msg, Stream m state key msg → Stream m' state key (msg ++ bytesAt m data len.toNat)

/-- What `vg_poly1305_update` may leak: the length stored in the state. -/
def streamUpdateLeak (pb : Nat) : Curry (streamUpdateSig.words pb) (Mem → List Nat) :=
  fun state _data _len m => [storedLen m state]

/-- `streamUpdatePost`, leaking at most the stored length. -/
def streamUpdateContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamUpdateSig.contract A (post := streamUpdatePost A.ptrBits) (stack := stack)
    (leak := some (streamUpdateLeak A.ptrBits))

/-- `vg_poly1305_update` on every target, on the state `Stream`. -/
def streamUpdateApi : Api where
  module := "poly1305"
  name := "vg_poly1305_update"
  sig := streamUpdateSig
  contracts := some fun A stack => streamUpdateContract A stack
  summary := "Absorbs data into a Poly1305 computation: if the streaming state `*state` represents \
    a message under a key, it then represents that message followed by the `len` bytes at `data`, \
    under the same key. The state stores the length of the message (modulo 2⁶⁴), which this \
    updates.\n\n\
    Contract: `VG.Spec.Poly1305.streamUpdateContract`. The streaming state is the accumulator, \
    the key, the message's last bytes that do not fill a block and the length of the message \
    (`VG.Spec.Poly1305.Stream`). Constant time: only the pointers, `len` and the length stored in \
    the state may affect timing, not the rest of the state or the data."
  safety := []

/-- `vg_poly1305_finalize(state: *mut [u64; 17], out: *mut [u8; 16])`.
`state` is left unspecified. -/
def streamFinalizeSig : Sig where
  params := [("state", .array true .u64 17), ("out", .array true .u8 16)]

/-- If the state at `state` represents a message `msg` under a key, with its
length, writes the Poly1305 tag of `msg` under that key to `out`. -/
def streamFinalizePost (pb : Nat) : streamFinalizeSig.Post pb := fun state out m m' _ =>
  ∀ key msg, Stream m state key msg → bytesAt m' out 16 = mac key msg

/-- What `vg_poly1305_finalize` may leak: the length stored in the state. -/
def streamFinalizeLeak (pb : Nat) : Curry (streamFinalizeSig.words pb) (Mem → List Nat) :=
  fun state _out m => [storedLen m state]

/-- `streamFinalizePost`, leaking at most the stored length. -/
def streamFinalizeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamFinalizeSig.contract A (post := streamFinalizePost A.ptrBits) (stack := stack)
    (leak := some (streamFinalizeLeak A.ptrBits))

/-- `vg_poly1305_finalize` on every target, on the state `Stream`. -/
def streamFinalizeApi : Api where
  module := "poly1305"
  name := "vg_poly1305_finalize"
  sig := streamFinalizeSig
  contracts := some fun A stack => streamFinalizeContract A stack
  summary := "Finishes a Poly1305 computation: if the streaming state `*state` represents a \
    message under a key, writes the tag of that message, under that key, to `*out`.\n\n\
    Contract: `VG.Spec.Poly1305.streamFinalizeContract`. Constant time: only the pointers and the \
    length stored in the state may affect timing, not the rest of the state."
  safety := ["The contents of `state` on return are unspecified."]

