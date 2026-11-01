module

public import VerifiedGarbage.Spec.Cmac
public import VerifiedGarbage.TCB.Artifact

/-!
# AES-CMAC: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of streaming
AES-CMAC, in terms of `Spec/Cmac.lean`, for any target: `A` is the target's
calling convention. The signatures fix where the arguments are, the memory
each function may access, disjointness, and that the pointers, the lengths
and the number of rounds are public (see `TCB/Sig.lean`). The key schedule,
the subkeys, the chaining value and the message are secret.

Streaming AES-CMAC keeps everything in a state of its own (`Repr`, in
`Spec/Cmac.lean`), which the caller holds as opaque words:

* `vg_cmac_aes_init` expands a key of 16, 24 or 32 bytes into the state
  (the key schedule and the subkeys) and makes it represent the empty
  message (§6.2 steps 1 and 5).
* `vg_cmac_aes_absorb` absorbs bytes of any length, chaining every block but
  the last bytes `Mₙ*`, which it holds back in the state (steps 3 and 6).
* `vg_cmac_aes_finish` writes the MAC of the message the state represents
  (steps 4 and 6, with `Tlen = 128`).

The key length is public, so the number of rounds is; the length of the
message so far (`count`) is public, as the lengths of its pieces are, so
the number of bytes held back (a function of it) is too. The key, the
state and the message are secret. `absorb` and `finish` take the number of
rounds (`key_len / 4 + 6` for the key `init` was given) and `count` from
the caller, as the hashes' `update` and `finalize` take `count`: the state
does not store them, since what it stores is secret. Every message is
shorter than 2⁶⁴ bytes, so that `count` (a `u64`) is its exact length: with
a length modulo 2⁶⁴, a message of 2⁶⁴ bytes, whose last block is held back,
would look like the empty one.

The caller truncates the MAC and compares MACs (§6.3).

Each takes the number of bytes of stack below the stack pointer that an
implementation's calls and frames use (`stack`, see `Sig.contract`), 0 for
one that uses none; the functions keep their working space there.
-/

@[expose] public section

namespace VG.Spec.Cmac

/-! ## Streaming AES-CMAC -/

/-- `vg_cmac_aes_init(state: *mut [u64; 38], key: *const u8, key_len: usize)`. -/
def aesInitSig : Sig where
  params := [("state", .array true .u64 38), ("key", .slice false .u8 "key_len")]

/-- `init`'s precondition: a key of 16, 24 or 32 bytes. -/
def aesInitPre (pb : Nat) : Curry (aesInitSig.words pb) (Mem → Prop) :=
  fun _state _key keyLen _ => keyLen.toNat = 16 ∨ keyLen.toNat = 24 ∨ keyLen.toNat = 32

/-- Makes the state at `state` represent the empty message under the key at
`key`. -/
def aesInitPost (pb : Nat) : aesInitSig.Post pb := fun state key keyLen m m' _ =>
  Repr m' state (Aes.bytesAt m key keyLen.toNat) []

/-- For a key of 16, 24 or 32 bytes at `key`: `aesInitPost`. The key is
secret. -/
def aesInitContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesInitSig.contract A (pre := aesInitPre A.ptrBits) (post := aesInitPost A.ptrBits)
    (stack := stack)

/-- `vg_cmac_aes_init` on every target. -/
def aesInitApi : Api where
  module := "cmac_aes"
  name := "vg_cmac_aes_init"
  sig := aesInitSig
  contracts := some fun A stack => aesInitContract A stack
  summary := "Starts an AES-CMAC computation (NIST SP 800-38B, RFC 4493): makes the streaming \
    state `*state` represent the empty message under the AES key of `key_len` bytes at `key` \
    (AES-128, AES-192 or AES-256). The state holds the key schedule of AES (FIPS 197) with \
    `key_len / 4 + 6` rounds, the subkeys `K1 ‖ K2` (§6.1), the chaining value and the \
    message's last bytes, held back (`VG.Spec.Cmac.Repr`). Continue with `vg_cmac_aes_absorb` \
    and `vg_cmac_aes_finish`, passing them `key_len / 4 + 6` as `rounds`.\n\n\
    Contract: `VG.Spec.Cmac.aesInitContract`. Constant time: only the pointers and `key_len` may \
    affect timing, not the key."
  safety := ["`key_len` must be 16, 24 or 32."]

/-- `vg_cmac_aes_absorb(state: *mut [u64; 38], rounds: usize, count: u64, data: *const u8, len: usize)`.
`rounds` and `count` are public. -/
def aesAbsorbSig : Sig where
  params := [("state", .array true .u64 38), ("rounds", .int .usize true),
    ("count", .int .u64 true), ("data", .slice false .u8 "len")]

/-- `absorb`'s precondition: `rounds` of 10, 12 or 14. -/
def aesAbsorbPre (pb : Nat) : Curry (aesAbsorbSig.words pb) (Mem → Prop) :=
  fun _state rounds _count _data _len _ =>
    rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14

/-- If the state at `state` represents a message `msg` of `count` bytes under
a key of `Nr = rounds` rounds, and `msg` followed by the `len` bytes at
`data` is shorter than 2⁶⁴ bytes, then afterwards it represents `msg`
followed by those bytes, under the same key. -/
def aesAbsorbPost (pb : Nat) : aesAbsorbSig.Post pb := fun state rounds count data len m m' _ =>
  ∀ key msg, Repr m state key msg → rounds.toNat = Aes.rounds (key.length / 4) →
    count = BitVec.ofNat 64 msg.length → msg.length + len.toNat < 2 ^ 64 →
    Repr m' state key (msg ++ Aes.bytesAt m data len.toNat)

/-- For `rounds` of 10, 12 or 14: `aesAbsorbPost`. The state and the data
are secret. -/
def aesAbsorbContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesAbsorbSig.contract A (pre := aesAbsorbPre A.ptrBits) (post := aesAbsorbPost A.ptrBits)
    (stack := stack)

/-- `vg_cmac_aes_absorb` on every target. -/
def aesAbsorbApi : Api where
  module := "cmac_aes"
  name := "vg_cmac_aes_absorb"
  sig := aesAbsorbSig
  contracts := some fun A stack => aesAbsorbContract A stack
  summary := "Absorbs data into an AES-CMAC computation (NIST SP 800-38B §6.2): if the streaming \
    state `*state` represents a message of `count` bytes under an AES key with `rounds` rounds \
    (as `vg_cmac_aes_init` set it up), it then represents that message followed by the `len` \
    bytes at `data`, under the same key, provided that the two together are shorter than 2⁶⁴ \
    bytes. It chains (step 6) every block of the message but its last bytes `Mₙ*` (step 3), \
    which it holds back in the state, since only `vg_cmac_aes_finish` knows they are the last.\n\n\
    Contract: `VG.Spec.Cmac.aesAbsorbContract`. Constant time: only the pointers, `rounds`, \
    `count` and `len` may affect timing, not the state or the data."
  safety := ["`rounds` must be 10, 12 or 14."]

/-- `vg_cmac_aes_finish(state: *mut [u64; 38], rounds: usize, count: u64, out: *mut [u8; 16])`.
`rounds` and `count` are public; `state` is left unspecified. -/
def aesFinishSig : Sig where
  params := [("state", .array true .u64 38), ("rounds", .int .usize true),
    ("count", .int .u64 true), ("out", .array true .u8 16)]

/-- `finish`'s precondition: `rounds` of 10, 12 or 14. -/
def aesFinishPre (pb : Nat) : Curry (aesFinishSig.words pb) (Mem → Prop) :=
  fun _state rounds _count _out _ =>
    rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14

/-- If the state at `state` represents a message `msg` of `count` bytes,
shorter than 2⁶⁴ bytes, under a key `key` of `Nr = rounds` rounds, writes
the AES-CMAC of `msg` under `key` (§6.2, with `Tlen = 128`) to `out`. -/
def aesFinishPost (pb : Nat) : aesFinishSig.Post pb := fun state rounds count out m m' _ =>
  ∀ key msg, Repr m state key msg → rounds.toNat = Aes.rounds (key.length / 4) →
    count = BitVec.ofNat 64 msg.length → msg.length < 2 ^ 64 →
    Aes.bytesAt m' out 16 = aesCmac key 16 msg

/-- For `rounds` of 10, 12 or 14: `aesFinishPost`. The state is secret. -/
def aesFinishContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesFinishSig.contract A (pre := aesFinishPre A.ptrBits) (post := aesFinishPost A.ptrBits)
    (stack := stack)

/-- `vg_cmac_aes_finish` on every target. -/
def aesFinishApi : Api where
  module := "cmac_aes"
  name := "vg_cmac_aes_finish"
  sig := aesFinishSig
  contracts := some fun A stack => aesFinishContract A stack
  summary := "Finishes an AES-CMAC computation (NIST SP 800-38B §6.2, with `Tlen = 128`): if the \
    streaming state `*state` represents a message of `count` bytes, shorter than 2⁶⁴ bytes, \
    under an AES key with `rounds` rounds (as `vg_cmac_aes_init` and `vg_cmac_aes_absorb` set \
    it up), writes the MAC of that message under that key to `*out`: `Cₙ = CIPH_K(Cₙ₋₁ ⊕ Mₙ)`, \
    where `Mₙ = K1 ⊕ Mₙ*` if the message's last bytes `Mₙ*` are a complete block, and \
    `Mₙ = K2 ⊕ (Mₙ* ‖ 10ʲ)` otherwise (step 4). The caller truncates it (step 7) and compares \
    it (§6.3).\n\n\
    Contract: `VG.Spec.Cmac.aesFinishContract`. Constant time: only the pointers, `rounds` and \
    `count` may affect timing, not the state."
  safety := [
    "`rounds` must be 10, 12 or 14.",
    "The contents of `state` on return are unspecified."]

end VG.Spec.Cmac
