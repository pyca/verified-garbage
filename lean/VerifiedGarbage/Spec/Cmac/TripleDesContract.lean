module

public import VerifiedGarbage.Spec.Cmac
public import VerifiedGarbage.TCB.Artifact

/-!
# TDEA-CMAC (3DES-CMAC): the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of streaming
TDEA-CMAC, in terms of `Spec/Cmac.lean` with 8-byte blocks, for any target:
`A` is the target's calling convention. The signatures fix where the
arguments are, the memory each function may access, disjointness, and that
the pointers and the lengths are public (see `TCB/Sig.lean`). The key
schedule, the subkeys, the chaining value and the message are secret.

The key schedule is `TripleDes.expandKey`'s: 384 bytes, the three DES
schedules in 48 little-endian 64-bit slots (`TripleDes.scheduleAt`), as
`vg_triple_des_expand_key` (`VG.Spec.TripleDes.expandKeyContract`) also
writes it; TDEA-CMAC computes its own, so it needs no other primitive.

Streaming TDEA-CMAC keeps its state in a buffer of its own (`tdesRepr`,
below), which the caller holds as opaque words, as streaming AES-CMAC does
(`Repr`, in `Spec/Cmac.lean`). Its functions are named as AES's, but for
the one that starts a computation, `stream_init`:

* `vg_cmac_triple_des_stream_init` expands a key of 16 or 24 bytes into the
  state (the key schedule and the subkeys) and makes it represent the empty
  message (§6.2 steps 1 and 5).
* `vg_cmac_triple_des_absorb` absorbs bytes of any length, chaining every
  block but the last bytes `Mₙ*`, which it holds back in the state (steps 3
  and 6).
* `vg_cmac_triple_des_finish` writes the MAC of the message the state
  represents (steps 4 and 6, with `Tlen = 64`).

The length of the message so far (`count`) is public, as the lengths of its
pieces are, so the number of bytes held back (a function of it) is too. The
key, the state and the message are secret. `absorb` and `finish` take
`count` from the caller, as the hashes' `update` and `finalize` take
`count`: the state does not store it, since what it stores is secret. Every
message is shorter than 2⁶⁴ bytes, so that `count` (a `u64`) is its exact
length: with a length modulo 2⁶⁴, a message of 2⁶⁴ bytes, whose last block
is held back, would look like the empty one.

The caller truncates the MAC and compares MACs (§6.3).

Each takes the number of bytes of stack below the stack pointer that an
implementation's calls and frames use (`stack`, see `Sig.contract`), where
it keeps its working space.
-/

@[expose] public section

namespace VG.Spec.Cmac

/-! ## Streaming TDEA-CMAC

The streaming functions MAC a message given in pieces of any length. §6.2
cannot process a block until it knows whether it is the last (step 4 masks
the last block `Mₙ` with `K1` or `K2`), so the state holds back the
message's last bytes `Mₙ*`, between 1 and 8 of them (none for the empty
message), even a whole block, and chains the blocks before them
(`chainedLen 8`).

The state is 416 bytes (`[u64; 52]`):

* bytes 0–383: the TDEA key schedule, `TripleDes.expandKey` in
  `TripleDes.scheduleAt`'s layout, as `vg_cmac_triple_des_init` writes it;
* bytes 384–399: the subkeys `K1 ‖ K2` (§6.1);
* bytes 400–407: the chaining value `Cᵢ` (§6.2 step 6) of the blocks
  chained so far, from `C₀ = 0⁶⁴` (step 5);
* bytes 408–415: the bytes held back, of which the first
  `msg.length - chainedLen 8 msg.length` are specified.

Bytes 0–399 are laid out as `vg_cmac_triple_des_finalize`'s `key` reads
them. -/

/-- The streaming state at `p` represents the message `msg` under the TDEA
key `key`: the key is 16 or 24 bytes, and the state holds its key schedule,
its subkeys, the chaining value of the first `chainedLen 8 msg.length` bytes
of `msg` from the zero block, and the rest of `msg` (see above). The rest of
the state is unspecified. -/
def tdesRepr (mem : Mem) (p : Addr) (key msg : List Byte) : Prop :=
  let ks := subkeys (tdes key) 8
  let c := chainedLen 8 msg.length
  TripleDes.validKey key.length ∧
    TripleDes.scheduleAt mem p = TripleDes.expandKey key ∧
    Aes.bytesAt mem (p + 384) 16 = ks.1 ++ ks.2 ∧
    Aes.bytesAt mem (p + 400) 8 = chain (tdes key) (zeros 8) (blocks 8 (msg.take c)) ∧
    Aes.bytesAt mem (p + 408) (msg.length - c) = msg.drop c

/-- `vg_cmac_triple_des_stream_init(state: *mut [u64; 52], key: *const u8, key_len: usize)`. -/
def tdesStreamInitSig : Sig where
  params := [("state", .array true .u64 52), ("key", .slice false .u8 "key_len")]

/-- `stream_init`'s precondition: a 16- or 24-byte key. -/
def tdesStreamInitPre (pb : Nat) : Curry (tdesStreamInitSig.words pb) (Mem → Prop) :=
  fun _state _key keyLen _ => TripleDes.validKey keyLen.toNat

/-- Makes the state at `state` represent the empty message under the key at
`key`. -/
def tdesStreamInitPost (pb : Nat) : tdesStreamInitSig.Post pb := fun state key keyLen m m' _ =>
  tdesRepr m' state (TripleDes.bytesAt m key keyLen.toNat) []

/-- For a 16- or 24-byte TDEA key at `key`: `tdesStreamInitPost`. The key is
secret. -/
def tdesStreamInitContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  tdesStreamInitSig.contract A (pre := tdesStreamInitPre A.ptrBits)
    (post := tdesStreamInitPost A.ptrBits) (stack := stack)

/-- `vg_cmac_triple_des_stream_init` on every target. -/
def tdesStreamInitApi : Api where
  module := "cmac_triple_des"
  name := "vg_cmac_triple_des_stream_init"
  sig := tdesStreamInitSig
  contracts := some fun A stack => tdesStreamInitContract A stack
  summary := "Starts a TDEA-CMAC computation (NIST SP 800-38B): makes the streaming state \
    `*state` represent the empty message under the 16- or 24-byte TDEA key at `key` (FIPS \
    46-3; a 16-byte key is `K1 ‖ K2` with `K3 = K1`, parity bits are ignored). The state holds \
    the key schedule (the three DES schedules), the subkeys `K1 ‖ K2` (§6.1), the chaining \
    value and the message's last bytes, held back (`VG.Spec.Cmac.tdesRepr`). Continue with \
    `vg_cmac_triple_des_absorb` and `vg_cmac_triple_des_finish`.\n\n\
    Contract: `VG.Spec.Cmac.tdesStreamInitContract`. Constant time: only the pointers and \
    `key_len` may affect timing, not the key."
  safety := ["`key_len` must be 16 or 24."]

/-- `vg_cmac_triple_des_absorb(state: *mut [u64; 52], count: u64, data: *const u8, len: usize)`.
`count` is public. -/
def tdesAbsorbSig : Sig where
  params := [("state", .array true .u64 52), ("count", .int .u64 true),
    ("data", .slice false .u8 "len")]

/-- If the state at `state` represents a message `msg` of `count` bytes under
a key, and `msg` followed by the `len` bytes at `data` is shorter than 2⁶⁴
bytes, then afterwards it represents `msg` followed by those bytes, under the
same key. -/
def tdesAbsorbPost (pb : Nat) : tdesAbsorbSig.Post pb := fun state count data len m m' _ =>
  ∀ key msg, tdesRepr m state key msg →
    count = BitVec.ofNat 64 msg.length → msg.length + len.toNat < 2 ^ 64 →
    tdesRepr m' state key (msg ++ Aes.bytesAt m data len.toNat)

/-- `tdesAbsorbPost`. The state and the data are secret. -/
def tdesAbsorbContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  tdesAbsorbSig.contract A (post := tdesAbsorbPost A.ptrBits) (stack := stack)

/-- `vg_cmac_triple_des_absorb` on every target. -/
def tdesAbsorbApi : Api where
  module := "cmac_triple_des"
  name := "vg_cmac_triple_des_absorb"
  sig := tdesAbsorbSig
  contracts := some fun A stack => tdesAbsorbContract A stack
  summary := "Absorbs data into a TDEA-CMAC computation (NIST SP 800-38B §6.2): if the streaming \
    state `*state` represents a message of `count` bytes under a TDEA key (as \
    `vg_cmac_triple_des_stream_init` set it up), it then represents that message followed by \
    the `len` bytes at `data`, under the same key, provided that the two together are shorter \
    than 2⁶⁴ bytes. It chains (step 6) every block of the message but its last bytes `Mₙ*` \
    (step 3), which it holds back in the state, since only `vg_cmac_triple_des_finish` knows \
    they are the last.\n\n\
    Contract: `VG.Spec.Cmac.tdesAbsorbContract`. Constant time: only the pointers, `count` and \
    `len` may affect timing, not the state or the data."
  safety := []

/-- `vg_cmac_triple_des_finish(state: *mut [u64; 52], count: u64, out: *mut [u8; 8])`.
`count` is public; `state` is left unspecified. -/
def tdesFinishSig : Sig where
  params := [("state", .array true .u64 52), ("count", .int .u64 true),
    ("out", .array true .u8 8)]

/-- If the state at `state` represents a message `msg` of `count` bytes,
shorter than 2⁶⁴ bytes, under a key `key`, writes the TDEA-CMAC of `msg`
under `key` (§6.2, with `Tlen = 64`) to `out`. -/
def tdesFinishPost (pb : Nat) : tdesFinishSig.Post pb := fun state count out m m' _ =>
  ∀ key msg, tdesRepr m state key msg →
    count = BitVec.ofNat 64 msg.length → msg.length < 2 ^ 64 →
    Aes.bytesAt m' out 8 = tdesCmac key 8 msg

/-- `tdesFinishPost`. The state is secret. -/
def tdesFinishContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  tdesFinishSig.contract A (post := tdesFinishPost A.ptrBits) (stack := stack)

/-- `vg_cmac_triple_des_finish` on every target. -/
def tdesFinishApi : Api where
  module := "cmac_triple_des"
  name := "vg_cmac_triple_des_finish"
  sig := tdesFinishSig
  contracts := some fun A stack => tdesFinishContract A stack
  summary := "Finishes a TDEA-CMAC computation (NIST SP 800-38B §6.2, with `Tlen = 64`): if the \
    streaming state `*state` represents a message of `count` bytes, shorter than 2⁶⁴ bytes, \
    under a TDEA key (as `vg_cmac_triple_des_stream_init` and `vg_cmac_triple_des_absorb` set \
    it up), writes the MAC of that message under that key to `*out`: \
    `Cₙ = CIPH_K(Cₙ₋₁ ⊕ Mₙ)`, where `Mₙ = K1 ⊕ Mₙ*` if the message's last bytes `Mₙ*` are a \
    complete block, and `Mₙ = K2 ⊕ (Mₙ* ‖ 10ʲ)` otherwise (step 4). The caller truncates it \
    (step 7) and compares it (§6.3).\n\n\
    Contract: `VG.Spec.Cmac.tdesFinishContract`. Constant time: only the pointers and `count` \
    may affect timing, not the state."
  safety := ["The contents of `state` on return are unspecified."]

end VG.Spec.Cmac
