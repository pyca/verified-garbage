import VerifiedGarbage.Spec.Cmac
import VerifiedGarbage.TCB.Artifact

/-!
# TDEA-CMAC (3DES-CMAC): the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of the three
primitives TDEA-CMAC is built from, in terms of `Spec/Cmac.lean` with
8-byte blocks, for any target: `A` is the target's calling convention. The
signatures fix where the arguments are, the memory each function may
access, disjointness, and that the pointers and the lengths are public (see
`TCB/Sig.lean`). The key schedule, the subkeys, the chaining value and the
message are secret.

The key schedule is `TripleDes.expandKey`'s: 384 bytes, the three DES
schedules in 48 little-endian 64-bit slots (`TripleDes.scheduleAt`), as
`vg_triple_des_expand_key` (`VG.Spec.TripleDes.expandKeyContract`) also
writes it; TDEA-CMAC computes its own, so it needs no other primitive.

* `vg_cmac_triple_des_init` expands the key, and writes its schedule
  followed by the subkeys `K1 ‖ K2` (§6.1): the 400-byte buffer that
  `vg_cmac_triple_des_finalize` takes.
* `vg_cmac_triple_des_update` continues §6.2 step 6
  (`Cᵢ = CIPH_K(Cᵢ₋₁ ⊕ Mᵢ)`) over whole blocks, from the chaining value
  `C` in `state`.
* `vg_cmac_triple_des_finalize` takes the key schedule and the subkeys
  together, as one 400-byte buffer (the 384-byte schedule, then
  `K1 ‖ K2`), and the message's last bytes `Mₙ*` (at most a block); if
  `state` holds the chaining value of the message's other blocks, it
  replaces it with the MAC of the whole message (§6.2, with `Tlen = 64`).

The Rust caller keeps the chaining value between calls, and holds back the
last block of what it has been given, even a complete one, since only
`finalize` knows whether a block is the last (§6.2 step 4); it calls
`finalize` with no bytes only for the empty message. It truncates the MAC
and compares MACs (§6.3).

Each takes the number of bytes of stack below the stack pointer that an
implementation's calls and frames use (`stack`, see `Sig.contract`), where
it keeps its working space.
-/

namespace VG.Spec.Cmac

/-- `vg_cmac_triple_des_init(key: *const u8, key_len: usize, out: *mut [u8; 400])`.
`key_len` is public. -/
def tdesInitSig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("out", .array true .u8 400)]

/-- `init`'s precondition: a 16- or 24-byte key. -/
def tdesInitPre (pb : Nat) : Curry (tdesInitSig.words pb) (Mem → Prop) :=
  fun _key keyLen _out _ => TripleDes.validKey keyLen.toNat

/-- Writes the key schedule of the key at `key` (`TripleDes.expandKey`, in
`TripleDes.scheduleAt`'s layout) to the first 384 bytes at `out`, and TDEA's
subkeys `K1 ‖ K2` for it (§6.1) to bytes 384–399. -/
def tdesInitPost (pb : Nat) : tdesInitSig.Post pb := fun key keyLen out m m' _ =>
  let k := TripleDes.expandKey (TripleDes.bytesAt m key keyLen.toNat)
  let ks := subkeys (tdesWith k) 8
  TripleDes.scheduleAt m' out = k ∧ Aes.bytesAt m' (out + 384) 16 = ks.1 ++ ks.2

/-- For a 16- or 24-byte TDEA key at `key`: `tdesInitPost`. -/
def tdesInitContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  tdesInitSig.contract A (pre := tdesInitPre A.ptrBits) (post := tdesInitPost A.ptrBits)
    (stack := stack)

/-- `vg_cmac_triple_des_init` on every target. -/
def tdesInitApi : Api where
  module := "cmac_triple_des"
  name := "vg_cmac_triple_des_init"
  sig := tdesInitSig
  contracts := some fun A stack => tdesInitContract A stack
  summary := "Sets up TDEA-CMAC (NIST SP 800-38B) for a 16- or 24-byte TDEA key (FIPS 46-3; a \
    16-byte key is `K1 ‖ K2` with `K3 = K1`, parity bits are ignored): writes the key schedule \
    (the three DES schedules, sixteen encryption-order 48-bit round keys each, zero-extended \
    into little-endian 64-bit slots) to the first 384 bytes of `*out`, and the CMAC subkeys \
    `K1 ‖ K2` (§6.1) to the last 16, where `L = CIPH_K(0⁶⁴)`, `K1 = L << 1` (XORed with \
    `R₆₄ = 0⁵⁹11011` if the leftmost bit of `L` is 1) and `K2` is `K1` doubled the same way.\n\n\
    Contract: `VG.Spec.Cmac.tdesInitContract`. Constant time: only the pointers and `key_len` \
    may affect timing, not the key, the key schedule or the subkeys."
  safety := ["`key_len` must be 16 or 24."]

/-- `vg_cmac_triple_des_update(schedule: *const [u8; 384], state: *mut [u8; 8], data: *const [u8; 8], n: usize)`. -/
def tdesUpdateSig : Sig where
  params := [("schedule", .array false .u8 384), ("state", .array true .u8 8),
    ("data", .slice false (.array .u8 8) "n")]

/-- With the TDEA key schedule at `schedule`: replaces the block `C` at
`state` with §6.2 step 6 continued from `C` over the `n` blocks at
`data`. -/
def tdesUpdatePost (pb : Nat) : tdesUpdateSig.Post pb := fun schedule state data n m m' _ =>
  let ciph := tdesWith (TripleDes.scheduleAt m schedule)
  Aes.bytesAt m' state 8 = chain ciph (Aes.bytesAt m state 8) (blocksAt m data 8 n.toNat)

/-- `tdesUpdatePost`. -/
def tdesUpdateContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  tdesUpdateSig.contract A (post := tdesUpdatePost A.ptrBits) (stack := stack)

/-- `vg_cmac_triple_des_update` on every target. -/
def tdesUpdateApi : Api where
  module := "cmac_triple_des"
  name := "vg_cmac_triple_des_update"
  sig := tdesUpdateSig
  contracts := some fun A stack => tdesUpdateContract A stack
  summary := "CMAC's chaining (NIST SP 800-38B §6.2 step 6) for TDEA, over whole blocks: replaces \
    the block `C₀` at `*state` with `Cₙ`, where `Cᵢ = CIPH_K(Cᵢ₋₁ ⊕ Mᵢ)` for the `n` 8-byte \
    blocks `M₁ … Mₙ` starting at `data`. `CIPH_K` is TDEA encryption (FIPS 46-3) with the \
    three DES schedules at `*schedule`, as `vg_cmac_triple_des_init` writes them.\n\n\
    Contract: `VG.Spec.Cmac.tdesUpdateContract`. Constant time: only the pointers and `n` may \
    affect timing, not the key schedule, the chaining value or the data."
  safety := []

/-- `vg_cmac_triple_des_finalize(key: *const [u8; 400], state: *mut [u8; 8], last: *const u8, last_len: usize)`. -/
def tdesFinalizeSig : Sig where
  params := [("key", .array false .u8 400), ("state", .array true .u8 8),
    ("last", .slice false .u8 "last_len")]

/-- `finalize`'s precondition: at most a block of last bytes. -/
def tdesFinalizePre (pb : Nat) : Curry (tdesFinalizeSig.words pb) (Mem → Prop) :=
  fun _key _state _last lastLen _ => lastLen.toNat ≤ 8

/-- With the TDEA key schedule in the first 384 bytes at `key` and TDEA's
subkeys `K1 ‖ K2` for it in bytes 384–399: if the block at `state` is the
chaining value (§6.2 step 6, from `C₀ = 0⁶⁴`) of a message `msg` of whole
blocks, and `last_len` is not 0 unless `msg` is empty (so that the
`last_len` bytes at `last` are `Mₙ*`), replaces it with the CMAC `Cₙ` of
`msg` followed by those bytes. -/
def tdesFinalizePost (pb : Nat) : tdesFinalizeSig.Post pb := fun key state last lastLen m m' _ =>
  let ciph := tdesWith (TripleDes.scheduleAt m key)
  let ks := subkeys ciph 8
  Aes.bytesAt m (key + 384) 16 = ks.1 ++ ks.2 →
  ∀ msg : List Byte, msg.length % 8 = 0 → (msg = [] ∨ 0 < lastLen.toNat) →
    Aes.bytesAt m state 8 = chain ciph (zeros 8) (blocks 8 msg) →
    Aes.bytesAt m' state 8 = macFull ciph 8 (msg ++ Aes.bytesAt m last lastLen.toNat)

/-- For `last_len` at most 8: `tdesFinalizePost`. -/
def tdesFinalizeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  tdesFinalizeSig.contract A (pre := tdesFinalizePre A.ptrBits) (post := tdesFinalizePost A.ptrBits)
    (stack := stack)

/-- `vg_cmac_triple_des_finalize` on every target. -/
def tdesFinalizeApi : Api where
  module := "cmac_triple_des"
  name := "vg_cmac_triple_des_finalize"
  sig := tdesFinalizeSig
  contracts := some fun A stack => tdesFinalizeContract A stack
  summary := "Finishes a TDEA-CMAC computation (NIST SP 800-38B §6.2, with `Tlen = 64`): if the \
    block at `*state` is the chaining value `Cₙ₋₁` of the message's blocks but the last (as \
    `vg_cmac_triple_des_update` computes it from a zero block), and the `last_len` bytes at \
    `last` are the message's last bytes `Mₙ*`, replaces it with the MAC \
    `Cₙ = CIPH_K(Cₙ₋₁ ⊕ Mₙ)`, where `Mₙ = K1 ⊕ Mₙ*` if `last_len` is 8, and \
    `Mₙ = K2 ⊕ (Mₙ* ‖ 10ʲ)` otherwise. `*key` is the 384-byte key schedule \
    followed by the subkeys `K1 ‖ K2`, as `vg_cmac_triple_des_init` writes them. `last_len` \
    is 0 only for the empty message.\n\n\
    Contract: `VG.Spec.Cmac.tdesFinalizeContract`. Constant time: only the pointers and \
    `last_len` may affect timing, not the key schedule, the subkeys, the chaining value or the \
    data."
  safety := ["`last_len` must be at most 8."]

end VG.Spec.Cmac
