module

public import VerifiedGarbage.Spec.Cmac.TripleDesContract

/-!
# TDEA-CMAC (3DES-CMAC): the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

The three primitives streaming TDEA-CMAC is built from:

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

Their caller keeps the chaining value between calls, and holds back the
last block of what it has been given, even a complete one, since only
`finalize` knows whether a block is the last (§6.2 step 4); it calls
`finalize` with no bytes only for the empty message.
-/

@[expose] public section

namespace VG.Proof.Cmac

open VG.Spec VG.Spec.Cmac

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

end VG.Proof.Cmac
