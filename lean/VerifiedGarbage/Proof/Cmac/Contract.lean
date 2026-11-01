module

public import VerifiedGarbage.Spec.Cmac.Contract

/-!
# AES-CMAC: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

The three functions streaming AES-CMAC (`Spec/Cmac/Contract.lean`) calls
read the AES key schedule that `vg_aes_expand_key`
(`VG.Spec.Aes.expandKeyContract`) writes, `16 (rounds + 1)` bytes, at the
start of a 240-byte buffer.

* `vg_cmac_aes_subkeys` writes the subkeys `K1 ‖ K2` (§6.1).
* `vg_cmac_aes_update` continues §6.2 step 6 (`Cᵢ = CIPH_K(Cᵢ₋₁ ⊕ Mᵢ)`)
  over whole blocks, from the chaining value `C` in `state`.
* `vg_cmac_aes_finalize` takes the key schedule and the subkeys together,
  as one 272-byte buffer (the 240-byte schedule buffer, then `K1 ‖ K2`),
  and the message's last bytes `Mₙ*` (at most a block); if `state` holds the
  chaining value of the message's other blocks, it replaces it with the
  MAC of the whole message (§6.2, with `Tlen = 128`).

Each takes a `scratch` buffer of working space, sized for the target that
needs the most (room for `vg_aes_ctr32`'s working space and 128 bytes more).
-/

@[expose] public section

namespace VG.Proof.Cmac

open VG.Spec VG.Spec.Cmac

/-- `vg_cmac_aes_subkeys(schedule: *const [u8; 240], rounds: usize, subkeys: *mut [u8; 32], scratch: *mut [u64; 272])`.
`rounds` is public; `scratch` is working space. -/
def aesSubkeysSig : Sig where
  params := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
    ("subkeys", .array true .u8 32), ("scratch", .array true .u64 272)]

/-- For `rounds` of 10, 12 or 14, with the key schedule `w` in the first
`16 (rounds + 1)` bytes at `schedule`: writes the subkeys `K1 ‖ K2` of AES
with that schedule (§6.1) to `subkeys`. -/
def aesSubkeysContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesSubkeysSig.contract A
    (pre := fun _schedule rounds _subkeys _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds subkeys' _scratch m m' _ =>
      let ks := subkeys (aesWith rounds.toNat (Aes.bytesAt m schedule (16 * (rounds.toNat + 1)))) 16
      Aes.bytesAt m' subkeys' 32 = ks.1 ++ ks.2)
    (stack := stack)

/-- `vg_cmac_aes_update(schedule: *const [u8; 240], rounds: usize, state: *mut [u8; 16], data: *const [u8; 16], n: usize, scratch: *mut [u64; 272])`.
`rounds` is public; `scratch` is working space. -/
def aesUpdateSig : Sig where
  params := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
    ("state", .array true .u8 16), ("data", .slice false (.array .u8 16) "n"),
    ("scratch", .array true .u64 272)]

/-- For `rounds` of 10, 12 or 14, with the key schedule `w` in the first
`16 (rounds + 1)` bytes at `schedule`: replaces the block `C` at `state`
with §6.2 step 6 continued from `C` over the `n` blocks at `data`. -/
def aesUpdateContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesUpdateSig.contract A
    (pre := fun _schedule rounds _state _data _n _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds state data n _scratch m m' _ =>
      let ciph := aesWith rounds.toNat (Aes.bytesAt m schedule (16 * (rounds.toNat + 1)))
      Aes.bytesAt m' state 16 = chain ciph (Aes.bytesAt m state 16) (blocksAt m data 16 n.toNat))
    (stack := stack)

/-- `vg_cmac_aes_finalize(key: *const [u8; 272], rounds: usize, state: *mut [u8; 16], last: *const u8, last_len: usize, scratch: *mut [u64; 272])`.
`rounds` is public; `scratch` is working space. -/
def aesFinalizeSig : Sig where
  params := [("key", .array false .u8 272), ("rounds", .int .usize true),
    ("state", .array true .u8 16), ("last", .slice false .u8 "last_len"),
    ("scratch", .array true .u64 272)]

/-- For `rounds` of 10, 12 or 14 and `last_len` at most 16, with the key
schedule `w` in the first `16 (rounds + 1)` bytes at `key` and AES's
subkeys `K1 ‖ K2` for it in bytes 240–271: if the block at `state` is the
chaining value (§6.2 step 6, from `C₀ = 0¹²⁸`) of a message `msg` of whole
blocks, and `last_len` is not 0 unless `msg` is empty (so that the `last_len`
bytes at `last` are `Mₙ*`), replaces it with the CMAC `Cₙ` of `msg`
followed by those bytes. -/
def aesFinalizeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesFinalizeSig.contract A
    (pre := fun _key rounds _state _last lastLen _scratch _ =>
      (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧ lastLen.toNat ≤ 16)
    (post := fun key rounds state last lastLen _scratch m m' _ =>
      let ciph := aesWith rounds.toNat (Aes.bytesAt m key (16 * (rounds.toNat + 1)))
      let ks := subkeys ciph 16
      Aes.bytesAt m (key + 240) 32 = ks.1 ++ ks.2 →
      ∀ msg : List Byte, msg.length % 16 = 0 → (msg = [] ∨ 0 < lastLen.toNat) →
        Aes.bytesAt m state 16 = chain ciph (zeros 16) (blocks 16 msg) →
        Aes.bytesAt m' state 16 = macFull ciph 16 (msg ++ Aes.bytesAt m last lastLen.toNat))
    (stack := stack)

end VG.Proof.Cmac
