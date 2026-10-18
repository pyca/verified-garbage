module

public import VerifiedGarbage.Spec.Gcm.Prepared

/-!
# AES-GCM's whole blocks, partly out of place

**Trusted.** `vg_aes_gcm_encrypt_blocks_split_prepared` is
`vg_aes_gcm_encrypt_blocks_to_prepared` (`encryptBlocksToPreparedContract`)
whose output has more blocks than its input: it encrypts the `n` blocks at
`src` to the first `n` blocks of `dst`, and the `dst_n - n` blocks of `dst`
after them in place, as one run of blocks under one counter and one GHASH.
`vg_aes_gcm_seal_split_prepared` seals a TLS record's payload out of place
and its content type in place (`Spec/Gcm/OutOfPlace.lean`): with this
function, the whole blocks of both are one run, rather than one call for the
blocks read from `src` and another for those after them.

The arguments, what is public and what is secret, the working space, the
prepared powers (`PreparedPowersRepr`) and the disjointness of the buffers
are those of `vg_aes_gcm_encrypt_blocks_to_prepared`; `dst_n` may exceed
`n`, where that function requires them equal. Existing specifications and
contracts are unchanged.
-/

@[expose] public section

namespace VG.Spec.Gcm

/-- `vg_aes_gcm_encrypt_blocks_split_prepared(ctx: *const [u64; 128], rounds: usize, counter: *mut [u8; 16], y: *mut [u8; 16], src: *const [u8; 16], n: usize, dst: *mut [u8; 16], dst_n: usize, scratch: *mut [u64; 264])`:
`encryptBlocksToPreparedSig`. -/
abbrev encryptBlocksSplitPreparedSig := encryptBlocksToPreparedSig

/-- `rounds` is 10, 12 or 14, the output has at least as many blocks as the
input, and `ctx` holds the prepared powers. -/
def encryptBlocksSplitPreparedPre (pb : Nat) :
    Curry (encryptBlocksSplitPreparedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _counter _y _src n _dst dstN _scratch m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      n.toNat ≤ dstN.toNat ∧ PreparedPowersRepr m ctx

/-- With the key context at `ctx`: writes `C = ctr32 CIPH_K CB₁ P` to the
`dst_n` blocks at `dst`, where `P` is the `n` blocks at `src` followed by the
`dst_n - n` blocks of `dst` after its first `n`, and `CB₁` the block at
`counter`; leaves `inc₃₂^dst_n(CB₁)` at `counter`, and replaces the block
`Y` at `y` with `GHASH_H` continued from `Y` over `C`:
`encryptBlocksToPost` with the plaintext read from `src` and then from
`dst`. -/
def encryptBlocksSplitPost (pb : Nat) : encryptBlocksSplitPreparedSig.Post pb :=
  fun ctx rounds counter y src n dst dstN _scratch m m' _ =>
    let p := blocksAt m src n.toNat ++
      blocksAt m (dst + BitVec.ofNat 64 (16 * n.toNat)) (dstN.toNat - n.toNat)
    let c := ctr32 (ctxCiph m ctx rounds.toNat) (blockAt m counter) p
    blocksAt m' dst dstN.toNat = c ∧
      blockAt m' counter = Nat.repeat inc32 dstN.toNat (blockAt m counter) ∧
      blockAt m' y = ghashFrom (ctxH m ctx) (blockAt m y) c

/-- For `rounds` of 10, 12 or 14, at least as many blocks at `dst` as at
`src` and a prepared key context (`encryptBlocksSplitPreparedPre`):
`encryptBlocksSplitPost`. The key context, the counter, `Y` and the data are
secret. -/
def encryptBlocksSplitPreparedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  encryptBlocksSplitPreparedSig.contract A (pre := encryptBlocksSplitPreparedPre A.ptrBits)
    (post := encryptBlocksSplitPost A.ptrBits) (stack := stack)

/-- `vg_aes_gcm_encrypt_blocks_split_prepared` on every target. -/
def encryptBlocksSplitPreparedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_encrypt_blocks_split_prepared"
  sig := encryptBlocksSplitPreparedSig
  contracts := some fun A stack => encryptBlocksSplitPreparedContract A stack
  summary := "AES-GCM's encryption of whole blocks (NIST SP 800-38D §7.1 steps 3 and 5, on whole \
    blocks), partly out of place: with the key context `*ctx` that `vg_aes_gcm_prepare` wrote for \
    `rounds` rounds, encrypts the `n` 16-byte blocks at `src` to the first `n` blocks at `dst`, and \
    the `dst_n - n` blocks of `dst` after them in place, as `vg_aes_gcm_encrypt_blocks_to_prepared` \
    encrypts one run of `dst_n` blocks: XORed with `CIPH_K(CB₁) … CIPH_K(CB_dst_n)`, where `CB₁` is \
    the counter block `*counter` and `CBᵢ₊₁ = inc₃₂(CBᵢ)`; leaves `inc₃₂^dst_n(CB₁)` in `*counter`, \
    and replaces the block `Y` at `*y` with GHASH (§6.4) continued from `Y` over the ciphertext \
    written, with the hash subkey of `*ctx`.\n\n\
    Contract: `VG.Spec.Gcm.encryptBlocksSplitPreparedContract`. Constant time: only the pointers, \
    `rounds`, `n` and `dst_n` may affect timing, not the key context, the counter block, `Y` or \
    the data."
  safety := [
    "`rounds` must be 10, 12 or 14.",
    "`dst_n` must be at least `n`.",
    "The contents of `scratch` on return are unspecified.",
    preparedSafety]

end VG.Spec.Gcm
