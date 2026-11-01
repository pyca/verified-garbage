module
public import VerifiedGarbage.Spec.Camellia.Prepared

/-!
# Camellia's encryption with its subkeys prepared once, in a working space

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

The two callable pieces of `Spec/Camellia/Prepared.lean`, for an
implementation that only encrypts: `vg_camellia_prepare_encrypt_keys`
prepares the subkeys in the order encryption uses them, and
`vg_camellia_encrypt_prepared` encrypts the blocks of the working space
under them. The feedback modes (OFB, CFB in both directions and CBC
encryption) use only Camellia's forward cipher, one block at a time, so an
implementation built for them (e.g. a serial core that encrypts one block
in registers) prepares no decryption order, which
`vg_camellia_prepare_keys` requires.

The working space is described by a `Layout`, as in `Spec/Camellia/Prepared.lean`, of
which these use only the direction `.encrypt`: the table encodes the
schedule's words (`encode rounds w .encrypt`), the batch's `blocks` blocks
are at `buf`, and each function changes only its ranges. The two functions
are only ever composed, so the encoding is the implementation's: the
batch's postcondition holds only where the table encodes some words in the
order of encryption, and then says that the batch is their ECB encryption.

The subkeys, the table and the blocks are secret; the working space's
address and length and the number of rounds are public.
-/

@[expose] public section

namespace VG.Proof.Camellia.Prepared

open VG.Spec VG.Spec.Camellia VG.Spec.Camellia.Prepared

/-! ## The preparation -/

/-- `vg_camellia_prepare_encrypt_keys(schedule, rounds, ws, ws_len)`: the
subkeys, the number of rounds, public, and the working space, in 64-bit
words. -/
def prepareEncryptSig : Sig where
  params := [("schedule", .array false .u8 272), ("rounds", .int .usize true),
    ("ws", .slice true .u64 "ws_len")]

/-- For `rounds` of 18 or 24 and a working space of at least `L.size`
bytes: the table encodes the words of the subkeys of `rounds` rounds at
`schedule` in the order of encryption. Only the bytes of `L.prepScratch`
change. -/
def prepareEncryptContract {I : ISA} (L : Layout) (A : Abi I) (stack : Nat := 0) : Contract I :=
  prepareEncryptSig.contract A
    (pre := fun _schedule rounds _ws wsLen _ =>
      (rounds.toNat = 18 ∨ rounds.toNat = 24) ∧ L.size ≤ 8 * wsLen.toNat)
    (post := fun schedule rounds ws wsLen m m' _ =>
      Holds L m' ws rounds.toNat (wordsAt m schedule rounds.toNat) .encrypt ∧
        Keeps ws wsLen.toNat L.prepScratch m m')
    (stack := stack)

/-! ## A batch -/

/-- For `rounds` of 18 or 24 and a working space of at least `L.size` bytes
whose table encodes some words of `rounds` rounds in the order of
encryption (as `vg_camellia_prepare_encrypt_keys` leaves it): wherever the
table encodes the words `w` of `rounds` rounds in that order, the
`L.blocks` blocks at `L.buf` are replaced by their ECB encryption under the
subkeys of `rounds` rounds of those words, `subkeysOfWords rounds w`. Only
the bytes of `L.cryptScratch` change. Its signature is
`vg_camellia_crypt_prepared`'s, `cryptSig`. -/
def encryptPreparedContract {I : ISA} (L : Layout) (A : Abi I) (stack : Nat := 0) : Contract I :=
  cryptSig.contract A
    (pre := fun rounds ws wsLen m => (rounds.toNat = 18 ∨ rounds.toNat = 24) ∧ L.size ≤ 8 * wsLen.toNat ∧
      ∃ w, Holds L m ws rounds.toNat w .encrypt)
    (post := fun rounds ws wsLen m m' _ =>
      (∀ w, Holds L m ws rounds.toNat w .encrypt →
        blocksAt m' (ws + BitVec.ofNat 64 L.buf) L.blocks =
          ecb (subkeysOfWords rounds.toNat w) .encrypt (blocksAt m (ws + BitVec.ofNat 64 L.buf) L.blocks)) ∧
      Keeps ws wsLen.toNat L.cryptScratch m m')
    (stack := stack)

end VG.Proof.Camellia.Prepared
