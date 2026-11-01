module

public import VerifiedGarbage.Spec.Gcm.Precomputed
public import VerifiedGarbage.Proof.Gcm.Contract
public import VerifiedGarbage.Proof.Gcm.OutOfPlaceContract

/-!
# AES-GCM with precomputed powers: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.
-/

@[expose] public section

namespace VG.Proof.Gcm

open VG.Spec VG.Spec.Gcm

/-- `vg_aes_gcm_encrypt_blocks_precomputed(ctx: *const [u64; 128], rounds: usize, counter: *mut [u8; 16], y: *mut [u8; 16], data: *mut [u8; 16], n: usize, scratch: *mut [u64; 264])`,
and `vg_aes_gcm_decrypt_blocks_precomputed` with the same signature:
`cryptBlocksSig` with the larger key context. -/
def cryptBlocksPrecomputedSig : Sig where
  params := [("ctx", .array false .u64 128), ("rounds", .int .usize true),
    ("counter", .array true .u8 16), ("y", .array true .u8 16),
    ("data", .slice true (.array .u8 16) "n"), ("scratch", .array true .u64 264)]

/-- `rounds` is 10, 12 or 14, and the key context at `ctx` holds the powers
of its hash subkey. -/
def cryptBlocksPrecomputedPre (pb : Nat) :
    Curry (cryptBlocksPrecomputedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _counter _y _data _n _scratch m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧ PowersRepr m ctx

/-- `encryptBlocksContract`'s postcondition, with the larger key context. -/
def encryptBlocksPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cryptBlocksPrecomputedSig.contract A (pre := cryptBlocksPrecomputedPre A.ptrBits)
    (post := fun ctx rounds counter y data n _scratch m m' _ =>
      let c := ctr32 (ctxCiph m ctx rounds.toNat) (blockAt m counter) (blocksAt m data n.toNat)
      blocksAt m' data n.toNat = c ∧
        blockAt m' counter = Nat.repeat inc32 n.toNat (blockAt m counter) ∧
        blockAt m' y = ghashFrom (ctxH m ctx) (blockAt m y) c)
    (stack := stack)

/-- `decryptBlocksContract`'s postcondition, with the larger key context. -/
def decryptBlocksPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cryptBlocksPrecomputedSig.contract A (pre := cryptBlocksPrecomputedPre A.ptrBits)
    (post := fun ctx rounds counter y data n _scratch m m' _ =>
      let c := blocksAt m data n.toNat
      blocksAt m' data n.toNat = ctr32 (ctxCiph m ctx rounds.toNat) (blockAt m counter) c ∧
        blockAt m' counter = Nat.repeat inc32 n.toNat (blockAt m counter) ∧
        blockAt m' y = ghashFrom (ctxH m ctx) (blockAt m y) c)
    (stack := stack)

end VG.Proof.Gcm
