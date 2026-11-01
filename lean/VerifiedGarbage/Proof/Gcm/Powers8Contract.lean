module
-- separate module: the contracts moved out of `Spec/Gcm/Powers8.lean`, beside those of the other GCM specs

public import VerifiedGarbage.Spec.Gcm.Powers8
public import VerifiedGarbage.Proof.Gcm.Contract

/-!
# GHASH with stored powers: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.
-/

@[expose] public section

namespace VG.Proof.Gcm

open VG.Spec VG.Spec.Gcm

/-- `vg_ghash_with_powers(h: *const [u8; 16], y: *mut [u8; 16], data: *const [u8; 16], n: usize, scratch: *mut [u64; 32], pw: *const [u64; 16])`:
`ghashSig` and the powers' buffer. `scratch` is working space. -/
def ghashWithPowersSig : Sig where
  params := ghashSig.params ++ [withPowersParam]

/-- `ghashContract`'s postcondition, given the powers of the hash subkey at
`h` at `pw`. -/
def ghashWithPowersContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ghashWithPowersSig.contract A
    (pre := fun h _y _data _n _scratch pw m => Powers8Repr m pw (blockAt m h))
    (post := fun h y data n _scratch _pw m m' _ =>
      blockAt m' y = ghashFrom (blockAt m h) (blockAt m y) (blocksAt m data n.toNat))
    (stack := stack)

end VG.Proof.Gcm
