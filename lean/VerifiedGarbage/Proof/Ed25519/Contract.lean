module

public import VerifiedGarbage.Spec.Ed25519.Contract

/-!
# Ed25519: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

The scalar and group primitives that the complete operations are built from:
`vg_ed25519_scalar_base`, `_scalar_reduce`, `_scalar_mul_add` and
`_verify_equation`. `verifyEquation` alone checks a supplied challenge, which
`verify`'s predicate needs reduced modulo `L` (with `scalarReduce`) before the
call. They take the complete operations' 8 KiB of scratch space, whose
contents are unspecified on return.
-/

@[expose] public section

namespace VG.Proof.Ed25519

open VG.Spec VG.Spec.Ed25519

/-- `(out: *mut [u8; 32], scalar: *const [u8; 32], scratch: *mut [u64; 1024])`. -/
def scalarBaseSig : Sig where
  params := [("out", .array true .u8 32), ("scalar", .array false .u8 32),
    ("scratch", .array true .u64 scratchWords)]

/-- Encode `[s]B`, for the entire unsigned 256-bit scalar, without pruning. -/
def scalarBaseContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  scalarBaseSig.contract A
    (post := fun out scalar _scratch m m' _ =>
      bytesAt m' out 32 = scalarBase (bytesAt m scalar 32))
    (writeArgs := true) (stack := stack)

/-- `(out: *mut [u8; 32], wide: *const [u8; 64], scratch: *mut [u64; 1024])`. -/
def scalarReduceSig : Sig where
  params := [("out", .array true .u8 32), ("wide", .array false .u8 64),
    ("scratch", .array true .u64 scratchWords)]

/-- Reduce all 512 input bits modulo `L`, returning a canonical scalar. -/
def scalarReduceContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  scalarReduceSig.contract A
    (post := fun out wide _scratch m m' _ =>
      bytesAt m' out 32 = scalarReduce (bytesAt m wide 64))
    (writeArgs := true) (stack := stack)

/-- `(out: *mut [u8; 32], r: *const [u8; 32], k: *const [u8; 32], s: *const [u8; 32], scratch: *mut [u64; 1024])`. -/
def scalarMulAddSig : Sig where
  params := [("out", .array true .u8 32), ("r", .array false .u8 32),
    ("k", .array false .u8 32), ("s", .array false .u8 32),
    ("scratch", .array true .u64 scratchWords)]

/-- Compute `(r + k*s) mod L`. All three unsigned 256-bit inputs are secret;
they need not be reduced modulo `L`. -/
def scalarMulAddContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  scalarMulAddSig.contract A
    (post := fun out r k s _scratch m m' _ =>
      bytesAt m' out 32 = scalarMulAdd (bytesAt m r 32) (bytesAt m k 32) (bytesAt m s 32))
    (writeArgs := true) (stack := stack)

/-- `(pk: *const [u8; 32], signature: *const [u8; 64], challenge: *const [u8; 64], scratch: *mut [u64; 1024]) -> u32`. -/
def verifyEquationSig : Sig where
  params := [("pk", .array false .u8 32), ("signature", .array false .u8 64),
    ("challenge", .array false .u8 64), ("scratch", .array true .u64 scratchWords)]
  ret := some .u32

/-- Check the encodings and equation using the full 512-bit challenge, as
given: no reduction modulo `L` takes place here, nor message hashing.
All inputs may affect timing. -/
def verifyEquationContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  verifyEquationSig.contract A
    (post := fun pk signature challenge _scratch m _m' r =>
      r = if verifyEquation (bytesAt m pk 32) (bytesAt m signature 64)
        (bytesAt m challenge 64) then 1 else 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun pk signature challenge _scratch m =>
      (bytesAt m pk 32 ++ bytesAt m signature 64 ++ bytesAt m challenge 64).map (·.toNat))

end VG.Proof.Ed25519
