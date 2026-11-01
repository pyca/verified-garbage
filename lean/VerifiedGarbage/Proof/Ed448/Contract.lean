module

public import VerifiedGarbage.Spec.Ed448.Contract

/-!
# Ed448: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

The scalar and group primitives that the complete operations are built from:
`vg_ed448_scalar_base`, `_scalar_reduce`, `_scalar_mul_add` and
`_verify_equation`. `verifyEquation` alone checks a supplied challenge, which
`verify`'s predicate needs reduced modulo `L` (with `scalarReduce`) before the
call. They take the complete operations' 8 KiB of scratch space, whose
contents are unspecified on return.
-/

@[expose] public section

namespace VG.Proof.Ed448

open VG.Spec VG.Spec.Ed448

/-- `(out: *mut [u8; 57], scalar: *const [u8; 57], scratch: *mut [u64; 1024])`. -/
def scalarBaseSig : Sig where
  params := [("out", .array true .u8 57), ("scalar", .array false .u8 57),
    ("scratch", .array true .u64 scratchWords)]

/-- Encode `[s]B`, for the entire unsigned 456-bit scalar, without pruning. -/
def scalarBaseContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  scalarBaseSig.contract A
    (post := fun out scalar _scratch m m' _ =>
      bytesAt m' out 57 = scalarBase (bytesAt m scalar 57))
    (writeArgs := true) (stack := stack)

/-- `(out: *mut [u8; 57], wide: *const [u8; 114], scratch: *mut [u64; 1024])`. -/
def scalarReduceSig : Sig where
  params := [("out", .array true .u8 57), ("wide", .array false .u8 114),
    ("scratch", .array true .u64 scratchWords)]

/-- Reduce all 912 input bits modulo `L`, returning a canonical scalar. -/
def scalarReduceContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  scalarReduceSig.contract A
    (post := fun out wide _scratch m m' _ =>
      bytesAt m' out 57 = scalarReduce (bytesAt m wide 114))
    (writeArgs := true) (stack := stack)

/-- `(out: *mut [u8; 57], r: *const [u8; 57], k: *const [u8; 57], s: *const [u8; 57], scratch: *mut [u64; 1024])`. -/
def scalarMulAddSig : Sig where
  params := [("out", .array true .u8 57), ("r", .array false .u8 57),
    ("k", .array false .u8 57), ("s", .array false .u8 57),
    ("scratch", .array true .u64 scratchWords)]

/-- Compute `(r + k*s) mod L`. All three unsigned 456-bit inputs are secret;
they need not be reduced modulo `L`. -/
def scalarMulAddContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  scalarMulAddSig.contract A
    (post := fun out r k s _scratch m m' _ =>
      bytesAt m' out 57 = scalarMulAdd (bytesAt m r 57) (bytesAt m k 57) (bytesAt m s 57))
    (writeArgs := true) (stack := stack)

/-- `(pk: *const [u8; 57], signature: *const [u8; 114], challenge: *const [u8; 57], scratch: *mut [u64; 1024]) -> u32`. -/
def verifyEquationSig : Sig where
  params := [("pk", .array false .u8 57), ("signature", .array false .u8 114),
    ("challenge", .array false .u8 57), ("scratch", .array true .u64 scratchWords)]
  ret := some .u32

/-- Check the encodings and the cofactored equation using the 456-bit
challenge as given: no reduction modulo `L` takes place here, nor message
hashing. All inputs may affect timing. -/
def verifyEquationContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  verifyEquationSig.contract A
    (post := fun pk signature challenge _scratch m _m' r =>
      r = if verifyEquation (bytesAt m pk 57) (bytesAt m signature 114)
        (bytesAt m challenge 57) then 1 else 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun pk signature challenge _scratch m =>
      (bytesAt m pk 57 ++ bytesAt m signature 114 ++ bytesAt m challenge 57).map (·.toNat))

end VG.Proof.Ed448
