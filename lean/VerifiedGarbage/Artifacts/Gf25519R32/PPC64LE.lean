module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.FieldVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Products and powers in curve25519's field, in radix `2^32`, on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Gf25519R32.PPC64LE

open VG.Spec.X25519.Field32 VG.Impl.Ed25519.PPC64LE VG.Proof.Ed25519.PPC64LE

/-- How the product works. -/
def mulNotes : List String := ["Uses baseline integer instructions and only volatile registers. \
  The function zero-extends the offsets and runs X25519's PPC64LE product (row by row, with \
  `mulld`, each step `a_i b_j + acc + carry` fitting in 64 bits, into sixteen 32-bit limbs at \
  byte 864, then `lo + 38 hi` and the carry folded in twice) with its operands and result \
  through pointers: `ws` plus each offset."]

/-- How the powers work. -/
def notes : List String := ["Uses baseline integer instructions and only volatile registers. \
  The function runs the addition chain of ref10's `fe_invert` up to `a^(2^250 - 1)` (249 \
  squarings, most in loops counted by `r12`, and 10 multiplications), with X25519's PPC64LE \
  product inlined (row by row, with `mulld`, then `lo + 38 hi` and the carry folded in) and its \
  temporaries in bytes 512 to 639."]

def artifacts : List Artifact := [
  mulApi.artifact PPC64LE.target {
    notes := mulNotes
    code := mulFn
    verified := mulFn_verified },
  pow250Api.artifact PPC64LE.target {
    notes := notes
    code := pow250Fn
    verified := pow250Fn_verified }]

end VG.Artifacts.Gf25519R32.PPC64LE
