import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Impl.X25519.X86.Field32
import VerifiedGarbage.Proof.X25519.X86.Field32.Verified

/-! # Powers in curve25519's field, in radix `2^32`, on x86 (32-bit) -/

namespace VG.Artifacts.Gf25519R32.X86

open VG.Spec.X25519.Field32 VG.Impl.X25519.X86.Field32 VG.Proof.X25519.X86.Field32

/-- How the function works. -/
def notes : List String := ["Uses baseline integer instructions. The function saves `ebx`, `esi`, \
  `edi` and `ebp` in its own working space, copies `a` to it, and runs the addition chain of \
  ref10's `fe_invert` up to `a^(2^250 - 1)` (249 squarings, most in loops counted by `esi`, and 10 \
  multiplications) with X25519's x86 product: the 512-bit product by columns (product scanning, \
  each product of two different words of a square computed once and doubled), folded with \
  `2^256 = 38` into eight words. It then restores the registers."]

def artifacts : List Artifact := [
  { pow250Api with
    target := X86.target
    doc := pow250Api.doc (notes := notes)
    code := pow250Fn
    contract := pow250Contract X86.abi
    verified := pow250Fn_verified
    ofSig := by unfold pow250Contract; exact ⟨_, _, _, rfl⟩
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Gf25519R32.X86
