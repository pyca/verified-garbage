import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Impl.X25519.X86.Field32
import VerifiedGarbage.Proof.X25519.X86.Field32.Verified

/-! # Multiplication in curve25519's field, in radix `2^32`, on x86 (32-bit) -/

namespace VG.Artifacts.Gf25519R32.X86

open VG.Spec.X25519.Field32 VG.Impl.X25519.X86.Field32 VG.Proof.X25519.X86.Field32

/-- How the function works. -/
def notes : List String := ["Uses baseline integer instructions. The function saves `ebx`, `ebp` and \
  `edi` in its own working space, copies the operands to fixed offsets of it, and multiplies them \
  there as X25519's x86 code does: the 512-bit product by columns (product scanning, each product of \
  two different words of a square computed once and doubled), folded with `2^256 = 38` into eight \
  words. It restores the registers and then copies the result to `o`."]

def artifacts : List Artifact := [
  { mulApi with
    target := X86.target
    doc := mulApi.doc (notes := notes)
    code := mulFn
    contract := mulContract X86.abi
    verified := mulFn_verified
    ofSig := by unfold mulContract; exact ⟨_, _, _, rfl⟩
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.Gf25519R32.X86
