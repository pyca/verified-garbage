import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Impl.Ed25519.X86.Point32
import VerifiedGarbage.Proof.Ed25519.X86.Point32.Verified

/-! # Ed25519's point additions and doubling, in radix `2^32`, on x86 (32-bit) -/

namespace VG.Artifacts.Ed25519R32.X86

open VG.Spec.Ed25519.Point32 VG.Impl.Ed25519.X86.Point32 VG.Proof.Ed25519.X86.Point32

/-- How the function works. -/
def notes : List String := ["Uses baseline integer instructions. The function saves `ebx`, `ebp` \
  and `edi` in its own working space and runs the addition as the x86 Ed25519 code inlined it: \
  nine products of eight-word field elements, by X25519's x86 product (product scanning, folded \
  with `2^256 = 38`), and additions and subtractions (`a - b + 4p`, so that every word is a \
  natural number), with the temporaries in bytes 320 to 575. It then restores the registers."]

/-- How the affine addition works. -/
def affNotes : List String := ["Uses baseline integer instructions. The function saves `ebx`, \
  `ebp` and `edi` in its own working space and runs the addition of the affine point as the x86 \
  comb of `vg_ed25519_scalar_base` inlined it: seven products of eight-word field elements, `2Z₁` \
  by an addition, by X25519's x86 product (product scanning, folded with `2^256 = 38`), and \
  additions and subtractions (`a - b + 4p`, so that every word is a natural number), with the \
  temporaries in bytes 320 to 575. It then restores the registers."]

/-- How the doubling works. -/
def doubleNotes : List String := ["Uses baseline integer instructions. The function saves `ebx`, \
  `ebp` and `edi` in its own working space and runs RFC 8032's doubling with `-E = 2XY` from one \
  product and `F`, `G` and `H` negated: eight products of eight-word field elements, by X25519's \
  x86 product (product scanning, folded with `2^256 = 38`), and additions and subtractions \
  (`a - b + 4p`, so that every word is a natural number), with the temporaries in bytes 320 to \
  575. It then restores the registers."]

def artifacts : List Artifact := [
  { addApi with
    target := X86.target
    doc := addApi.doc (notes := notes)
    code := addFn
    contract := addContract X86.abi
    verified := addFn_verified
    ofSig := by unfold addContract; exact ⟨_, _, _, rfl⟩
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { addAffineApi with
    target := X86.target
    doc := addAffineApi.doc (notes := affNotes)
    code := affFn
    contract := addAffineContract X86.abi
    verified := affFn_verified
    ofSig := by unfold addAffineContract; exact ⟨_, _, _, rfl⟩
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { doubleApi with
    target := X86.target
    doc := doubleApi.doc (notes := doubleNotes)
    code := doubleFn
    contract := doubleContract X86.abi
    verified := doubleFn_verified
    ofSig := by unfold doubleContract; exact ⟨_, _, _, rfl⟩
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Ed25519R32.X86
