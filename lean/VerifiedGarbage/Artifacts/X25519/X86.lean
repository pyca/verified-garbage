import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Impl.X25519.X86
import VerifiedGarbage.Proof.X25519.X86.Verified
import VerifiedGarbage.Proof.X25519.X86.Lit
import VerifiedGarbage.Proof.X25519.X86.Base.Verified

/-! # X25519 (RFC 7748) on x86 -/

namespace VG.Artifacts.X25519.X86

def artifacts : List Artifact := [
  { Spec.X25519.x25519Api with
    target := X86.target
    doc := Spec.X25519.x25519Api.doc (notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. Field elements are eight 32-bit words, multiplied by product scanning \
      (squared with each product of distinct words doubled) and reduced with `2^256 = 38` (mod p); \
      the inversion is ref10's addition chain."])
    code := Impl.X25519.X86.x25519
    contract := Spec.X25519.x25519Contract X86.abi
    verified := Proof.X25519.X86.x25519_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.X25519.x25519BaseApi with
    target := X86.target
    doc := Spec.X25519.x25519BaseApi.doc (notes := ["Computes `[k] B` on edwards25519 with \
      `vg_ed25519_scalar_base`'s comb (64 signed radix-16 digits, 32 tables of 8 points, every \
      entry of a table read and masked), for the clamped scalar `k`, then `u = (Z + Y) / (Z - Y)` \
      with one inversion: RFC 7748 §4.1's birational map, which takes edwards25519's base point to \
      `u = 9` and its group law to the ladder's (`VG.Proof.X25519.Edwards.x25519_basePoint`). \
      Callee-saved registers are saved in the first 16 bytes of `scratch`."])
    code := Impl.X25519.X86.Base.x25519Base
    contract := Spec.X25519.x25519BaseContract X86.abi
    verified := Proof.X25519.X86.Base.x25519Base_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.X25519.X86
