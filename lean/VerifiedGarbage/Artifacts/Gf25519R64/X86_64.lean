import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Impl.X25519.X86_64
import VerifiedGarbage.Proof.X25519.X86_64.Invert
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Sound
import VerifiedGarbage.Proof.X25519.X86_64.Lit

/-! # Curve25519's inversion, in radix `2^64`, on x86-64 -/

namespace VG.Artifacts.Gf25519R64.X86_64

def artifacts : List Artifact := [
  { Spec.X25519.Field64.invertApi with
    target := X86_64.target
    doc := Spec.X25519.Field64.invertApi.doc (notes := ["Uses baseline integer instructions. The \
      function keeps `rbx`, `rbp` and `r12`–`r15` in `xmm0`–`xmm5`, and inverts by Bernstein–Yang \
      divsteps (`Proof/X25519/X86_64/Divstep/`): ten batches of 59 divsteps on the low words of \
      `f` and `g`, each applied to the full `f`, `g`, `a` and `b` by a 2×2 matrix of signed \
      words, then `a` times the constant `±2^-590`, with `vg_x25519`'s field multiplication."])
    code := Impl.X25519.X86_64.invertFn
    contract := Spec.X25519.Field64.invertContract X86_64.abi
    verified := Proof.X25519.X86_64.invert_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Gf25519R64.X86_64
