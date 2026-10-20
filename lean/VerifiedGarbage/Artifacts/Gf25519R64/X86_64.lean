module

public import VerifiedGarbage.Proof.X25519.X86_64.Invert
public import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Sound
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.X25519.X86_64.Lit

/-! # Curve25519's inversion, in radix `2^64`, on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Gf25519R64.X86_64

def artifacts : List Artifact := [
  Spec.X25519.Field64.invertApi.artifact X86_64.target {
    notes := ["Uses baseline integer instructions. The \
      function keeps `rbx`, `rbp` and `r12`–`r15` in `xmm0`–`xmm5`, and inverts by Bernstein–Yang \
      divsteps (`Proof/X25519/X86_64/Divstep/`): ten batches of 59 divsteps on the low words of \
      `f` and `g`, each applied to the full `f`, `g`, `a` and `b` by a 2×2 matrix of signed \
      words, then `a` times the constant `±2^-590`, with `vg_x25519`'s field multiplication."]
    code := Impl.X25519.X86_64.invertFn
    verified := Proof.X25519.X86_64.invert_verified }]

end VG.Artifacts.Gf25519R64.X86_64
