module
import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP512r1.InverseCfgLit

public import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP512r1.InverseVerified
public import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP512r1.InverseLit
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# brainpoolP512r1's inversions modulo `p` and `n` on x86-64

`vg_brainpoolp512r1_inv_mod_p` and `vg_brainpoolp512r1_inv_mod_n` (`Spec/Weierstrass/Inverse.lean`),
which the signature, the public key derivation, verification and ECDH call. A generic file (see
`TCB/Emit.lean`) over brainpoolP512r1's group law and inversions `h`, the variant
`Variants/BrainpoolP512r1/X86_64/Law.lean`, whose inversions' soundness the proofs take.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.X86_64.InverseBrainpoolP512r1

open VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.BrainpoolP512r1.Inverse

/-- What the functions run. -/
def note (mod : String) : String :=
  "The function keeps `rbx`, `rbp` and `r12`–`r15` in bytes 1984 to 2031 of `ws` (slot 30) while \
  it runs, and computes the inverse modulo `" ++ mod ++ "` by Bernstein and Yang's divsteps, in \
  batches of 59 (23 batches for eight words), each run on the low words of `f` and `g` packed into \
  64-bit registers and applied to `f`, `g` and the numbers `d`, `e` by the batch's matrix, in its \
  working area at bytes 4504 to 5079, then multiplies by a constant (`2^(5 B) R³ mod " ++ mod ++
  "`) to return to Montgomery form, by `mul` and column-wise Montgomery reduction; nothing depends \
  on the numbers but through masks and `cmov`."

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.BrainpoolP512r1.curve) : List Artifact :=
  [C.invPApi.artifact X86_64.target {
      notes := [note "p"]
      code := cfg.invFn cfg.pPowI
      verified := p_verified h.inv },
    C.invNApi.artifact X86_64.target {
      notes := [note "n"]
      code := cfg.invFn cfg.nPowI
      verified := n_verified h.inv }]

end VG.Generic.BrainpoolP512r1.X86_64.InverseBrainpoolP512r1
