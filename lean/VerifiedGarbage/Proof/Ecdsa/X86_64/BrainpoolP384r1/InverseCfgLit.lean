module

public import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP384r1.InverseVerified
public import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP384r1.InverseLit

/-!
# The inversions' code as the registration writes it, as literals

The registration (`Generic/BrainpoolP384r1/X86_64/InverseBrainpoolP384r1.lean`) writes each function's
code as `Cfg.invFn` of `cfg`, which `lit_decide` (its `spSafe`) does not rewrite
to the literals of `InverseLit.lean`, whose code is written with the curve's
configuration itself: it would evaluate the divsteps again. A literal of code
written as a term (`materialize_code N := t`, `Proof/Framework/Lit.lean`) is
found where the term occurs as written, so each function's literal is given
here again, as `N.lit` and `N.lit_eq : t = N.lit` for the registration's term
`t` (by `InverseLit`'s equation, the two terms being the same by unfolding
`cfg`), and nothing is evaluated again.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.BrainpoolP384r1.Inverse

open VG.Impl.Ecdsa.X86_64

noncomputable def invPCfg.lit : Prog VG.X86_64.isa := invP.lit
theorem invPCfg.lit_eq : cfg.invFn cfg.pPowI = invPCfg.lit := invP.lit_eq

noncomputable def invNCfg.lit : Prog VG.X86_64.isa := invN.lit
theorem invNCfg.lit_eq : cfg.invFn cfg.nPowI = invNCfg.lit := invN.lit_eq

end VG.Proof.Ecdsa.X86_64.BrainpoolP384r1.Inverse
