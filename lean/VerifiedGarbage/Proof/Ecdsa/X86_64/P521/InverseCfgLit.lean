module

public import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.InverseVerified
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.InverseLit

/-!
# The inversions' code as the registration writes it, as literals

The registration (`Generic/P521/X86_64/InverseP521.lean`) writes each function's
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

namespace VG.Proof.Ecdsa.X86_64.P521.Inverse

open VG.Impl.Ecdsa.X86_64

noncomputable def invPCfg.lit : Prog VG.X86_64.isa := invP.lit
theorem invPCfg.lit_eq : (cfg false).invFn (cfg false).pPowI = invPCfg.lit := invP.lit_eq

noncomputable def invPAdxCfg.lit : Prog VG.X86_64.isa := invPAdx.lit
theorem invPAdxCfg.lit_eq : (cfg true).invFn (cfg true).pPowI = invPAdxCfg.lit := invPAdx.lit_eq

noncomputable def invNCfg.lit : Prog VG.X86_64.isa := invN.lit
theorem invNCfg.lit_eq : (cfg false).invFn (cfg false).nPowI = invNCfg.lit := invN.lit_eq

end VG.Proof.Ecdsa.X86_64.P521.Inverse
