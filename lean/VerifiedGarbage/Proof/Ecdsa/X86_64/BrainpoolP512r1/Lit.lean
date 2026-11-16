module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.X86_64
public import VerifiedGarbage.Proof.Weierstrass.X86_64.BrainpoolP512r1Literals
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.X86_64
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.BrainpoolP512r1Literals
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.BrainpoolP512r1

open VG.Impl.Ecdsa.X86_64 VG.Proof.Weierstrass.X86_64

/-! The signature's configuration is `brainpoolp512r1` with the comb's tables
declared, and its inversions are `brainpoolp512r1`'s code, which has literals
(`BrainpoolP512r1Literals`): they are those of `brainpoolp512r1S`'s too, by name
(`pPowS.lit_eq`, `nPowS.lit_eq`), so that the signature's literal reads them
rather than have the kernel build the inversions again. -/

theorem pPowS_eq : Cfg.pPow brainpoolp512r1S = Cfg.pPow brainpoolp512r1 := by kernel_rfl

theorem nPowS_eq : Cfg.nPow brainpoolp512r1S = Cfg.nPow brainpoolp512r1 := by kernel_rfl

noncomputable abbrev pPowS.lit : Prog VG.X86_64.isa := BrainpoolP512r1Literals.pPow.lit

noncomputable abbrev nPowS.lit : Prog VG.X86_64.isa := BrainpoolP512r1Literals.nPow.lit

theorem pPowS.lit_eq : Cfg.pPow brainpoolp512r1S = pPowS.lit := pPowS_eq.trans BrainpoolP512r1Literals.pPow.lit_eq

theorem nPowS.lit_eq : Cfg.nPow brainpoolp512r1S = nPowS.lit := nPowS_eq.trans BrainpoolP512r1Literals.nPow.lit_eq

materialize_code signBrainpoolP512r1

end VG.Proof.Ecdsa.X86_64.BrainpoolP512r1
