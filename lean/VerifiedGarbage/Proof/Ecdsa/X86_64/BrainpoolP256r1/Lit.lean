module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.X86_64
public import VerifiedGarbage.Proof.Weierstrass.X86_64.BrainpoolP256r1Literals
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.X86_64
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.BrainpoolP256r1Literals
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.BrainpoolP256r1

open VG.Impl.Ecdsa.X86_64 VG.Proof.Weierstrass.X86_64

/-! The signature's configuration is `brainpoolp256r1` with the comb's tables
declared, and its inversions are `brainpoolp256r1`'s code, which has literals
(`BrainpoolP256r1Literals`): they are those of `brainpoolp256r1S`'s too, by name
(`pPowS.lit_eq`, `nPowS.lit_eq`), so that the signature's literal reads them
rather than have the kernel build the inversions again. -/

theorem pPowS_eq : Cfg.pPow brainpoolp256r1S = Cfg.pPow brainpoolp256r1 := by kernel_rfl

theorem nPowS_eq : Cfg.nPow brainpoolp256r1S = Cfg.nPow brainpoolp256r1 := by kernel_rfl

noncomputable abbrev pPowS.lit : Prog VG.X86_64.isa := BrainpoolP256r1Literals.pPow.lit

noncomputable abbrev nPowS.lit : Prog VG.X86_64.isa := BrainpoolP256r1Literals.nPow.lit

theorem pPowS.lit_eq : Cfg.pPow brainpoolp256r1S = pPowS.lit := pPowS_eq.trans BrainpoolP256r1Literals.pPow.lit_eq

theorem nPowS.lit_eq : Cfg.nPow brainpoolp256r1S = nPowS.lit := nPowS_eq.trans BrainpoolP256r1Literals.nPow.lit_eq

materialize_code signBrainpoolP256r1

end VG.Proof.Ecdsa.X86_64.BrainpoolP256r1
