module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.AArch64.Comb
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP384r1.Lit
public import VerifiedGarbage.Proof.Ecdsa.AArch64.SignParts
import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP384r1Literals
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.AArch64.Comb
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP384r1.Lit
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.SignParts
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP384r1Literals
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # The fixed-base signing code as a kernel-checked literal

`combCfg` is `brainpoolp384r1` with the comb's table, so the code around the
comb is `signBrainpoolP384r1`'s: its literal reads those parts in that code's
(`Proof/Ecdsa/AArch64/SignParts.lean`), and the kernel builds only the comb.
That the parts are the same code is the kernel's to check alone
(`kernel_rfl`), by unfolding the two: the elaborator would evaluate them. -/

@[expose] public section

namespace VG

namespace Impl.Ecdsa.AArch64.BrainpoolP384r1
open VG.AArch64 VG.Proof.Ecdsa.AArch64.SignParts

noncomputable abbrev combPPow.lit : Prog isa := pPowOf signBrainpoolP384r1.lit
theorem combPPow.lit_eq : combCfg.pPow = combPPow.lit :=
  Eq.trans (b := pPowOf signBrainpoolP384r1) (by kernel_rfl) (congrArg pPowOf signBrainpoolP384r1.lit_eq)

noncomputable abbrev combMiddle.lit : Prog isa := middleOf signBrainpoolP384r1.lit
theorem combMiddle.lit_eq : combCfg.middle = combMiddle.lit :=
  Eq.trans (b := middleOf signBrainpoolP384r1) (by kernel_rfl) (congrArg middleOf signBrainpoolP384r1.lit_eq)

noncomputable abbrev combNPow.lit : Prog isa := nPowOf signBrainpoolP384r1.lit
theorem combNPow.lit_eq : combCfg.nPow = combNPow.lit :=
  Eq.trans (b := nPowOf signBrainpoolP384r1) (by kernel_rfl) (congrArg nPowOf signBrainpoolP384r1.lit_eq)

noncomputable abbrev combScalar.lit : Prog isa := scalarOf signBrainpoolP384r1.lit
theorem combScalar.lit_eq : combCfg.scalar = combScalar.lit :=
  Eq.trans (b := scalarOf signBrainpoolP384r1) (by kernel_rfl) (congrArg scalarOf signBrainpoolP384r1.lit_eq)

end Impl.Ecdsa.AArch64.BrainpoolP384r1

materialize_code Impl.Ecdsa.AArch64.BrainpoolP384r1.signComb

end VG
