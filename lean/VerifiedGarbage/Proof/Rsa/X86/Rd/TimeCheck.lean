module

public import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Rsa.X86.RvTaint
meta import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
meta import VerifiedGarbage.Proof.Rsa.X86.RvTaint
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint

/-! # The taint checks of Appendix C.2 on i686

Every piece of `RecoverDetRt.sized` but its loops' conditions and the GCD
leaks only the arguments, `edi` and `esp` (`τA`), and keeps them public: a
piece's check ends in a taint at least `τA` (`PubA`). The loops count in the
header word `sK`, which the analysis cannot follow through the arrays'
stores, so their bodies are checked alone.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86
open VG.Impl.Rsa.X86.Keys (aZero)
open VG.Impl.Rsa.X86.KeyRt (copy chain zeroWide eqSFast)
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.RecoverDetRt hiding aN aP aQ

/-- Code that leaks only what `τA` makes public, and keeps it public. -/
def PubA (c : Prog isa) : Prop :=
  ∃ hint, (VG.Taint.check sseTaint τA c hint).map (sseTaint.le τA ·) = some true

theorem loadsPub : PubA VG.Impl.Rsa.X86.RecoverRt.loads := ⟨_, by taint_decide⟩
theorem prodPub : PubA VG.Impl.Rsa.X86.RecoverRt.prod := ⟨_, by taint_decide⟩
theorem storesPub : PubA VG.Impl.Rsa.X86.RecoverRt.stores := ⟨_, by taint_decide⟩
theorem deMinusPub : PubA deMinus := ⟨_, by taint_decide⟩
theorem twosInitPub : PubA twosInit := ⟨_, by taint_decide⟩
theorem countNPub : PubA (.block countN) := ⟨_, by taint_decide⟩
theorem countWPub : PubA (.block countW) := ⟨_, by taint_decide⟩
theorem twosBodyPub : PubA twosBody := ⟨_, by taint_decide⟩
theorem gcdSetPub : PubA gcdSet := ⟨_, by taint_decide⟩
theorem zeroWZ2Pub : PubA (zeroWide wid wZ2) := ⟨_, by taint_decide⟩
theorem zeroWAPub : PubA (zeroWide wid wA) := ⟨_, by taint_decide⟩
theorem zeroWBPub : PubA (zeroWide wid wB) := ⟨_, by taint_decide⟩
theorem stepAPub : PubA (productStep aG wX3 wA wT wZ2) := ⟨_, by taint_decide⟩
theorem stepBPub : PubA (productStep aBy wB wA wT wZ2) := ⟨_, by taint_decide⟩
theorem divAPub : PubA divA := ⟨_, by taint_decide⟩
theorem divBPub : PubA divB := ⟨_, by taint_decide⟩
theorem incPub : PubA (chain nar .adc aD aD aOne1 false) := ⟨_, by taint_decide⟩
theorem copyByPub : PubA (copy nar aBy aD) := ⟨_, by taint_decide⟩
theorem copyBPub : PubA (copy nar (2 * wB) aD) := ⟨_, by taint_decide⟩
theorem minus4nPub : PubA minus4n := ⟨_, by taint_decide⟩
theorem copyRmPub : PubA (copy nar aRm aZero) := ⟨_, by taint_decide⟩
theorem copyYPub : PubA (copy nar aY aZero) := ⟨_, by taint_decide⟩
theorem sqrtBodyPub : PubA sqrtBody := ⟨_, by taint_decide⟩
theorem eqOk5Pub : PubA (eqSFast nar sOk5 aRm aZero) := ⟨_, by taint_decide⟩
theorem factorsPub : PubA factors := ⟨_, by taint_decide⟩

end VG.Proof.Rsa.X86.Recover
