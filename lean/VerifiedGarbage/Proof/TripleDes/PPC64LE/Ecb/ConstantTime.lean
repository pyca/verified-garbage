module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ConstantTime
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Ecb
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.ConstantTime
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
meta import VerifiedGarbage.Impl.TripleDes.PPC64LE.Ecb
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet

/-! # Constant-time Triple DES ECB on PPC64LE

The block functions are analysed at their calls; they never write `r31`,
which counts the blocks left, nor `r3`–`r5`. -/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

theorem ecbEncrypt_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.r3, .r4, .r5, .r6]) Ecb.encrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

theorem ecbDecrypt_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.r3, .r4, .r5, .r6]) Ecb.decrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

end VG.Proof.TripleDes.PPC64LE
