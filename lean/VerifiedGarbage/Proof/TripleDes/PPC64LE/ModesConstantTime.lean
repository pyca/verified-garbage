module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ConstantTime
import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesLit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Modes
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.ConstantTime
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesLit
meta import VerifiedGarbage.Impl.TripleDes.PPC64LE.Modes
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet

/-! # Constant-time Triple DES modes on PPC64LE

Only the pointers and the count (`r3`–`r7`) are public. The block functions
are analysed at their calls; they never write `r29`–`r31`, which hold the
IV's address, the steps left and the data pointer, nor `r3` and `r5`, which
hold the schedule and the scratch buffer. -/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

/-- The modes' public arguments. -/
abbrev modePub : State → State → Prop := PublicRegs [.r3, .r4, .r5, .r6, .r7]

theorem modes_ofRegs (s₁ s₂ : State) (h : modePub s₁ s₂) :
    taint.Agree (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) s₁ s₂ :=
  ⟨h.1, fun r hr => h.2 r (Taint.mem_ofRegs.mp hr)⟩

theorem cbcEncryptChained_constantTime (pre : State → Prop) :
    ConstantTime isa pre modePub cbcEncryptChained :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cbcDecryptChained_constantTime (pre : State → Prop) :
    ConstantTime isa pre modePub cbcDecryptChained :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem ofb_constantTime (pre : State → Prop) : ConstantTime isa pre modePub ofb :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cfbEncrypt_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbEncrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cfbDecrypt_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbDecrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cfb8Encrypt_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfb8Encrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cfb8Decrypt_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfb8Decrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

end VG.Proof.TripleDes.PPC64LE
