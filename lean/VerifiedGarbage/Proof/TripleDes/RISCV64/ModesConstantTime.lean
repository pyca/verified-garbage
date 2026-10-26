module

public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Modes
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesLit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Impl.TripleDes.RISCV64.Modes
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesLit

/-!
# Constant-time Triple DES modes on RISC-V

Only the pointers and the count (`a0`–`a3`) and the stack pointer are
public. The modes keep their state in `s1`–`s4`, which the block function
never writes (it saves and restores the other callee-saved registers it
uses), and zero the frame through `t3`, a copy of its base made before the
caller's `s1`–`s4` come back from memory.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64

open VG VG.RISCV64 VG.Impl.TripleDes.RISCV64

/-- The modes' public arguments: the stack pointer and `a0`–`a3`. -/
def modePub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.a0, .a1, .a2, .a3], s₁.gpr r = s₂.gpr r

theorem modes_ofRegs (s₁ s₂ : State) (h : modePub s₁ s₂) :
    taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3]) s₁ s₂ :=
  ⟨h.1, fun r hr => h.2 r (Taint.mem_ofRegs.mp hr)⟩

theorem cbcEncryptChained_constantTime (pre : State → Prop) :
    ConstantTime isa pre modePub cbcEncryptChained :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cbcDecryptChained_constantTime (pre : State → Prop) :
    ConstantTime isa pre modePub cbcDecryptChained :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem ofb_constantTime (pre : State → Prop) : ConstantTime isa pre modePub ofb :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cfbEncrypt_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbEncrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cfbDecrypt_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbDecrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cfb8Encrypt_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfb8Encrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cfb8Decrypt_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfb8Decrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

end VG.Proof.TripleDes.RISCV64
