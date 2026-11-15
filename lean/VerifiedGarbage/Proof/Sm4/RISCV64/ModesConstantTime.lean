module

public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
public import VerifiedGarbage.Impl.Sm4.RISCV64.Modes
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
meta import VerifiedGarbage.Impl.Sm4.RISCV64.Modes
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit

/-!
# Constant-time SM4 modes on RISC-V

Only the pointers and the count (`a0`–`a3`) and the stack pointer are
public. The modes keep their state in `s1`–`s4`; around ECB's code the core
keeps `s1`–`s3` in `a1`, `a2` and `a4`, which the rounds never write,
computes `s4` again from ECB's base, and reloads the schedule's address,
`a0`, from the frame, where it stored it (a public slot). The caller's
`s0`–`s11` pass through ECB's working space and come back secret, but
nothing addresses or branches on them.

The batch encryption and the preparation of the round keys in encryption's
order, which every mode calls, are analysed once, as summaries
(`cryptSum`, `prepareSum`), which the modes' checks use
(`taint_decide_sum`) in place of the analysis of the functions in each.
-/

@[expose] public section

namespace VG.Proof.Sm4.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4.RISCV64

/-- The modes' public arguments: the stack pointer and `a0`–`a3`. -/
def modePub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.a0, .a1, .a2, .a3], s₁.gpr r = s₂.gpr r

theorem modes_ofRegs (s₁ s₂ : State) (h : modePub s₁ s₂) :
    taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3]) s₁ s₂ :=
  ⟨h.1, fun r hr => h.2 r (Taint.mem_ofRegs.mp hr)⟩

/-! The constant-time analysis of the batch encryption the modes call, from the modes' state
(`s1`–`s3`) and the frame's base (`s4`), which it leaves public, done once for every check of
code that calls it (`taint_decide_sum [cryptSum, prepareSum]`). -/
taint_summary cryptSum : taint (Taint.ofRegs [.s1, .s2, .s3, .s4]) coreCrypt

/-! The same of the preparation of the round keys in encryption's order, from the schedule's
address (`a0`) as well. -/
taint_summary prepareSum : taint (Taint.ofRegs [.a0, .s1, .s2, .s3, .s4]) (corePrepare .encrypt)

theorem cbcEncryptChained_constantTime (pre : State → Prop) :
    ConstantTime isa pre modePub cbcEncryptChained :=
  VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide_sum [cryptSum, prepareSum])

theorem cbcDecryptChained_constantTime (pre : State → Prop) :
    ConstantTime isa pre modePub cbcDecryptChained :=
  VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide_sum [cryptSum, prepareSum])

theorem ofb_constantTime (pre : State → Prop) : ConstantTime isa pre modePub ofb :=
  VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide_sum [cryptSum, prepareSum])

theorem cfbEncrypt_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbEncrypt :=
  VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide_sum [cryptSum, prepareSum])

theorem cfbDecrypt_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbDecrypt :=
  VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide_sum [cryptSum, prepareSum])

theorem ctr_constantTime (pre : State → Prop) : ConstantTime isa pre modePub ctr :=
  VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide_sum [cryptSum, prepareSum])

theorem ctr32_constantTime (pre : State → Prop) : ConstantTime isa pre modePub ctr32 :=
  VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide_sum [cryptSum, prepareSum])

end VG.Proof.Sm4.RISCV64
