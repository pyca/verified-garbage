module

public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Camellia.RISCV64.Modes
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.Lit
import VerifiedGarbage.Proof.Camellia.RISCV64.ModesLit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Impl.Camellia.RISCV64.Modes
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Camellia.RISCV64.ModesLit

/-!
# Constant-time Camellia modes on RISC-V

Only the pointers, `rounds` and the count (`a0`–`a4`) and the stack pointer
are public; the branch on `rounds` and the loops' tests follow them. The
core keeps the modes' `s1`–`s3` in `a2`, `a3` and `ra` while ECB's key setup
or rounds run, which never write them nor ECB's base in `a5`, from which it
computes `s4` again, so none of them passes through memory. `ra` itself and
`a0` do, and come back secret, but nothing addresses or branches on them
after the key setup.

The eight blocks' encryption (`crypt8`), which every mode's code has for
18 rounds and for 24, in each of its loops, is analysed once, as a summary
(`crypt8Sum`), which the modes' checks use (`taint_decide_sum`) in place of
its analysis in each.
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64

open VG VG.RISCV64 VG.Impl.Camellia.RISCV64

/-- The modes' public arguments: the stack pointer and `a0`–`a4`. -/
def modePub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4], s₁.gpr r = s₂.gpr r

theorem modes_ofRegs (s₁ s₂ : State) (h : modePub s₁ s₂) :
    taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) s₁ s₂ :=
  ⟨h.1, fun r hr => h.2 r (Taint.mem_ofRegs.mp hr)⟩

/-! The constant-time analysis of the eight blocks' encryption, from ECB's base (`a5`) and the
postwhitening's entry (`a4`), done once for every check of code that has it
(`taint_decide_sum [crypt8Sum]`), which keeps what is public of `a2`, `a3` and `ra`, where the
modes' state waits: it writes none of them. -/
taint_summary crypt8Sum : taint (Taint.ofRegs [.a4, .a5]) crypt8
  keeping (Taint.ofRegs [.a2, .a3, .ra])

theorem cbcEncryptChained_constantTime (pre : State → Prop) :
    ConstantTime isa pre modePub cbcEncryptChained :=
  VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide_sum [crypt8Sum])

theorem cbcDecryptChained_constantTime (pre : State → Prop) :
    ConstantTime isa pre modePub cbcDecryptChained :=
  VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide_sum [crypt8Sum])

theorem ofb_constantTime (pre : State → Prop) : ConstantTime isa pre modePub ofb :=
  VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide_sum [crypt8Sum])

theorem cfbEncrypt_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbEncrypt :=
  VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide_sum [crypt8Sum])

theorem cfbDecrypt_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbDecrypt :=
  VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide_sum [crypt8Sum])

theorem ctr_constantTime (pre : State → Prop) : ConstantTime isa pre modePub ctr :=
  VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide_sum [crypt8Sum])

end VG.Proof.Camellia.RISCV64
