module

public import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
public import VerifiedGarbage.Impl.Cast5.RISCV64.Modes
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Cast5.RISCV64.ModesLit
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
meta import VerifiedGarbage.Impl.Cast5.RISCV64.Modes
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Cast5.RISCV64.ModesLit

/-!
# Constant-time CAST5 modes on RISC-V

Only the pointers, `rounds` and the count (`a0`–`a4`), the stack pointer
and the table's address are public (`taintSym`). The core keeps the modes'
`s1`–`s4` in `a3`, `a4`, `s11` and `ra` while the block function runs,
which never writes them, nor `a0` (the schedule).
-/

@[expose] public section

namespace VG.Proof.Cast5.RISCV64

open VG VG.RISCV64 VG.Impl.Cast5.RISCV64
open VG.Impl.Cast5 (s1234Sym)

/-- The modes' public arguments: the stack pointer, `a0`–`a4` and the table's address. -/
def modePub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ (∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4], s₁.gpr r = s₂.gpr r) ∧
    s₁.syms s1234Sym = s₂.syms s1234Sym

theorem modes_agree (s₁ s₂ : State) (h : modePub s₁ s₂) :
    (taintSym [s1234Sym]).Agree (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) s₁ s₂ :=
  ⟨⟨h.1, fun r hr => h.2.1 r (Taint.mem_ofRegs.mp hr)⟩, fun n hn => by
    simp only [List.mem_singleton] at hn; subst hn; exact h.2.2⟩

theorem cbcEncryptChained_constantTime (pre : State → Prop) :
    ConstantTime isa pre modePub cbcEncryptChained :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4])
    (fun _ _ _ _ hp => modes_agree _ _ hp) (by taint_decide)

theorem cbcDecryptChained_constantTime (pre : State → Prop) :
    ConstantTime isa pre modePub cbcDecryptChained :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4])
    (fun _ _ _ _ hp => modes_agree _ _ hp) (by taint_decide)

theorem ofb_constantTime (pre : State → Prop) : ConstantTime isa pre modePub ofb :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4])
    (fun _ _ _ _ hp => modes_agree _ _ hp) (by taint_decide)

theorem cfbEncrypt_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbEncrypt :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4])
    (fun _ _ _ _ hp => modes_agree _ _ hp) (by taint_decide)

theorem cfbDecrypt_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbDecrypt :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4])
    (fun _ _ _ _ hp => modes_agree _ _ hp) (by taint_decide)

end VG.Proof.Cast5.RISCV64
