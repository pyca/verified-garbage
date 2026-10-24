module

public import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
public import VerifiedGarbage.Impl.Cast5.PPC64LE.Modes
import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesLit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Impl.Cast5.PPC64LE.Modes
meta import VerifiedGarbage.Proof.Framework.RegSet

/-!
# Constant-time CAST5 modes on PPC64LE

Only the pointers, `rounds` and the count (`r3`–`r8`) and the table's
address are public (`taintSym`). The core keeps the modes' `r29` and `r30`
in `r6` and `r7` while the block function runs, which never writes them,
nor `r3` (the schedule), `r4` (the count of rounds), `sb` or `r31`.
-/

@[expose] public section

namespace VG.Proof.Cast5.PPC64LE

open VG VG.PPC64LE VG.Impl.Cast5.PPC64LE
open VG.Impl.Cast5 (s1234Sym)

/-- The modes' public arguments: the stack pointer, `r3`–`r8` and the table's address. -/
def modePub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ (∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8], s₁.gpr r = s₂.gpr r) ∧
    s₁.syms s1234Sym = s₂.syms s1234Sym

theorem modes_agree (s₁ s₂ : State) (h : modePub s₁ s₂) :
    (taintSym [s1234Sym]).Agree (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8]) s₁ s₂ :=
  ⟨⟨h.1, fun r hr => h.2.1 r (Taint.mem_ofRegs.mp hr)⟩, fun n hn => by
    simp only [List.mem_singleton] at hn; subst hn; exact h.2.2⟩

theorem cbcEncryptChained_constantTime (pre : State → Prop) :
    ConstantTime isa pre modePub cbcEncryptChained :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8])
    (fun _ _ _ _ hp => modes_agree _ _ hp) (by taint_decide)

theorem cbcDecryptChained_constantTime (pre : State → Prop) :
    ConstantTime isa pre modePub cbcDecryptChained :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8])
    (fun _ _ _ _ hp => modes_agree _ _ hp) (by taint_decide)

theorem ofb_constantTime (pre : State → Prop) : ConstantTime isa pre modePub ofb :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8])
    (fun _ _ _ _ hp => modes_agree _ _ hp) (by taint_decide)

theorem cfbEncrypt_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbEncrypt :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8])
    (fun _ _ _ _ hp => modes_agree _ _ hp) (by taint_decide)

theorem cfbDecrypt_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbDecrypt :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8])
    (fun _ _ _ _ hp => modes_agree _ _ hp) (by taint_decide)

end VG.Proof.Cast5.PPC64LE
