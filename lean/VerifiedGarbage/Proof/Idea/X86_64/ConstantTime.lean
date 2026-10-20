module

import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Idea.X86_64.Lit
public import VerifiedGarbage.Impl.Idea.X86_64
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Idea.X86_64.Lit
meta import VerifiedGarbage.Impl.Idea.X86_64
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Constant-time IDEA programs on x86-64

Only the argument pointers and `n` are public; the key, the subkeys and the
data may differ between runs.
-/

@[expose] public section

namespace VG.Proof.Idea.X86_64

open VG VG.X86_64 VG.Impl.Idea.X86_64

def PublicRegs (rs : List Reg) (s₁ s₂ : State) : Prop :=
  ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

theorem expandKey_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.rdi, .rsi]) expandKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp

theorem invertKey_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.rdi, .rsi]) invertKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp

theorem ecb_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.rdi, .rsi, .rdx, .rcx]) ecb := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp

end VG.Proof.Idea.X86_64
