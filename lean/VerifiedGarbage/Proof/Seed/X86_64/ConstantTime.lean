import VerifiedGarbage.Proof.Seed.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.TaintMono

/-!
# Constant time

The pointers, the count of blocks and the stack pointer are public; so is
everything the functions compute from them (the batches' sizes, the counts
of rounds and lanes, the addresses of the round keys and of the lanes).
-/

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64

/-- Only argument pointers and lengths agree; all memory contents, including
the key, schedule and data, may differ. -/
def PublicRegs (rs : List Reg) (s₁ s₂ : State) : Prop :=
  ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

def ecbTaint : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .rsp], flags := false,
    lens := [0, 8 * Impl.Seed.X86_64.scratchSlots], bases := [(.rcx, 1, 0)] }

theorem encrypt_constantTime (pre : State → Prop) (pub : State → State → Prop)
    (hagree : ∀ s t, pre s → pre t → pub s t → X86_64.Taint.Agree ecbTaint s t) :
    ConstantTime isa pre pub Impl.Seed.X86_64.encrypt :=
  VG.Taint.constantTime (A := taint) ecbTaint hagree (by taint_decide)

theorem decrypt_constantTime (pre : State → Prop) (pub : State → State → Prop)
    (hagree : ∀ s t, pre s → pre t → pub s t → X86_64.Taint.Agree ecbTaint s t) :
    ConstantTime isa pre pub Impl.Seed.X86_64.decrypt :=
  VG.Taint.constantTime (A := taint) ecbTaint hagree (by taint_decide)

theorem expandKey_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.rdi, .rsi, .rdx, .rsp]) Impl.Seed.X86_64.expandKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rsp]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp

end VG.Proof.Seed.X86_64
