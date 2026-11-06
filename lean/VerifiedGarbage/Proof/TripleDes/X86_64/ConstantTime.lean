module

public import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
import VerifiedGarbage.Proof.TripleDes.X86_64.FunctionsLit
public import VerifiedGarbage.Impl.TripleDes.X86_64.Block
public import VerifiedGarbage.Impl.TripleDes.X86_64.ExpandKey
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
meta import VerifiedGarbage.Proof.TripleDes.X86_64.FunctionsLit
meta import VerifiedGarbage.Impl.TripleDes.X86_64.Block
meta import VerifiedGarbage.Impl.TripleDes.X86_64.ExpandKey
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.Impl.TripleDes.X86_64

def PublicRegs (rs : List Reg) (s₁ s₂ : State) : Prop :=
  ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

/-- What the rounds need public: the pointers, the round counter, the key
step, the passes left and the saved pointers in the scratch buffer. -/
def roundTaint : X86_64.Taint.T :=
  { regs := .ofList [.rax, .rdx, .rsi, .rdi], flags := false,
    lens := [0, 512], bases := [(.rdx, 1, 0)],
    slots := [(1, 456, 8), (1, 448, 8), (1, 56, 8), (1, 48, 8)] }

/-! The block functions' round, analysed once, as a summary. -/

taint_summary round : taintS roundTaint (.block (roundBody ++ roundAdvance))

theorem expandKey_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.rdi, .rsi, .rdx, .rcx]) Key.expandKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp

end VG.Proof.TripleDes.X86_64
