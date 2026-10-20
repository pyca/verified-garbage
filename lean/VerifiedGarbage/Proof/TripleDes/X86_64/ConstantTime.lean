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

def blockTaint : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx], flags := false,
    lens := [0, 512], bases := [(.rdx, 1, 0)] }

/-- What the rounds need public: the pointers, the round counter, the key
step, the passes left and the saved pointers in the scratch buffer. -/
def roundTaint : X86_64.Taint.T :=
  { regs := .ofList [.rax, .rdx, .rsi, .rdi], flags := false,
    lens := [0, 512], bases := [(.rdx, 1, 0)],
    slots := [(1, 456, 8), (1, 448, 8), (1, 56, 8), (1, 48, 8)] }

/-! The block functions' round, analysed once, as a summary. -/

taint_summary round : taintS roundTaint (.block (roundBody ++ roundAdvance))

theorem encryptBlock_taint : ∃ h, (taintS.check blockTaint encryptBlock h).isSome = true := by
  taint_decide_sum [round]

theorem decryptBlock_taint : ∃ h, (taintS.check blockTaint decryptBlock h).isSome = true := by
  taint_decide_sum [round]

theorem encryptBlock_constantTime (pre : State → Prop) (pub : State → State → Prop)
    (hagree : ∀ s t, pre s → pre t → pub s t → X86_64.Taint.Agree blockTaint s t) :
    ConstantTime isa pre pub encryptBlock :=
  let ⟨_, h⟩ := encryptBlock_taint
  VG.Taint.constantTime (A := taintS) blockTaint hagree h

theorem decryptBlock_constantTime (pre : State → Prop) (pub : State → State → Prop)
    (hagree : ∀ s t, pre s → pre t → pub s t → X86_64.Taint.Agree blockTaint s t) :
    ConstantTime isa pre pub decryptBlock :=
  let ⟨_, h⟩ := decryptBlock_taint
  VG.Taint.constantTime (A := taintS) blockTaint hagree h

theorem expandKey_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.rdi, .rsi, .rdx, .rcx]) Key.expandKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp

end VG.Proof.TripleDes.X86_64
