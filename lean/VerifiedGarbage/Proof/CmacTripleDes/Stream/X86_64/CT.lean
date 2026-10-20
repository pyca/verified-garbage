module

import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Lit
meta import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Lit
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86_64.Contract
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86_64.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.X86_64
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Impl.CmacTripleDes.Stream.X86_64
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

/-!
# Streaming TDEA-CMAC on x86-64: constant time

The taint analysis (`Framework/X86_64/Taint.lean`) checks that only the
arguments, which are public, decide branches and addresses, through the code
of `init`, `update` and `finalize` too. `absorb` knows where the state and
the scratch buffer are, as `update` does, which keeps the data pointer and
the blocks left in public slots of the scratch buffer.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86_64

open VG VG.X86_64

/-- `stream_init`: the arguments are public. The taint knows nothing of the
writable regions: the code never reads a public value back from them. -/
def τInit : X86_64.Taint.T := Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]

/-- `absorb`: the arguments are public; `rdi` and `r8` point at the state
and the scratch buffer. -/
def τAbsorb : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .rsp], flags := false, lens := [416, 688],
    bases := [(.rdi, 0, 0), (.r8, 1, 0)] }

/-- `finish`: the arguments are public; as for `stream_init`, nothing of the
writable regions. -/
def τFinish : X86_64.Taint.T := Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]

theorem init_agree {s₁ s₂ : State} (_ : initX86_64.pre s₁) (_ : initX86_64.pre s₂)
    (hpub : initX86_64.pub s₁ s₂) : X86_64.Taint.Agree τInit s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := hpub
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  exacts [p1, p2, p3, p4, p5]

theorem absorb_agree {s₁ s₂ : State} (h₁ : absorbX86_64.pre s₁) (h₂ : absorbX86_64.pre s₂)
    (hpub : absorbX86_64.pub s₁ s₂) : X86_64.Taint.Agree τAbsorb s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpub
  have wf : ∀ s, absorbX86_64.pre s → X86_64.Taint.Wf τAbsorb s := by
    intro s hs
    obtain ⟨-, hw, -, d2, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, τAbsorb], by simp [hw, d2], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [τAbsorb, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_, X86_64.Taint.noLo,
    X86_64.Taint.noXr⟩
  · simp only [τAbsorb, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [p1, p2, p3, p4, p5, p6]
  · rw [h₁.2.1, h₂.2.1, p1, p5]
  · intro sl h; simp [τAbsorb] at h
  · intro sl h; simp [τAbsorb] at h

theorem finish_agree {s₁ s₂ : State} (_ : finishX86_64.pre s₁) (_ : finishX86_64.pre s₂)
    (hpub : finishX86_64.pub s₁ s₂) : X86_64.Taint.Agree τFinish s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := hpub
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  exacts [p1, p2, p3, p4, p5]

theorem init_ct :
    ConstantTime isa initX86_64.pre initX86_64.pub Impl.CmacTripleDes.Stream.X86_64.streamInit :=
  VG.Taint.constantTime (A := taint) τInit (fun _ _ h₁ h₂ hp => init_agree h₁ h₂ hp) (by taint_decide)

/-- What the second part of `absorb` starts from: the registers the first
part leaves, pinned to the arguments by its correctness proof. -/
def τAbsorb₂ : X86_64.Taint.T :=
  { regs := .ofList [.rbx, .r13, .r14, .r15, .rsp], flags := false, lens := [416, 688],
    bases := [(.rbx, 0, 0), (.r15, 1, 0)] }

theorem absorb₁_taint :
    ∃ h, (taint.check τAbsorb Impl.CmacTripleDes.Stream.X86_64.absorb₁ h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem absorb₂_taint :
    ∃ h, (taint.check τAbsorb₂ Impl.CmacTripleDes.Stream.X86_64.absorb₂ h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem finish_ct :
    ConstantTime isa finishX86_64.pre finishX86_64.pub Impl.CmacTripleDes.Stream.X86_64.finish :=
  VG.Taint.constantTime (A := taint) τFinish (fun _ _ h₁ h₂ hp => finish_agree h₁ h₂ hp) (by taint_decide)

end VG.Proof.CmacTripleDes.Stream.X86_64
