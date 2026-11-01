module

import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.XorSplitFn
public import VerifiedGarbage.Proof.ChaCha20.Contract
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.XorSplit
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.LitSplit
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.XorSplitFn
meta import VerifiedGarbage.Proof.ChaCha20.Contract
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.XorSplit
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.LitSplit
meta import VerifiedGarbage.Proof.Aes.KeyExp
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_chacha20_xor_split_avx512` verified

Correctness (`XorSplitFn.lean`), constant time and the calling convention.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx512Split

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512

theorem xorSplit_correct (s : State) (hs : xorSplitX86_64.pre s) :
    ∃ t s', Exec isa xorSplit s t s' ∧ abiPreserved s s' ∧ xorSplitX86_64.post s s' := by
  obtain ⟨t, s', he, h, hpost⟩ := correct (APre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h, hpost⟩

/-- The public registers on entry, and the writable regions: the state,
the output and `buf`. -/
def τ₀ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], flags := false, lens := [64, 0, 320],
    bases := [(.rdi, 0, 0), (.rcx, 1, 0), (.r9, 2, 0)] }

theorem agree₀ {s₁ s₂ : State} (h₁ : xorSplitX86_64.pre s₁) (h₂ : xorSplitX86_64.pre s₂)
    (hpub : xorSplitX86_64.pub s₁ s₂) : X86_64.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hpub
  have wf : ∀ s, xorSplitX86_64.pre s → X86_64.Taint.Wf τ₀ s := by
    intro s hs
    obtain ⟨-, hw, -, d1, d2, d3, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, τ₀], by simp [hw, d1, d2, d3], by simp [hw, Nat.le_of_lt (s.gpr .r8).isLt]⟩,
      fun p hp => ?_⟩
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo, X86_64.Taint.noXr⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [h₁.2.1, h₂.2.1, p1, p4, p5, p6]
  · intro sl h; simp [τ₀] at h
  · intro sl h; simp [τ₀] at h

theorem xorSplit_ct : ConstantTime isa xorSplitX86_64.pre xorSplitX86_64.pub xorSplit :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)

/-- A state satisfying the precondition (with no data). -/
def sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rcx => 0x3000 | .r9 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x3000, 0⟩, ⟨0x4000, 320⟩]

theorem xorSplit_verified :
    Verified X86_64.target xorSplit (Proof.ChaCha20.xorSplitContract X86_64.abi 24) :=
  Verified.of_correct xorSplit_correct xorSplit_ct
    (by sig_implies [Proof.ChaCha20.xorSplitContract, Proof.ChaCha20.xorSplitSig, Proof.ChaCha20.xorSplitPre,
      X86_64.abi, X86_64.argRegs, Proof.ChaCha20.xorSplitX86_64]
      [sat] using sat)

end VG.Proof.ChaCha20.X86_64.Avx512Split
