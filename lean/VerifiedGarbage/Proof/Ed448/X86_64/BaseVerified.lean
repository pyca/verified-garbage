module

import VerifiedGarbage.Proof.Ed448.X86_64.BaseMain
public import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.Proof.Ed448.X86_64.BaseLocal
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import Mathlib.Tactic.NormNum.Prime
import VerifiedGarbage.Proof.Ed448.X86_64.BaseLit
public import VerifiedGarbage.Impl.Ed448.X86_64.ScalarBase
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ed448.X86_64.BaseMain
meta import VerifiedGarbage.Proof.Ed448.Ref
meta import VerifiedGarbage.Proof.Ed448.X86_64.BaseLocal
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import Mathlib.Tactic.NormNum.Prime
meta import VerifiedGarbage.Proof.Ed448.X86_64.BaseLit
meta import VerifiedGarbage.Impl.Ed448.X86_64.ScalarBase
meta import Mathlib.Data.Nat.Totient
meta import Mathlib.Tactic.Positivity.Finset
meta import Mathlib.Algebra.Order.Field.Basic
meta import Mathlib.Tactic.NormNum.GCD
meta import Mathlib.Data.Sym.Sym2.Init
meta import Mathlib.Tactic.ContinuousFunctionalCalculus
meta import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Spec.Ed448.Contract

/-!
# Ed448 base-point multiplication on x86-64: the pieces of `Verified`

The taint domain of the code (`scalarBaseτ`), in which the arguments of two
states the contract calls public agree (`scalarBase_agree`), so that the code
is constant time (`scalarBase_ct0`); a concrete state satisfying the
signature's contract (`scalarBaseSat`); and that the output is apart from the
call's return address (`scalarBase_patch`).
-/

@[expose] public section

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64

def scalarBaseSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 57⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x3000, 8192⟩]

/-- The arguments are public, and so is what the code stores in the working
space (writable region 1, at `rdx`): the output's address, at `OUT`. -/
def scalarBaseτ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rsp], flags := false, lens := [0, 8192], bases := [(.rdx, 1, 0)] }

theorem scalarBase_agree {s₁ s₂ : State} (h₁ : scalarBaseLocal.pre s₁)
    (h₂ : scalarBaseLocal.pre s₂) (hpub : scalarBaseLocal.pub s₁ s₂) :
    X86_64.Taint.Agree scalarBaseτ s₁ s₂ := by
  obtain ⟨p0, p1, p2, p3⟩ := hpub
  have wf : ∀ s, scalarBaseLocal.pre s → X86_64.Taint.Wf scalarBaseτ s := by
    intro s hs
    obtain ⟨-, hw, -, -, -, d, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, scalarBaseτ], by simp [hw, d], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [scalarBaseτ, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp; simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo, X86_64.Taint.noXr⟩
  · simp only [scalarBaseτ, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p1, p3]
  · intro sl h; simp [scalarBaseτ] at h
  · intro sl h; simp [scalarBaseτ] at h

/-- The output is apart from the call's return address. -/
theorem scalarBase_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64) (hs : scalarBaseLocal.pre s)
    (hcl : Clear (hole (s.gpr .rsp)) s) (hp : scalarBaseLocal.post s b) :
    scalarBaseLocal.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hw, -⟩ := hs
  have hb := Clear.wr_bytes hcl (p := s.gpr .rdi) (n := 57) (by rw [hw]; simp) (by decide)
  show Spec.Ed448.bytesAt (b.patch _ hv u).mem (s.gpr .rdi) 57 = _
  rw [show Spec.Ed448.bytesAt (b.patch _ hv u).mem (s.gpr .rdi) 57 = Spec.Ed448.bytesAt b.mem (s.gpr .rdi) 57
    from bytes_patch hb]
  exact hp

theorem scalarBase_ct0 : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase := by
  refine VG.Taint.constantTime (A := taint) scalarBaseτ
    (fun _ _ h₁ h₂ hp => scalarBase_agree h₁ h₂ hp) (by taint_decide)

end VG.Proof.Ed448.X86_64
