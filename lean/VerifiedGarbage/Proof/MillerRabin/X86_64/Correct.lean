module
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Impl.MillerRabin.X86_64.Round
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Table

import VerifiedGarbage.Proof.MillerRabin.X86_64.CorrectMath
import VerifiedGarbage.Proof.Framework.Offset

/-! # The inlined prepared round preserves its full calling convention -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Impl.MillerRabin.X86_64 VG.Proof.Bignum.X86_64

theorem round_correct (M : Mont) (hload : ∀ i ∈ instrs (round M.mm), loadsMxcsr i = false)
    (s : State) (h : roundPre s) :
    ∃ tr t, Exec isa (round M.mm) s tr t ∧ abiPreserved s t ∧ roundPost s t := by
  obtain ⟨tr, t, he, hregs, hp, hf⟩ := round_math_ok M h
  refine ⟨tr, t, he, ⟨hregs, ?_, ?_⟩, hp⟩
  · apply hf.readW (r := ⟨s.gpr .rsp, 8⟩)
    · simp only [Region.Contains, BitVec.sub_self]
      decide
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · have ha : s.gpr .rsp = (s.gpr .rsp - 112#64) + 112#64 := by bv_omega
        conv_lhs => rw [ha]
        exact Offset.disjoint_base (s.gpr .rsp - 112#64) (by decide : 112 ≤ 112) (by decide : 112 + 8 ≤ 2 ^ 64)
      · exact h.2.2.2.2.1
    · decide
  · rw [VG.X86_64.Exec.mxcsr hload he]

end VG.Proof.MillerRabin.X86_64
