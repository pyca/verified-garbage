module

import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.X86.Square.Dispatch
meta import VerifiedGarbage.Proof.Mont.X86.Square.Dispatch
import VerifiedGarbage.Proof.Mont.X86.Square.Time
import VerifiedGarbage.Proof.Mont.X86.Rt.ScalarVerified
meta import VerifiedGarbage.Proof.Mont.X86.Rt.ScalarVerified
meta import VerifiedGarbage.Proof.Rsa.MontMulContract
public import Init.Core
public import VerifiedGarbage.Impl.Mont.X86.MulRt
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Rsa.MontMulContract

/-! The runtime-width Montgomery contract, including the public alias dispatch.

`InputMath` proves symmetry, `ColumnMath` cancellation and carry bounds,
`RowsStep` preserves the polynomial prefix invariant, and `RowsFinal` derives
the result bound and congruence. `Body` connects this to the existing masked
subtraction and ABI; `Dispatch` retains the scalar multiplication proof.
`Time` checks the SSE2 path with the existing ISA taint semantics. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Rsa.MontMul

theorem correct (s : State) (h : (Proof.Rsa.MontMul.mulContract abi 0).pre s) :
    ∃ tr t, Exec isa Impl.Mont.X86.Rt.Square.dispatch s tr t ∧ abiPreserved s t ∧ (Proof.Rsa.MontMul.mulContract abi 0).post s t := by
  have A := rtAbi_of h
  have hso := A.so
  have hol := A.o_le
  have hscr := A.s_le
  have hinv := A.inv
  have hb := A.bLt
  simp only [Apart, scratchBytes] at hso hscr
  rw [numAt_val32, numAt_w32] at hinv
  rw [numAt_val32, numAt_val32] at hb
  obtain ⟨tr, t, E, O, lt, cong, ebx, esi, ebp, edi, esp, -, -⟩ :=
    dispatch_ok A.ws A.args A.vals A.lay (by simp only [nOf]; have := A.pos; omega) A.n32
      (by simp only [nOf, lenOf]; omega) (by simp only [nOf]; omega) hinv hb
  have far : ∀ x, ¬ (⟨wsOf s, lenOf s⟩ : Region).Contains x 1 → t.mem x = s.mem x := fun x hx =>
    O x fun r hr => by
      have := Dynamic.ofs_far hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [nOf, lenOf] at this ⊢ <;> omega
  refine ⟨tr, t, E, ⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · exact Mem.readW_congr fun i hi => far _ fun hc =>
      A.retScratch _ (Offset.contains_base _ (by omega) (by omega)) hc
  · sig_post [Proof.Rsa.MontMul.mulContract, Proof.Rsa.MontMul.sig, abi, argSlots, argVal, argBytes]
    refine ⟨?_, ?_, ?_⟩
    · rw [numAt_val32, numAt_val32]; exact lt
    · rw [numAt_val32, numAt_val32, numAt_val32, numAt_val32,
        show 64 * (arg s 2).toNat = 32 * nOf s by simp only [nOf]; omega]
      exact cong
    · intro i hi hj
      apply O _
      intro r hr
      rw [show ofs (wsOf s) (wsOf s + BitVec.ofNat 64 i) = i by
        simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by omega)]]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have := hj
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, scratchBytes] at this
      rcases hr with rfl | rfl <;> simp only [nOf] <;> omega


theorem verified : Verified target Impl.Mont.X86.Rt.Square.dispatch (Proof.Rsa.MontMul.mulContract abi 0) :=
  ⟨correct,constantTime,rt_satisfiable⟩

end VG.Proof.Mont.X86.Square
