module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Exponent
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentClear
import VerifiedGarbage.Proof.RsaKeyGen.X86.HalfPassLoop
import VerifiedGarbage.Proof.Mont.X86.Instr
public import Init.Prelude
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # The first native pass copies c/2 into the exponent and retains its zero sentinel -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Exponent
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Exponent

def firstRanges (n src out : Nat) : List (Nat × Nat) :=
  [(src + 4 * n, 4), (out + 4 * n, 4), (out, 4 * n)]

theorem firstPass_ok {s : State} {base : Addr} {size n src out : Nat} (scratch : Scr s base size)
    (positive : 0 < n) (srcFit : src + 4 * (n + 1) ≤ size) (outFit : out + 4 * (n + 1) ≤ size)
    (sep : src + 4 * (n + 1) ≤ out) :
    WP isa (firstPass n src out) s fun t =>
      val32 t.mem base out n = val32 s.mem base src n / 2 ∧ w32 t.mem base (out + 4 * n) = 0 ∧
      Outs base (firstRanges n src out) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.seq (WP.mono (clearTops_ok scratch srcFit outFit sep) fun a ⟨srcTop, outTop, mask, Oa, Ka⟩ => ?_)
  refine WP.mono (HalfPass.code_ok (scratch.of_keeps Ka (by decide)) positive srcFit (by omega)
    (Or.inr (Or.inl sep)) srcTop mask) fun t ⟨Ot, V, Kt⟩ => ?_
  have before : val32 a.mem base src n = val32 s.mem base src n :=
    Oa.val32 (fun r mem => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl <;> left <;> omega) (by have := scratch.nowrap; omega)
  refine ⟨by rw [before] at V; exact V, ?_, ?_, (Ka.mono (by decide)).widen Kt⟩
  · rw [Ot.w32 (Or.inr (Nat.le_refl _)) (by have := scratch.nowrap; omega)]
    exact outTop
  · exact (Oa.mono (fun r mem => by
      simp only [firstRanges, List.mem_cons, List.not_mem_nil, or_false] at mem ⊢
      rcases mem with rfl | rfl <;> simp)).trans
      (Outs.of_outside Ot (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))

end VG.Proof.RsaKeyGen.X86.Exponent
