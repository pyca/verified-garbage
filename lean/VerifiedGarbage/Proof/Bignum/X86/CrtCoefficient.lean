module

public import VerifiedGarbage.Impl.Bignum.X86.CrtCoefficient
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
import VerifiedGarbage.Proof.Bignum.X86.ReduceOperand
import VerifiedGarbage.Proof.Bignum.X86.ContextSub
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Mont.X86.ExponentInitMath
import VerifiedGarbage.Proof.Mont.X86.ContextMul
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame

/-! # Correct reduced CRT coefficient after full-width residue reduction -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic

def coefficientRanges (n : Nat) : List (Nat × Nat) :=
  [(slot n 5, 8 * n), (slot n 7, 8 * n), (slot n 8, 8 * n),
    (slot n 1, 8 * n), (slot n 2, 16 * n + 4)]

theorem coefficient_op {n o : Nat} {base : Addr} {s t : State}
    (K : OpKeep (contextMod n) base (slot n 2) (slot n o) s t) (ho : o = 5 ∨ o = 7 ∨ o = 8) :
    Outs base (coefficientRanges n) s.mem t.mem := by
  refine K.mem.mono ?_
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rcases ho with rfl | rfl | rfl <;> simp [coefficientRanges, contextMod]
  · simp [coefficientRanges, contextMod]
  · rw [context_accLen]; simp [coefficientRanges]

theorem crtCoefficient_ok {s : State} {base : Addr} {bytes n m : Nat}
    (H : Context n m base bytes s)
    (A : wordsVal s.mem base (slot n 6) n < m)
    (one : wordsVal s.mem base (slot n 3) n = 1)
    (r2 : wordsVal s.mem base (slot n 4) n = 2 ^ (128 * n) % m) :
    WP isa (crtCoefficient n) s fun t =>
      Context n m base bytes t ∧
      wordsVal t.mem base (slot n 7) n =
        ((wordsVal s.mem base (slot n 6) n + m - wordsVal s.mem base (slot n 5) n % m) % m *
          wordsVal s.mem base (slot n 8) n) % m ∧
      Outs base (coefficientRanges n) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have positive : 0 < m := by have := H.gt_one; omega
  unfold crtCoefficient
  refine WP.seq (WP.mono (reduceOperand_ok H (.inl rfl) one r2) fun u ⟨C, B, O, K⟩ => ?_)
  have Ku : OpKeep (contextMod n) base (slot n 2) (slot n 5) s u := by
    apply OpKeep.of K (by decide)
    rw [context_accLen]
    exact O
  have Au := context_slot_val H (i := 6) (by decide) (by decide) (by decide) (by decide) Ku
  have Ru := context_slot_val H (i := 4) (by decide) (by decide) (by decide) (by decide) Ku
  have Iu := context_slot_val H (i := 8) (by decide) (by decide) (by decide) (by decide) Ku
  refine WP.seq (WP.mono (contextSub_ok C (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [Au]; exact A) (by rw [B]; exact Nat.mod_lt _ positive)) fun v ⟨Cv, Kv, D⟩ => ?_)
  have Rv : wordsVal v.mem base (slot n 4) n = 2 ^ (128 * n) % m := by
    rw [context_slot_val C (by decide) (by decide) (by decide) (by decide) Kv, Ru, r2]
  have Iv := context_slot_val C (i := 8) (by decide) (by decide) (by decide) (by decide) Kv
  refine WP.seq (WP.mono (context_mul_ok Cv (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [Rv]; exact Nat.mod_lt _ positive)) fun w ⟨Cw, Kw, Lw, Vw⟩ => ?_)
  have Encoded : wordsVal w.mem base (slot n 8) n =
      wordsVal s.mem base (slot n 8) n * 2 ^ (64 * n) % m :=
    mont_encode H.coprime Lw (by rw [Vw, Rv, Iv, Iu])
  have Dw := context_slot_val Cv (i := 7) (by decide) (by decide) (by decide) (by decide) Kw
  refine WP.mono (context_mul_ok Cw (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) Lw) fun t ⟨Ct, Kt, Lt, Vt⟩ => ?_
  refine ⟨Ct, ?_, ((coefficient_op Ku (.inl rfl)).trans (coefficient_op Kv (.inr (.inl rfl)))).trans
    ((coefficient_op Kw (.inr (.inr rfl))).trans (coefficient_op Kt (.inr (.inl rfl)))),
    ((K.trans (OpKeep.keeps Kv)).trans (OpKeep.keeps Kw)).trans (OpKeep.keeps Kt)⟩
  have Eq : wordsVal t.mem base (slot n 7) n * 2 ^ (64 * n) % m =
      (wordsVal v.mem base (slot n 7) n * wordsVal s.mem base (slot n 8) n) * 2 ^ (64 * n) % m := by
    rw [Vt, Encoded, Dw, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  have Cancel := VG.Proof.Bignum.mont_cancel H.coprime Eq
  rw [Nat.mod_eq_of_lt Lt, D, Au, B] at Cancel
  exact Cancel

end VG.Proof.Bignum.X86
