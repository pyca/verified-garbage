module

public import VerifiedGarbage.Impl.Bignum.X86.ReduceOperand
public import VerifiedGarbage.Proof.Mont.X86.ContextMul
public import VerifiedGarbage.Proof.Mont.X86.ContextMath
public import VerifiedGarbage.Proof.Mont.X86.ExponentInitMath

/-! # Two Montgomery products reduce an arbitrary full-width operand -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic

theorem reduceOperand_ok {s : State} {base : Addr} {bytes n m operand : Nat}
    (H : Context n m base bytes s) (o : operand = 5 ∨ operand = 7 ∨ operand = 8)
    (one : wordsVal s.mem base (slot n 3) n = 1)
    (r2 : wordsVal s.mem base (slot n 4) n = 2 ^ (128 * n) % m) :
    WP isa (reduceOperand n operand) s fun t =>
      Context n m base bytes t ∧
      wordsVal t.mem base (slot n operand) n = wordsVal s.mem base (slot n operand) n % m ∧
      Outs base [(slot n operand, 8 * n), (slot n 1, 8 * n), (slot n 2, 16 * n + 4)] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  unfold reduceOperand
  refine WP.seq (WP.mono (context_mul_ok H (by omega) (by omega) (by decide)
    (by omega) (by omega) (by omega) (by omega) (by decide)
    (by rw [r2]; exact Nat.mod_lt _ (by have := H.gt_one; omega)) (by omega))
    fun u ⟨C, K, Lt, V⟩ => ?_)
  have Encoded : wordsVal u.mem base (slot n operand) n =
      wordsVal s.mem base (slot n operand) n * 2 ^ (64 * n) % m :=
    mont_encode H.coprime Lt (by rw [V, r2])
  have One : wordsVal u.mem base (slot n 3) n = 1 := by
    rw [context_slot_val H (by decide) (by omega) (by decide) (by decide) K, one]
  refine WP.mono (context_mul_ok C (by omega) (by omega) (by decide)
    (by omega) (by omega) (by omega) (by omega) (by decide)
    (by rw [One]; exact H.gt_one) (by omega)) fun t ⟨Ct, Kt, Ltt, Vt⟩ => ?_
  have Decoded := VG.Proof.Dsa.mont_decode (A := wordsVal u.mem base (slot n operand) n)
    (out := wordsVal t.mem base (slot n operand) n) H.coprime
    (by rw [Encoded, Nat.mod_mod]) (by rw [Vt, One])
  rw [Nat.mod_eq_of_lt Ltt] at Decoded
  refine ⟨Ct, Decoded, ?_, (OpKeep.keeps K).trans (OpKeep.keeps Kt)⟩
  have Mem := K.mem.trans Kt.mem
  rw [context_accLen] at Mem
  exact Mem

end VG.Proof.Bignum.X86
