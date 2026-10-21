module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64Word
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64WordMath
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # A fixed native word reduces as one radix-2³² digit -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Mod64

structure WordState (s₀ : State) (base : Addr) (exponent i : Nat) (s : State) : Prop where
  value : pair (s.gpr .ecx) (s.gpr .ebx) =
    (pair (s₀.gpr .ecx) (s₀.gpr .ebx) * 2 ^ i + consumed (s₀.gpr .esi).toNat i) % exponentValue s₀.mem base exponent
  bound : pair (s.gpr .ecx) (s.gpr .ebx) < exponentValue s₀.mem base exponent
  wordValue : (s.gpr .esi).toNat = shifted (s₀.gpr .esi).toNat i
  memory : s.mem = s₀.mem
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s₀ s

theorem steps_ok {s : State} {base : Addr} {size exponent : Nat}
    (scratch : Scr s base size) (fit : exponent + 8 ≤ size)
    (remainder : pair (s.gpr .ecx) (s.gpr .ebx) < exponentValue s.mem base exponent)
    (count : Nat) (limit : count ≤ 32) :
    WP isa (.block (steps exponent count)) s (WordState s base exponent count) := by
  induction count with
  | zero =>
    refine WP.block_nil ⟨?_, remainder, ?_, rfl, Keeps.refl _ _⟩
    · simp only [Nat.pow_zero, Nat.mul_one, consumed, Nat.sub_zero,
        Nat.div_eq_of_lt (s.gpr .esi).isLt, Nat.add_zero, Nat.mod_eq_of_lt remainder]
    · simp only [shifted, Nat.sub_zero, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt (s.gpr .esi).isLt]
  | succ i ih =>
    unfold steps
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.block_append (WP.mono (ih (by omega)) fun t T => ?_)
    have math := word_step (s.gpr .esi).toNat i (by omega) (t.gpr .esi) T.wordValue
    refine WP.mono (bit_ok (scratch.of_keeps T.keeps (by decide)) fit
      (by rw [T.memory]; exact T.bound)) fun u ⟨value, bound, shiftedWord, mem, keep⟩ => ?_
    rw [T.memory, T.value] at value
    refine ⟨value.trans (consumed_mod_step _ _ _ _ _ math.2), ?_, ?_, mem.trans T.memory, T.keeps.trans keep⟩
    · rw [T.memory] at bound
      exact bound
    · rw [shiftedWord]
      exact math.1

theorem word_ok {s : State} {base : Addr} {size exponent : Nat}
    (scratch : Scr s base size) (fit : exponent + 8 ≤ size)
    (remainder : pair (s.gpr .ecx) (s.gpr .ebx) < exponentValue s.mem base exponent) :
    WP isa (.block (VG.Impl.RsaKeyGen.X86.Mod64.word exponent)) s fun t =>
      pair (t.gpr .ecx) (t.gpr .ebx) =
        (pair (s.gpr .ecx) (s.gpr .ebx) * 2 ^ 32 + (s.gpr .esi).toNat) % exponentValue s.mem base exponent ∧
      pair (t.gpr .ecx) (t.gpr .ebx) < exponentValue s.mem base exponent ∧
      t.gpr .esi = 0#32 ∧ t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.mono (steps_ok scratch fit remainder 32 (by decide)) fun t T => ?_
  refine ⟨?_, T.bound, ?_, T.memory, T.keeps⟩
  · simpa only [consumed, Nat.sub_self, Nat.pow_zero, Nat.div_one] using T.value
  · apply BitVec.eq_of_toNat_eq
    change (t.gpr .esi).toNat = 0
    simpa only [shifted, Nat.sub_self, Nat.pow_zero, Nat.mod_one, Nat.zero_mul] using T.wordValue

end VG.Proof.RsaKeyGen.X86.Mod64
