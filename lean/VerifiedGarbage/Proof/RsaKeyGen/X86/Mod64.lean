module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64Shift
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64Subtract
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64Select
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64Math
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # A native paired-word bit reduction computes exactly the modular recurrence -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Mod64

def exponentValue (m : Mem) (base : Addr) (offset : Nat) : Nat :=
  pair (m.readW (off base offset) 32) (m.readW (off base (offset + 4)) 32)

theorem bit_ok {s : State} {base : Addr} {size exponent : Nat}
    (scratch : Scr s base size) (fit : exponent + 8 ≤ size)
    (remainder : pair (s.gpr .ecx) (s.gpr .ebx) < exponentValue s.mem base exponent) :
    WP isa (.block (bit exponent)) s fun t =>
      pair (t.gpr .ecx) (t.gpr .ebx) =
        (2 * pair (s.gpr .ecx) (s.gpr .ebx) + (incoming (s.gpr .esi)).toNat) % exponentValue s.mem base exponent ∧
      pair (t.gpr .ecx) (t.gpr .ebx) < exponentValue s.mem base exponent ∧
      t.gpr .esi = s.gpr .esi + s.gpr .esi ∧ t.mem = s.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold bit
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (shift_ok s) fun u ⟨shiftedWord, ⟨carry, mask, sum⟩, Mu, Ku⟩ => ?_)
  refine WP.block_append (WP.mono (subtract_ok (scratch.of_keeps Ku (by decide)) fit)
    fun v ⟨⟨borrow, choiceMask, sub⟩, Mv, Kv⟩ => ?_)
  rw [Mu] at sub
  have exponentBound : exponentValue s.mem base exponent < 2 ^ 64 := pair_lt ..
  have sumBound : pair (u.gpr .ecx) (u.gpr .ebx) + 2 ^ 64 * carry.toNat < 2 * exponentValue s.mem base exponent := by
    have := Bool.toNat_le (incoming (s.gpr .esi))
    omega
  have cb : carry.toNat ≤ borrow.toNat := carry_le_borrow exponentBound sumBound sub
  have chosen : v.gpr .ebp = if choose carry borrow then BitVec.allOnes 32 else 0 := by
    rw [choiceMask, mask]
    exact mask_value carry borrow cb
  refine WP.mono (select_ok v (choose carry borrow) chosen) fun t ⟨low, high, Mt, Kt⟩ => ?_
  have original : pair (v.gpr .ecx) (v.gpr .ebx) = pair (u.gpr .ecx) (u.gpr .ebx) := by
    rw [Kv.1 .ecx (by decide), Kv.1 .ebx (by decide)]
  have selected : pair (t.gpr .ecx) (t.gpr .ebx) =
      if choose carry borrow then pair (v.gpr .eax) (v.gpr .edx) else pair (u.gpr .ecx) (u.gpr .ebx) := by
    cases C : choose carry borrow <;> rw [C] at low high <;>
      simp only [Bool.false_eq_true, ↓reduceIte] at low high ⊢
    · rw [low, high, original]
    · rw [low, high]
  have value := selected.trans (selected_value exponentBound (pair_lt ..) (pair_lt ..) sumBound sub)
  rw [sum] at value
  have positive : 0 < exponentValue s.mem base exponent := by omega
  have K : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t :=
    ((Ku.mono (by decide)).widen Kv).widen Kt
  refine ⟨value, ?_, ?_, Mt.trans (Mv.trans Mu), K⟩
  · rw [value]
    exact Nat.mod_lt _ positive
  · rw [Kt.1 .esi (by decide), Kv.1 .esi (by decide), shiftedWord]

end VG.Proof.RsaKeyGen.X86.Mod64
