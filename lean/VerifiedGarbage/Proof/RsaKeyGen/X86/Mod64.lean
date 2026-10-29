module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64Shift
public import VerifiedGarbage.Proof.Mont.X86.Words

import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64Subtract
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.Csub
import VerifiedGarbage.Proof.Bignum.Math
/-! # A native paired-word bit reduction computes exactly the modular recurrence -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/Mod64Select.lean`, which only this module imported.
section

/-! # One mask selects both native words of the reduced remainder -/

section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem select_ok (s : State) (choose : Bool)
    (mask : s.gpr .ebp = if choose then BitVec.allOnes 32 else 0) :
    WP isa (.block select) s fun t =>
      t.gpr .ecx = (if choose then s.gpr .eax else s.gpr .ecx) ∧
      t.gpr .ebx = (if choose then s.gpr .edx else s.gpr .ebx) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx, .ebx] s t := by
  unfold select
  refine wp_xor fun a A => wp_and fun b B => wp_xor fun c C =>
    wp_xor fun d D => wp_and fun e E => wp_xor fun t T => WP.block_nil ?_
  have Kc : Keeps [.eax, .ecx] s c := ((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps
  refine ⟨?_, ?_, ?_, (((Kc.mono (by decide)).widen D.keeps).widen E.keeps).widen T.keeps⟩
  · rw [T.other .ecx (by decide), E.other .ecx (by decide), D.other .ecx (by decide), C.gpr,
      B.other .ecx (by decide), A.other .ecx (by decide), B.gpr, A.gpr,
      A.other .ebp (by decide), mask, select_val]
  · rw [T.gpr, E.other .ebx (by decide), D.other .ebx (by decide), Kc.1 .ebx (by decide),
      E.gpr, D.gpr, Kc.1 .edx (by decide), Kc.1 .ebx (by decide),
      D.other .ebp (by decide), Kc.1 .ebp (by decide), mask, select_val]
  · rw [T.mem, E.mem, D.mem, C.mem, B.mem, A.mem]

end VG.Proof.RsaKeyGen.X86.Mod64
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/Mod64Math.lean`, which only this module imported.
section

/-! # Carry, borrow and masked selection reduce the doubled remainder exactly once -/

section
namespace VG.Proof.RsaKeyGen.X86.Mod64

def choose (carry borrow : Bool) : Bool := decide (borrow.toNat ≤ carry.toNat)

theorem pair_lt (low high : BitVec 32) : pair low high < 2 ^ 64 := by
  unfold pair
  have := low.isLt
  have := high.isLt
  omega

theorem carry_le_borrow {low difference exponent : Nat} {carry borrow : Bool}
    (exponentBound : exponent < 2 ^ 64)
    (sumBound : low + 2 ^ 64 * carry.toNat < 2 * exponent)
    (sub : difference + exponent = low + 2 ^ 64 * borrow.toNat) : carry.toNat ≤ borrow.toNat := by
  cases carry <;> cases borrow <;>
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at * <;> omega

theorem mask_value (carry borrow : Bool) (bound : carry.toNat ≤ borrow.toNat) :
    ((if carry then BitVec.allOnes 32 else 0) + 0#32 + (BitVec.ofBool borrow).setWidth 32) - 1 =
      if choose carry borrow then BitVec.allOnes 32 else 0 := by
  cases carry <;> cases borrow <;> first | rfl | (simp only [Bool.toNat_false, Bool.toNat_true] at bound; omega)

theorem selected_value {low difference exponent : Nat} {carry borrow : Bool}
    (exponentBound : exponent < 2 ^ 64) (differenceBound : difference < 2 ^ 64)
    (lowBound : low < 2 ^ 64) (sumBound : low + 2 ^ 64 * carry.toNat < 2 * exponent)
    (sub : difference + exponent = low + 2 ^ 64 * borrow.toNat) :
    (if choose carry borrow then difference else low) = (low + 2 ^ 64 * carry.toNat) % exponent := by
  have H := VG.Proof.Bignum.csub_result (Tw1 := 0) exponentBound differenceBound (Bool.toNat_le borrow)
    lowBound (by simpa only [Nat.mul_zero, Nat.add_zero] using sumBound) sub
  simp only [Nat.mul_zero, Nat.add_zero] at H
  by_cases accept : borrow.toNat ≤ carry.toNat
  · rw [choose, decide_eq_true accept]
    rw [ite_eq_right (by omega : ¬ carry.toNat < borrow.toNat)] at H
    exact H
  · rw [choose, decide_eq_false accept]
    rw [ite_eq_left (by omega : carry.toNat < borrow.toNat)] at H
    exact H

end VG.Proof.RsaKeyGen.X86.Mod64
end

end

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
