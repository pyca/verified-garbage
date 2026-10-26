module

import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentFast
public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentFilter
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Taint
import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack

/-! # The fast public-exponent path reads the saved candidate minus one -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentFilter
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.ExponentFilter

theorem val32_off (m : Mem) (base : Addr) (start d n : Nat) :
    val32 m (off base start) d n = val32 m base (start + d) n := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    simp only [val32, ih, w32, off, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [Nat.add_assoc]

theorem fast_candidate_ok {s : State} {base : Addr} {size w candidate : Nat}
    (S : Scr s base size) (width : 4 ≤ w) (widthBound : w ≤ 64)
    (space : slot w 5 + 8 * w ≤ size)
    (saved : val32 s.mem base (slot w 5) (2 * w) = candidate - 1)
    (fit : 40 ≤ (s.gpr .esp).toNat)
    (separate : (s.gpr .esp).toNat ≤ base.toNat ∨ base.toNat + size + 40 ≤ (s.gpr .esp).toNat) :
    WP isa (fast w) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (decide (Nat.gcd (candidate - 1) 65537 = 1)).toNat ∧
      Frame [below (s.gpr .esp) 20] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  let p := s.gpr .edi + BitVec.ofNat 32 (slot w 5)
  have slotBound : slot w 5 + 8 * w ≤ 2 ^ 32 := Nat.le_trans space (by have := S.nowrap; omega)
  have pbase : p.setWidth 64 = off base (slot w 5) := S.ea (d := slot w 5) (by omega)
  have pnat : p.toNat = base.toNat + slot w 5 := by
    change (s.gpr .edi + BitVec.ofNat 32 (slot w 5)).toNat = base.toNat + slot w 5
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, S.edi_toNat]
    rw [Nat.mod_eq_of_lt (a := slot w 5) (by omega),
      Nat.mod_eq_of_lt (by have := S.nowrap; omega)]
  have far : (⟨base, size⟩ : Region).Disjoint (below (s.gpr .esp) 20) :=
    FilterStack.allocated_apart (by omega) S.nowrap
      (by rcases separate with h | h; exact Or.inl h; exact Or.inr (by omega))
  refine WP.mono (fast_ok (p := p) (by omega) (by omega) (by omega) (by rw [pnat]; have := S.nowrap; omega) rfl
    (by
      intro i index
      rw [pbase]
      simpa only [off, BitVec.add_assoc, ← BitVec.ofNat_add] using S.read (d := slot w 5 + 4 * i) (n := 4) (by omega))
    (by
      apply Region.Disjoint.sub_left far
      intro x hx
      rw [pbase] at hx
      exact Offset.sub_base base space x hx)) fun t ⟨result, F, K⟩ => ?_
  rw [pbase, val32_off, Nat.add_zero, saved] at result
  exact ⟨result, F, K⟩

end VG.Proof.RsaKeyGen.X86.ExponentFilter
