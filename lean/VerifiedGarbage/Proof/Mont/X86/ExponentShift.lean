module
public import VerifiedGarbage.Impl.Mont.X86.Exponent
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words

import VerifiedGarbage.Proof.Mont.X86.ExponentWord
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.TCB.X86.State

/-! # The complete little-endian exponent shift -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont
open VG.Proof.Mont.X86

theorem val32_parity (m : Mem) (base : Addr) (out n : Nat) :
    val32 m base out (n + 1) % 2 = w32 m base out % 2 := by
  rw [val32]
  omega_using []

theorem shiftExponent_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) :
    ∀ n out, out + 4 * n ≤ size →
    WP isa (.block (VG.Impl.Mont.X86.Dynamic.shiftExponent n out)) s fun t =>
      Outside base out (4 * n) s.mem t.mem ∧
      val32 t.mem base out n = val32 s.mem base out n / 2 ∧
      Keeps [.eax, .edx] s t
  | 0, out, _ => WP.block_nil ⟨Outside.refl _ _ _ _, by simp only [val32, Nat.zero_div], Keeps.refl _ _⟩
  | n + 1, out, ho => by
    rw [VG.Impl.Mont.X86.Dynamic.shiftExponent]
    have hnext : (n == 0) = false → out + 8 ≤ size := by
      intro h
      have hn : n ≠ 0 := by intro e; subst n; contradiction
      omega_using [ho, hn]
    refine WP.block_append (WP.mono (shiftWord_ok hs (n == 0) (by omega_using [ho]) hnext)
      fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
    have hs₁ := hs.of_keeps K₁ (by decide)
    refine WP.mono (shiftExponent_ok hs₁ n (out + 4) (by omega_using [ho])) fun t ⟨O₂, V₂, K₂⟩ => ?_
    have hn := hs.nowrap
    refine ⟨(O₁.mono (o' := out) (n' := 4 * (n + 1)) (by omega_using []) (by omega_using [])).trans
      (O₂.mono (o' := out) (n' := 4 * (n + 1)) (by omega_using []) (by omega_using [])), ?_, K₁.trans K₂⟩
    have tail := O₁.val32 (d := out + 4) (k := n) (by omega_using []) (by omega_using [ho, hn])
    have head := O₂.w32 (d := out) (by omega_using []) (by omega_using [ho, hn])
    rw [val32, val32, head, V₁, V₂, tail]
    cases n with
    | zero => simp only [beq_self_eq_true, ite_true, val32]; omega_using []
    | succ n =>
      have hp := val32_parity s.mem base (out + 4) n
      simp only [show (n + 1 == 0) = false from by simp, Bool.false_eq_true, ite_false]
      omega_using [hp]

end VG.Proof.Mont.X86.Dynamic
