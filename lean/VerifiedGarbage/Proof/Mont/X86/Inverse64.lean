module

public import VerifiedGarbage.Impl.Mont.X86.Inverse64
public import VerifiedGarbage.Proof.Mont.Inverse64
public import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # The native high-word inverse reuses the existing 32-bit inverse -/

@[expose] public section
namespace VG.Proof.Mont.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Impl.Mont.X86

theorem extend_inverse {s : State} {c0 c1 u : BitVec 32}
    (lo : s.gpr .eax = c0) (hi : s.gpr .ebx = c1) (inv : s.gpr .ecx = u)
    (inverse : (c0.toNat * u.toNat + 1) % 2 ^ 32 = 0) :
    WP isa (.block extendInverse) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (inverseHigh c0.toNat c1.toNat u.toNat) ∧
      t.mem = s.mem ∧ Keeps [.eax, .edx, .ebp] s t := by
  unfold extendInverse
  refine wp_mul fun s₁ M₁ => wp_addS rfl fun s₂ U₂ _ => wp_movS rfl fun s₃ U₃ _ =>
    wp_movS rfl fun s₄ U₄ _ => wp_mul fun s₅ M₅ => wp_addS rfl fun s₆ U₆ _ =>
    wp_mul fun t M₇ => WP.block_nil ?_
  have K : Keeps [.eax, .edx, .ebp] s t :=
    ((((((M₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans
      (U₃.keeps.mono (by decide))).trans (U₄.keeps.mono (by decide))).trans
      (M₅.keeps.mono (by decide))).trans (U₆.keeps.mono (by decide))).trans (M₇.keeps.mono (by decide))
  have ecx₄ : s₄.gpr .ecx = u := by rw [U₄.other .ecx (by decide), U₃.other .ecx (by decide),
    U₂.other .ecx (by decide), M₁.other .ecx (by decide) (by decide), inv]
  have carry : s₃.gpr .ebp = BitVec.ofNat 32 ((c0.toNat * u.toNat + 1) / 2 ^ 32) := by
    rw [U₃.gpr, U₂.gpr, M₁.edx, lo, inv]
    change BitVec.ofNat 32 (c0.toNat * u.toNat / 2 ^ 32) + BitVec.ofNat 32 1 = _
    rw [← BitVec.ofNat_add, inverse_carry inverse]
  have c1₄ : s₄.gpr .eax = c1 := by rw [U₄.gpr, U₃.other .ebx (by decide), U₂.other .ebx (by decide),
    M₁.other .ebx (by decide) (by decide), hi]
  have kBound : (c0.toNat * u.toNat + 1) / 2 ^ 32 < 2 ^ 32 := by
    rw [inverse_carry inverse]
    exact inverse_carry_bound c0.isLt u.isLt
  refine ⟨?_, by rw [M₇.mem, U₆.mem, M₅.mem, U₄.mem, U₃.mem, U₂.mem, M₁.mem], K⟩
  rw [M₇.eax, U₆.gpr, M₅.eax, c1₄, ecx₄,
    M₅.other .ebp (by decide) (by decide), U₄.other .ebp (by decide), carry,
    U₆.other .ecx (by decide), M₅.other .ecx (by decide) (by decide), ecx₄]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_add, Nat.mod_eq_of_lt kBound, inverseHigh]
  rw [Nat.mod_add_mod, Nat.mod_mod, Nat.mod_mul_mod]
  congr 1
  ac_rfl

end VG.Proof.Mont.X86
