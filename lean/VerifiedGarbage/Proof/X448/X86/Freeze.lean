module
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.X86.Mem

public import VerifiedGarbage.Proof.X448.X86.Env
import VerifiedGarbage.Proof.X448.X86.Small
import VerifiedGarbage.Proof.X448.X86.Columns
import VerifiedGarbage.Proof.X448.X86.Instr
import VerifiedGarbage.Proof.X448.X86.Select
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# X448 on x86 (32-bit): full reduction

The carry out of 448 bits of `x + 1 + 2^224` selects it or the original `x`,
producing the unique representative below the prime.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16
open VG.Proof.X25519.X86 (num num_congr PassRel wp_sbbC)

/-- The mask of the carry flag. -/
theorem freezeMask_ok {s : State} {c : Bool} (hcf : s.cf = some c) :
    WP isa (.block [.alu .sbb .ecx (.reg .ecx)]) s fun t =>
      t.gpr .ecx = mask c ∧ t.mem = s.mem ∧ Keeps [.ecx] s t := by
  refine wp_sbbC (y := s.gpr .ecx) rfl hcf fun u hu _ => WP.block_nil ⟨?_, hu.mem,
    ⟨fun r hr => hu.other r (by simpa using hr), hu.rd, hu.wr⟩⟩
  rw [hu.gpr, BitVec.sub_self]
  cases c <;> rfl

theorem freeze_value {x y : Nat} {c : Bool} (hx : x < full) (hy : y < full)
    (h : x + (half + 1) = y + full * c.toNat) : (if c then y else x) = x % Spec.X448.P := by
  have he := full_eq
  have hp : half + 1 < Spec.X448.P := by decide +kernel
  cases c
  · rw [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at h
    rw [ite_eq_right (by decide), Nat.mod_eq_of_lt (by omega_arith)]
  · rw [Bool.toNat_true, Nat.mul_one] at h
    rw [ite_eq_left rfl, Nat.mod_eq_sub_mod (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith

theorem freeze_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block freeze) s fun t =>
      fe t.mem base X2 = fe s.mem base X2 % Spec.X448.P ∧
      FieldMem base X2 s.mem t.mem ∧ Keeps workRegs s t := by
  have hX : X2 = 192 := rfl
  have hT : TMP = 3840 := rfl
  unfold freeze
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (clearCarry_ok s) fun t₀ ⟨f₀, _, m₀, k₀⟩ => ?_
  have hs₀ := hs.of_keeps k₀ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (chain_ok (.inl rfl) hs₀ (yo := TMP) (xo := X2) (v := fun k => BitVec.ofNat 32 (foldV 1 k)) f₀ 14
    (by decide) (by decide) (.inr (.inr (by decide))) (fun k hk t tk => ?_) (fun k _ t _ _ => ?_))
    fun t₁ ⟨k₁, m₁, c, f₁, r₁⟩ => ?_
  · have ts := hs₀.of_keeps tk (by decide)
    exact ⟨ts.ea (by omega_arith), ts.ea (by omega_arith)⟩
  · unfold foldV; split <;> rfl
  rw [WP.block_append_iff]
  refine WP.mono (freezeMask_ok f₁) fun t₂ ⟨e₂, m₂, k₂⟩ => ?_
  have k₀₂ : Keeps [.eax, .ecx] s t₂ :=
    (k₀.mono (by decide)).trans ((k₁.mono (by decide)).trans (k₂.mono (by decide)))
  refine WP.mono (select_ok (hs.of_keeps k₀₂ (by decide)) e₂) fun t₃ ⟨f₃, m₃, k₃⟩ => ⟨?_, ?_,
    (k₀₂.mono (by decide)).trans (k₃.mono (by decide))⟩
  · rw [m₀] at m₁ r₁
    have ex : ∀ i < 14, limbs t₂.mem base X2 i = limbs s.mem base X2 i := fun i hi => by
      rw [m₂]; exact m₁.limbs (k := 14) (.inl (by decide)) (by decide) hi
    rw [PassRel, ite_eq_left rfl, pow14, show false.toNat = 0 from rfl, Nat.add_zero,
      num_congr (fun k _ => foldV_lt (by decide : 1 < 2 ^ 32) k), foldV_14, Nat.mul_one] at r₁
    rw [← freeze_value (fe_lt _ _ _) (fe_lt _ _ _) r₁]
    cases c
    · exact num_congr fun i hi => (f₃ i hi).trans (ex i hi)
    · exact num_congr fun i hi => (f₃ i hi).trans (by rw [m₂]; rfl)
  · rw [m₀] at m₁
    rw [m₂] at m₃
    exact (FieldMem.work m₁ (by decide) (by decide)).trans (FieldMem.output m₃)

end VG.Proof.X448.X86
