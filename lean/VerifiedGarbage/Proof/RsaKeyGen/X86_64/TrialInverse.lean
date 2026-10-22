module

public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.TrialInverse
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Words

/-! # The five-bit seed used by the trial-division inverse -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MlKem.X86_64
open VG.Proof.Bignum (emod_pow_weaken neg_inv)

/-- The seed identity is a fact about only five bits. -/
theorem inverse_seed5 (a : BitVec 64) (hodd : a.toNat % 2 = 1) :
    (a * ((a + a + a) ^^^ 2)).setWidth 5 = 1 := by
  have small : ∀ b : BitVec 5, b.toNat % 2 = 1 → b * ((b + b + b) ^^^ 2) = 1 := by decide
  have hb : (a.setWidth 5).toNat % 2 = 1 := by
    simp only [BitVec.toNat_setWidth]
    omega
  simpa (disch := decide) only [BitVec.setWidth_mul, BitVec.setWidth_add, BitVec.setWidth_xor,
    show (2 : BitVec 64).setWidth 5 = (2 : BitVec 5) from rfl] using small (a.setWidth 5) hb

/-- Lift the finite seed identity to the integer congruence Newton uses. -/
theorem inverse_seed5_mod (a : BitVec 64) (hodd : a.toNat % 2 = 1) :
    ((a.toNat : Int) * ((a + a + a) ^^^ 2).toNat - 1) % (2 ^ 5 : Int) = 0 := by
  have h := congrArg BitVec.toNat (inverse_seed5 a hodd)
  simp only [BitVec.toNat_setWidth, BitVec.toNat_mul] at h
  rw [Nat.mod_mod_of_dvd _ (show 2 ^ 5 ∣ 2 ^ 64 by decide)] at h
  have hi := congrArg (fun n : Nat => (n : Int)) h
  simp only [Int.natCast_emod, Int.natCast_mul] at hi
  change (a.toNat : Int) * ((a + a + a) ^^^ 2).toNat % 32 = 1 at hi
  omega

/-- `trialInverse`: `-m₀⁻¹ mod 2⁶⁴` into `r15`, for the odd `m₀` in `rbx`. -/
theorem trialInverse_ok (s : State) (hodd : (s.gpr .rbx).toNat % 2 = 1) :
    WP isa (.block trialInverse) s fun t =>
      ((s.gpr .rbx).toNat * (t.gpr .r15).toNat + 1) % 2 ^ 64 = 0 ∧
      Keep [.rax, .rcx, .rdx, .rsi, .r15] s t ∧ t.mem = s.mem := by
  unfold trialInverse
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rcx] (c := .block [.mov .rcx (.reg .rbx), .alu .add .rcx (.reg .rcx),
      .alu .add .rcx (.reg .rbx), .alu .xor .rcx (.imm 2)]) (Q := fun t =>
    t.gpr .rcx = ((s.gpr .rbx + s.gpr .rbx + s.gpr .rbx) ^^^ 2) ∧ t.mem = s.mem) (by xrun) rfl) fun t₀ ⟨⟨h₀, hm₀⟩, k₀⟩ => ?_
  have hb₀ : t₀.gpr .rbx = s.gpr .rbx := k₀.gpr (by decide)
  have e₀ : (((t₀.gpr .rbx).toNat : Int) * (t₀.gpr .rcx).toNat - 1) % (2 ^ 5 : Int) = 0 := by
    rw [hb₀, h₀]
    exact inverse_seed5_mod _ hodd
  rw [WP.block_append_iff]
  refine WP.mono (newton_step_ok t₀ (j := 5) (by decide) e₀) fun t₁ ⟨e₁, hb₁, hm₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (newton_step_ok t₁ (j := 10) (by decide) e₁) fun t₂ ⟨e₂, hb₂, hm₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (newton_step_ok t₂ (j := 20) (by decide) e₂) fun t₃ ⟨e₃, hb₃, hm₃, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (newton_step_ok t₃ (j := 32) (by decide) (emod_pow_weaken (by decide) e₃))
    fun t₄ ⟨e₄, hb₄, hm₄, k₄⟩ => ?_
  have hb : t₄.gpr .rbx = s.gpr .rbx := hb₄.trans (hb₃.trans (hb₂.trans (hb₁.trans hb₀)))
  have kk := (((k₀.trans k₁).trans k₂).trans k₃).trans k₄
  rw [hb] at e₄
  refine WP.mono (WP.keep [.r15] (Q := fun t => t.gpr .r15 = 0 - t₄.gpr .rcx ∧ t.mem = t₄.mem)
    (by xrun; rfl) rfl) fun t ⟨⟨h15, hm⟩, k⟩ => ⟨?_, (kk.trans k).mono (by decide), ?_⟩
  · rw [h15, BitVec.toNat_sub, show (0 : BitVec 64).toNat = 0 from rfl]
    exact neg_inv (t₄.gpr .rcx).isLt e₄
  · rw [hm, hm₄, hm₃, hm₂, hm₁, hm₀]

end VG.Proof.RsaKeyGen.X86_64
