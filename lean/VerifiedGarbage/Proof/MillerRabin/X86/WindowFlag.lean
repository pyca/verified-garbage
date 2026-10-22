module

public import VerifiedGarbage.Proof.MillerRabin.X86.StageStore
public import VerifiedGarbage.Proof.MillerRabin.X86.Mask
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr

/-! # After a nonzero digit, retain precisely the equality-test flag -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Mont.X86 VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt)

theorem window_flag {σ s : State} {base : Addr} {bytes w d : Nat} {F E1 E2 : Bool}
    (h : Stage base bytes w σ s) (hf : arrAt w 28 ≤ bytes) (hd : d < 16)
    (digit : s.mem.readW (off base sV) 32 >>> 28 = BitVec.ofNat 32 d)
    (flag : s.mem.readW (off base sF) 32 = BitVec.ofNat 32 F.toNat)
    (equal1 : s.mem.readW (off base sE1) 32 = BitVec.ofNat 32 E1.toNat)
    (equal2 : s.mem.readW (off base sE2) 32 = BitVec.ofNat 32 E2.toNat) :
    WP isa (.block winFlag) s fun t => Stage base bytes w σ t ∧
      w32 t.mem base sF = (if d = 0 then F else E1 || E2).toNat ∧
      t.gpr .eax = s.mem.readW (off base sV) 32 ∧ Frame [⟨off base sF, 4⟩] s.mem t.mem := by
  unfold winFlag
  refine wp_movS (h.read_header hf (by decide)) fun s₁ U₁ _ => wp_movS rfl fun s₂ U₂ _ => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun s₃ U₃ =>
    wp_subS rfl fun s₄ U₄ _ => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun s₅ U₅ =>
    wp_movS rfl fun s₆ U₆ _ => wp_logicS (.inr rfl) rfl fun s₇ U₇ => ?_
  have h₇ := ((((((h.of_registers U₁.keeps U₁.mem).of_registers U₂.keeps U₂.mem).of_registers
    U₃.keeps U₃.mem).of_registers U₄.keeps U₄.mem).of_registers U₅.keeps U₅.mem).of_registers
    U₆.keeps U₆.mem).of_registers U₇.keeps U₇.mem
  have m₇ : s₇.mem = s.mem := by rw [U₇.mem, U₆.mem, U₅.mem, U₄.mem, U₃.mem, U₂.mem, U₁.mem]
  refine wp_movS (by rw [h₇.read_header hf (by decide), m₇, equal1]) fun s₈ U₈ _ => ?_
  have h₈ := h₇.of_registers U₈.keeps U₈.mem
  refine wp_orS (by rw [h₈.read_header hf (by decide), U₈.mem, m₇, equal2]) fun s₉ U₉ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₁₀ U₁₀ => ?_
  have h₁₀ := (h₈.of_registers U₉.keeps U₉.mem).of_registers U₁₀.keeps U₁₀.mem
  refine wp_movS (by rw [h₁₀.read_header hf (by decide), U₁₀.mem, U₉.mem, U₈.mem, m₇, flag])
    fun s₁₁ U₁₁ _ => wp_logicS (.inl rfl) rfl fun s₁₂ U₁₂ => wp_orS rfl fun s₁₃ U₁₃ => ?_
  have h₁₃ := ((h₁₀.of_registers U₁₁.keeps U₁₁.mem).of_registers U₁₂.keeps U₁₂.mem).of_registers U₁₃.keeps U₁₃.mem
  refine h₁₃.store_header hf (by decide) fun t ht mt Kt _ => WP.block_nil ?_
  have zero : s₅.gpr .edx = BitVec.ofNat 32 (decide (d = 0)).toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [U₅.gpr, U₄.gpr, U₃.gpr, U₂.gpr, U₁.gpr, digit,
      VG.Proof.MillerRabin.Math.mask_zero d hd, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (by cases decide (d = 0) <;> decide)).symm
  have bits : (s₁₃.gpr .ebx).toNat = (if d = 0 then F else E1 || E2).toNat := by
    rw [U₁₃.gpr, U₁₂.other .ebx (by decide), U₁₁.other .ebx (by decide), U₁₀.gpr, U₉.gpr,
      U₈.gpr, U₉.other .ecx (by decide), U₈.other .ecx (by decide), U₇.gpr,
      U₆.gpr, zero, U₁₂.gpr, U₁₁.gpr, U₁₁.other .edx (by decide), U₁₀.other .edx (by decide),
      U₉.other .edx (by decide), U₈.other .edx (by decide), U₇.other .edx (by decide),
      U₆.other .edx (by decide), zero]
    simp only [↓reduceIte, ite_eq_right (by decide : AluOp.xor ≠ AluOp.and)]
    simpa only [decide_eq_true_eq] using VG.Proof.MillerRabin.Math.flag_bits (decide (d = 0)) E1 E2 F
  refine ⟨ht, by rw [mt, w32_write_self]; exact bits, ?_, ?_⟩
  · rw [Kt.1 .eax (by decide), U₁₃.other .eax (by decide), U₁₂.other .eax (by decide),
      U₁₁.other .eax (by decide), U₁₀.other .eax (by decide), U₉.other .eax (by decide),
      U₈.other .eax (by decide), U₇.other .eax (by decide), U₆.other .eax (by decide),
      U₅.other .eax (by decide), U₄.other .eax (by decide), U₃.other .eax (by decide),
      U₂.other .eax (by decide), U₁.gpr]
  · rw [mt, U₁₃.mem, U₁₂.mem, U₁₁.mem, U₁₀.mem, U₉.mem, U₈.mem, m₇]
    exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)

end VG.Proof.MillerRabin.X86
