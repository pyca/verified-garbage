module

public import VerifiedGarbage.Proof.MillerRabin.X86.StageStore
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFacts
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr

/-! # Load an exponent word using only the public remaining-window count -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Mont.X86 VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt)

theorem word_load {σ s : State} {base : Addr} {bytes w i : Nat}
    (facts : RoundFacts σ base bytes w) (h : Stage base bytes w σ s) (hi : i < 2 * w)
    (count : s.mem.readW (off base sK) 32 = BitVec.ofNat 32 (8 * (i + 1))) :
    WP isa (.block wordLoad) s fun t => Stage base bytes w σ t ∧
      w32 t.mem base sV = w32 σ.mem base (arrAt w 27 + 4 * i) ∧
      Frame [⟨off base sV, 4⟩] s.mem t.mem := by
  unfold wordLoad
  refine arrayPointer_ok (by decide) (by decide) (by decide)
    (by rw [h.read_header facts.fit (by decide), h.width facts.fit facts.width]) facts.upper
    h.context.ws.edi_toNat fun s₁ K₁ m₁ p₁ => ?_
  have h₁ := h.of_registers K₁ m₁
  refine wp_movS (by rw [h₁.read_header facts.fit (by decide), m₁, count]) fun s₂ U₂ _ => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun s₃ U₃ => wp_subS rfl fun s₄ U₄ _ =>
    wp_addS rfl fun s₅ U₅ _ => wp_addS rfl fun s₆ U₆ _ => wp_addS rfl fun s₇ U₇ _ => ?_
  have ecx : s₆.gpr .ecx = BitVec.ofNat 32 (4 * i) := by
    rw [U₆.gpr, U₅.gpr, U₄.gpr, U₃.gpr, U₂.gpr]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    have := facts.upper
    change (((2 ^ 32 - 1 + (8 * (i + 1) % 2 ^ 32 / 8)) % 2 ^ 32 +
      (2 ^ 32 - 1 + (8 * (i + 1) % 2 ^ 32 / 8)) % 2 ^ 32) % 2 ^ 32 +
      ((2 ^ 32 - 1 + (8 * (i + 1) % 2 ^ 32 / 8)) % 2 ^ 32 +
      (2 ^ 32 - 1 + (8 * (i + 1) % 2 ^ 32 / 8)) % 2 ^ 32) % 2 ^ 32) % 2 ^ 32 = (4 * i) % 2 ^ 32
    omega
  have p₆ : Rt.PtrAt s₆ base .ebp (arrAt w 27) := by
    rw [Rt.PtrAt, U₆.other .ebp (by decide), U₅.other .ebp (by decide), U₄.other .ebp (by decide),
      U₃.other .ebp (by decide), U₂.other .ebp (by decide)]
    exact p₁
  have p₇ : Rt.PtrAt s₇ base .ebp (arrAt w 27 + 4 * i) := by
    rw [Rt.PtrAt, U₇.gpr, Rt.ptr_add p₆, ecx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := facts.upper; omega : 4 * i < 2 ^ 32)]
  have h₇ := (((((h₁.of_registers U₂.keeps U₂.mem).of_registers U₃.keeps U₃.mem).of_registers
    U₄.keeps U₄.mem).of_registers U₅.keeps U₅.mem).of_registers U₆.keeps U₆.mem).of_registers U₇.keeps U₇.mem
  have m₇ : s₇.mem = s.mem := by rw [U₇.mem, U₆.mem, U₅.mem, U₄.mem, U₃.mem, U₂.mem, m₁]
  have bound := array_fits_bytes facts.fit (show 27 < 28 by decide)
  refine wp_movS (Rt.readSrc_ptr ⟨h₇.context.ws.wr, h₇.context.ws.nowrap⟩ p₇ (by omega)) fun s₈ U₈ _ => ?_
  have h₈ := h₇.of_registers U₈.keeps U₈.mem
  refine h₈.store_header facts.fit (by decide) fun t ht mt _ _ => WP.block_nil ?_
  have value : s₈.gpr .eax = σ.mem.readW (off base (arrAt w 27 + 4 * i)) 32 := by
    rw [U₈.gpr, Nat.add_zero, m₇]
    exact h.read_workspace32 facts.fit (by omega)
      ((array_static facts.lower (.inr (.inr (.inr rfl)))).subrange (by omega) (by omega))
  refine ⟨ht, ?_, ?_⟩
  · rw [mt, w32_write_self, value]
  · rw [mt, U₈.mem, m₇]
    exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)

end VG.Proof.MillerRabin.X86
