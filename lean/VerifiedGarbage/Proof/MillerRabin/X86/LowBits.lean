module

public import VerifiedGarbage.Proof.MillerRabin.X86.FoldBits
public import VerifiedGarbage.Proof.MillerRabin.X86.StageStore
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFacts

/-! # Compute the last squaring threshold from the prepared exponent tail -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Mont.X86 VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt)

theorem low_bits {σ s : State} {base : Addr} {bytes w : Nat}
    (facts : RoundFacts σ base bytes w) (h : Stage base bytes w σ s) :
    WP isa (.block lowBits) s fun t => Stage base bytes w σ t ∧ w32 t.mem base sQ = 3 ∧
      w32 t.mem base sR = (VG.Proof.MillerRabin.Math.foldR
        (σ.mem.readW (off base (arrAt w 27 + 8 * w)) 32)
        (σ.mem.readW (off base (arrAt w 27 + 8 * w + 4)) 32)).toNat ∧
      Frame ([sR, sQ].map (fun d => ⟨off base d, 4⟩)) s.mem t.mem := by
  unfold lowBits
  simp only [List.append_assoc]
  refine arrayPointer_ok (by decide) (by decide) (by decide)
    (by rw [h.read_header facts.fit (by decide), h.width facts.fit facts.width]) facts.upper
    h.context.ws.edi_toNat fun s₁ K₁ m₁ p₁ => ?_
  have h₁ := h.of_registers K₁ m₁
  refine width_ok (by rw [h₁.read_header facts.fit (by decide), h₁.width facts.fit facts.width])
    fun s₂ K₂ m₂ v₂ => wp_addS rfl fun s₃ U₃ _ => ?_
  have h₃ := (h₁.of_registers K₂ m₂).of_registers U₃.keeps U₃.mem
  have p₂ : Rt.PtrAt s₂ base .ebp (arrAt w 27) := by rw [Rt.PtrAt, K₂.1 .ebp (by decide)]; exact p₁
  have p₃ : Rt.PtrAt s₃ base .ebp (arrAt w 27 + 8 * w) := by
    rw [Rt.PtrAt, U₃.gpr, Rt.ptr_add p₂, v₂, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := facts.upper; omega : 8 * w < 2 ^ 32)]
  have fit := array_fits_bytes facts.fit (show 27 < 28 by decide)
  refine wp_movS (Rt.readSrc_ptr ⟨h₃.context.ws.wr, h₃.context.ws.nowrap⟩ p₃ (by omega)) fun s₄ U₄ _ => ?_
  have h₄ := h₃.of_registers U₄.keeps U₄.mem
  have p₄ : Rt.PtrAt s₄ base .ebp (arrAt w 27 + 8 * w) := by rw [Rt.PtrAt, U₄.other .ebp (by decide)]; exact p₃
  refine wp_orS (Rt.readSrc_ptr ⟨h₄.context.ws.wr, h₄.context.ws.nowrap⟩ p₄ (by omega)) fun s₅ U₅ => ?_
  have h₅ := h₄.of_registers U₅.keeps U₅.mem
  have m₅ : s₅.mem = s.mem := by rw [U₅.mem, U₄.mem, U₃.mem, m₂, m₁]
  have lo : s.mem.readW (off base (arrAt w 27 + 8 * w)) 32 =
      σ.mem.readW (off base (arrAt w 27 + 8 * w)) 32 :=
    h.read_workspace32 facts.fit (by omega)
      ((array_static facts.lower (.inr (.inr (.inr rfl)))).subrange (by omega) (by omega))
  have hi : s.mem.readW (off base (arrAt w 27 + 8 * w + 4)) 32 =
      σ.mem.readW (off base (arrAt w 27 + 8 * w + 4)) 32 :=
    h.read_workspace32 facts.fit (by omega)
      ((array_static facts.lower (.inr (.inr (.inr rfl)))).subrange (by omega) (by omega))
  have value₅ : s₅.gpr .eax = σ.mem.readW (off base (arrAt w 27 + 8 * w)) 32 |||
      σ.mem.readW (off base (arrAt w 27 + 8 * w + 4)) 32 := by
    rw [U₅.gpr, U₄.gpr, Nat.add_zero, U₄.mem, U₃.mem, m₂, m₁, lo, hi]
  refine fold_bits_ok value₅ fun s₆ K₆ m₆ v₆ => ?_
  have h₆ := h₅.of_registers K₆ m₆
  refine h₆.store_header facts.fit (by decide) fun s₇ h₇ m₇ _ _ => ?_
  refine wp_movS rfl fun s₈ U₈ _ => ?_
  have h₈ := h₇.of_registers U₈.keeps U₈.mem
  refine h₈.store_header facts.fit (by decide) fun t ht mt _ _ => WP.block_nil ?_
  have fold : s₆.gpr .eax = VG.Proof.MillerRabin.Math.foldR
      (σ.mem.readW (off base (arrAt w 27 + 8 * w)) 32)
      (σ.mem.readW (off base (arrAt w 27 + 8 * w + 4)) 32) := by
    rw [v₆]
    unfold VG.Proof.MillerRabin.Math.foldR
    rw [show (σ.mem.readW (off base (arrAt w 27 + 8 * w)) 32 |||
      σ.mem.readW (off base (arrAt w 27 + 8 * w + 4)) 32) ||| (0 : BitVec 32) =
      σ.mem.readW (off base (arrAt w 27 + 8 * w)) 32 |||
      σ.mem.readW (off base (arrAt w 27 + 8 * w + 4)) 32 from BitVec.or_zero]
  have memory : t.mem = (s.mem.writeW (off base sR) (s₆.gpr .eax)).writeW (off base sQ) (3 : BitVec 32) := by
    rw [mt, U₈.gpr, U₈.mem, m₇, m₆, m₅]
  have hdrFit : 256 ≤ bytes := Nat.le_trans (Nat.le_add_right _ _) facts.fit
  have nw256 : base.toNat + 256 ≤ 2 ^ 32 := Nat.le_trans (Nat.add_le_add_left hdrFit _) h.context.ws.nowrap
  refine ⟨ht, ?_, ?_, ?_⟩
  · rw [memory, w32_write_self]
    rfl
  · rw [memory, w32_write_ne nw256 (by decide : sQ + 4 ≤ 256) (by decide : sR + 4 ≤ 256)
      (by decide), w32_write_self, fold]
  · rw [memory]
    exact ((Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)).writeW
      (by simp) _ (Region.contains_self _ _)

end VG.Proof.MillerRabin.X86
