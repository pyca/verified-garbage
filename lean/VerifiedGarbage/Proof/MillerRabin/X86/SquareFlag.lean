module

public import VerifiedGarbage.Proof.MillerRabin.X86.StageStore
public import VerifiedGarbage.Proof.MillerRabin.X86.Mask
public import VerifiedGarbage.Proof.Mont.X86.Rt.Step
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr

/-! # Incorporate the minus-one comparison above the squaring threshold -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86 VG.Impl.Mont.X86 VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt)

theorem square_flag {σ s : State} {base : Addr} {bytes w q r : Nat} {F E : Bool}
    (h : Stage base bytes w σ s) (hf : arrAt w 28 ≤ bytes)
    (hq : 0 < q ∧ q < 2 ^ 31) (hr : r < 2 ^ 31)
    (count : s.mem.readW (off base sQ) 32 = BitVec.ofNat 32 q)
    (threshold : s.mem.readW (off base sR) 32 = BitVec.ofNat 32 r)
    (flag : s.mem.readW (off base sF) 32 = BitVec.ofNat 32 F.toNat)
    (equal : s.mem.readW (off base sE2) 32 = BitVec.ofNat 32 E.toNat) :
    WP isa (.block sqFlag) s fun t =>
      Stage base bytes w σ t ∧ w32 t.mem base sQ = q - 1 ∧
      w32 t.mem base sF = (F || (decide (r < q) && E)).toNat ∧
      t.zf = some (decide (q = 1)) ∧
      Frame [⟨off base sF, 4⟩, ⟨off base sQ, 4⟩] s.mem t.mem := by
  unfold sqFlag
  refine wp_movS (by rw [h.read_header hf (by decide), count]) fun s₁ U₁ _ => ?_
  have h₁ := h.of_registers U₁.keeps U₁.mem
  refine wp_movS (by rw [h₁.read_header hf (by decide), U₁.mem, threshold]) fun s₂ U₂ _ => ?_
  refine wp_subS rfl fun s₃ U₃ _ => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun s₄ U₄ => ?_
  have K₄ : Keeps [.ecx, .edx] s s₄ :=
    (((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans
      (U₃.keeps.mono (by decide))).trans (U₄.keeps.mono (by decide))
  have m₄ : s₄.mem = s.mem := by rw [U₄.mem, U₃.mem, U₂.mem, U₁.mem]
  have h₄ := h.of_registers K₄ m₄
  refine wp_logicS (.inl rfl) (by rw [h₄.read_header hf (by decide), m₄, equal]) fun s₅ U₅ => ?_
  have h₅ := h₄.of_registers U₅.keeps U₅.mem
  refine wp_movS (by rw [h₅.read_header hf (by decide), U₅.mem, m₄, flag]) fun s₆ U₆ _ => ?_
  refine wp_orS rfl fun s₇ U₇ => ?_
  have h₇ := (h₅.of_registers U₆.keeps U₆.mem).of_registers U₇.keeps U₇.mem
  refine h₇.store_header hf (by decide) fun s₈ h₈ m₈ K₈ _ => ?_
  refine wp_subZ rfl fun s₉ U₉ z₉ => ?_
  have h₉ := h₈.of_registers U₉.keeps U₉.mem
  refine h₉.store_header hf (by decide) fun t ht mt _ zt => WP.block_nil ?_
  have q₈ : s₈.gpr .ecx = BitVec.ofNat 32 q := by
    rw [K₈.1 .ecx (by decide), U₇.other .ecx (by decide), U₆.other .ecx (by decide),
      U₅.other .ecx (by decide), U₄.other .ecx (by decide), U₃.other .ecx (by decide),
      U₂.other .ecx (by decide), U₁.gpr]
  have mask : s₄.gpr .edx = BitVec.ofNat 32 (decide (r < q)).toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [U₄.gpr, U₃.gpr, U₂.gpr, U₂.other .ecx (by decide), U₁.gpr,
      VG.Proof.MillerRabin.Math.mask_lt hr hq.2, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (by cases decide (r < q) <;> decide)).symm
  have f₇ : s₇.gpr .eax = BitVec.ofNat 32 (F || (decide (r < q) && E)).toNat := by
    rw [U₇.gpr, U₆.gpr, U₆.other .edx (by decide), U₅.gpr, mask]
    cases F <;> cases E <;> cases decide (r < q) <;> rfl
  have dec : s₈.gpr .ecx - 1 = BitVec.ofNat 32 (q - 1) := by
    rw [q₈]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    change (2 ^ 32 - 1 + q % 2 ^ 32) % 2 ^ 32 = (q - 1) % 2 ^ 32
    omega
  have memory : t.mem = (s.mem.writeW (off base sF)
      (BitVec.ofNat 32 (F || (decide (r < q) && E)).toNat)).writeW (off base sQ)
        (BitVec.ofNat 32 (q - 1)) := by
    rw [mt, U₉.gpr, dec, U₉.mem, m₈, f₇, U₇.mem, U₆.mem, U₅.mem, m₄]
  have hdrFit : 256 ≤ bytes := Nat.le_trans (Nat.le_add_right _ _) hf
  have nw256 : base.toNat + 256 ≤ 2 ^ 32 :=
    Nat.le_trans (Nat.add_le_add_left hdrFit _) h.context.ws.nowrap
  refine ⟨ht, ?_, ?_, ?_, ?_⟩
  · rw [memory, w32_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · rw [memory, w32_write_ne nw256 (by decide : sQ + 4 ≤ 256) (by decide : sF + 4 ≤ 256) (by decide),
      w32_write_self, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by cases F || (decide (r < q) && E) <;> decide)
  · rw [zt, z₉, dec]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    rw [← BitVec.toNat_inj, BitVec.toNat_ofNat]
    change (q - 1) % 2 ^ 32 = 0 ↔ q = 1
    omega
  · rw [memory]
    exact ((Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)).writeW
      (by simp) _ (Region.contains_self _ _)

end VG.Proof.MillerRabin.X86
