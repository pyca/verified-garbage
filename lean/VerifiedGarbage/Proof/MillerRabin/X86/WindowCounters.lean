module

public import VerifiedGarbage.Proof.MillerRabin.X86.StageStore
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFacts

/-! # Initialize the flag and the public count of exponent windows -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Mont.X86 VG.Impl.MillerRabin.X86

theorem window_counters {σ s : State} {base : Addr} {bytes w : Nat}
    (facts : RoundFacts σ base bytes w) (h : Stage base bytes w σ s) :
    WP isa (.block winCounters) s fun t => Stage base bytes w σ t ∧
      w32 t.mem base sF = 0 ∧ w32 t.mem base sK = 16 * w ∧
      Frame ([sF, sK].map (fun d => ⟨off base d, 4⟩)) s.mem t.mem := by
  simp only [winCounters, List.cons_append, List.nil_append]
  refine wp_movS rfl fun s₁ U₁ _ => ?_
  have h₁ := h.of_registers U₁.keeps U₁.mem
  refine h₁.store_header facts.fit (by decide) fun s₂ h₂ m₂ _ _ => ?_
  refine width_ok (by rw [h₂.read_header facts.fit (by decide), h₂.width facts.fit facts.width])
    fun s₃ K₃ m₃ v₃ => wp_addS rfl fun s₄ U₄ _ => ?_
  have h₄ := (h₂.of_registers K₃ m₃).of_registers U₄.keeps U₄.mem
  refine h₄.store_header facts.fit (by decide) fun t ht mt _ _ => WP.block_nil ?_
  have value : s₄.gpr .eax = BitVec.ofNat 32 (16 * w) := by
    rw [U₄.gpr, v₃, ← BitVec.ofNat_add]
    congr 1
    omega
  have memory : t.mem = (s.mem.writeW (off base sF) (0 : BitVec 32)).writeW (off base sK)
      (BitVec.ofNat 32 (16 * w)) := by rw [mt, value, U₄.mem, m₃, m₂, U₁.gpr, U₁.mem]
  have hdrFit : 256 ≤ bytes := Nat.le_trans (Nat.le_add_right _ _) facts.fit
  have nw256 : base.toNat + 256 ≤ 2 ^ 32 := Nat.le_trans (Nat.add_le_add_left hdrFit _) h.context.ws.nowrap
  refine ⟨ht, ?_, ?_, ?_⟩
  · rw [memory, w32_write_ne nw256 (by decide : sK + 4 ≤ 256) (by decide : sF + 4 ≤ 256)
      (by decide), w32_write_self]
    rfl
  · rw [memory, w32_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := facts.upper; omega)]
  · rw [memory]
    exact ((Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)).writeW
      (by simp) _ (Region.contains_self _ _)

end VG.Proof.MillerRabin.X86
