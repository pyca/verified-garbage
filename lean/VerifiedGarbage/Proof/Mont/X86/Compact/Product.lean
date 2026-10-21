module

public import VerifiedGarbage.Proof.Mont.X86.Compact.Rows

/-! # The compact product after every CIOS row -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

/-- The rows, from the zeroed accumulator. -/
theorem rowsAll_ok {t : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (hw : Ws t W L) (ha : Args t W L A)
    {N S mo a b m : Nat} (base : (A 0).toNat = W.toNat)
    (V : Metadata t.mem W A N S mo a b) (hL : Lay L N S mo a b)
    (hN : 0 < N) (hN32 : 4 * N < 2 ^ 32) (hedi : PtrAt t W .edi S)
    (hm : val32 t.mem W mo N = m) (hinv : (m * w32 t.mem W 56 + 1) % 2 ^ 32 = 0)
    (hB : val32 t.mem W b N < m) (hZ : val32 t.mem W (S + Compact.accOff) (2 * N + 1) = 0) :
    WP isa Compact.rows t fun u => ∃ s₁, Keeps [.ebp] t s₁ ∧ s₁.mem = t.mem ∧ LoopInvR W N S a b m N s₁ u := by
  have hn := hw.nowrap
  have acc : Compact.accOff = 24 := rfl
  unfold Compact.rows
  simp only [Compact.accPtr]
  refine WP.seq (wp_movS rfl fun s₁ u₁ _ => wp_addS rfl fun s₂ u₂ _ => WP.block_nil ?_)
  have K₂ : Keeps [.ebp] t s₂ := (u₁.keeps.mono (by decide)).widen u₂.keeps
  have m₂ : s₂.mem = t.mem := by rw [u₂.mem, u₁.mem]
  have hw₂ := hw.of_keeps K₂
  have ha₂ : Args s₂ W L A := (ha.of_upd u₁ (by decide)).of_upd u₂ (by decide)
  have edi₂ : PtrAt s₂ W .edi S := by rw [PtrAt, K₂.1 _ (by decide)]; exact hedi
  have ebp₂ : PtrAt s₂ W .ebp (S + Compact.accOff) := by
    rw [PtrAt, u₂.gpr, u₁.gpr, ptr_add hedi]; simp only [BitVec.toNat_ofNat]; omega_using [acc]
  have hmpos : 0 < m := by omega_using [hB]
  have I₀ : LoopInvR W N S a b m 0 s₂ s₂ := by
    refine ⟨by simpa using ebp₂, Outs.refl _ _ _, Keeps.refl _ _, ?_, ⟨0, ?_⟩⟩
    · rw [m₂]; simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero, hZ]; omega_using [hmpos]
    · rw [m₂]; simp [val32, hZ]
  exact WP.mono (loopR_ok hw₂ ha₂ base (by rw [m₂]; exact V) hL hN hN32 edi₂ (by rw [m₂]; exact hm) (by rw [m₂]; exact hinv)
    (by rw [m₂]; exact hB) I₀) fun u I => ⟨s₂, K₂, m₂, I⟩

end VG.Proof.Mont.X86.Compact
