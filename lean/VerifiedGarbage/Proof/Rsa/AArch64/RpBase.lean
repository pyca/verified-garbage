import VerifiedGarbage.Proof.Rsa.AArch64.Inv
import VerifiedGarbage.Impl.Rsa.AArch64.Recover

/-!
# `vg_rsa_recover_primes` on AArch64: the working space

The header slots the recovery changes besides the arrays (`RMut`: `-n⁻¹`,
the mask, the candidate's number, `R² mod n`'s counter, `t`, and the loops'
counters and masks), which keep the working space (`Ws.congrR`,
`Ws.congrG`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The header slots the recovery changes: `-n⁻¹` (7), the mask (22), the
candidate's number (25), `R² mod n`'s counter (26), `t` (27), and the
counters and masks (29, 30, 31). -/
def rSlot (i : Nat) : Bool :=
  i == 7 || i == 22 || i == 25 || i == 26 || i == 27 || i == 29 || i == 30 || i == 31

/-- The ranges the recovery's pieces may change: arrays, and the slots of
`rSlot`. -/
def RMut (r : Nat × Nat) : Prop := 8 * 32 ≤ r.1 ∨ ∃ i, rSlot i = true ∧ r = (8 * i, 8)

theorem RMut.ofSlot (w j n : Nat) : RMut (slot w j, n) :=
  Or.inl (by unfold slot hdrBytes; omega)

theorem RMut.hdr {i : Nat} (h : rSlot i = true) : RMut (8 * i, 8) := Or.inr ⟨i, h, rfl⟩

theorem RMut.of_mut {r : Nat × Nat} (h : Mut r) : RMut r := by
  rcases h with h | rfl
  · exact Or.inl h
  · exact RMut.hdr (by decide)

/-- A slot of `rSlot` is not `w`'s, the stride's or a base's. -/
theorem rSlot_ne {i j : Nat} (h : rSlot i = true) (hj : j ∈ [sW, sStride] ∨ (8 ≤ j ∧ j < 16)) :
    8 * j + 8 ≤ 8 * i ∨ 8 * i + 8 ≤ 8 * j := by
  simp only [rSlot, Bool.or_eq_true, beq_iff_eq] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false, sW, sStride, sFn] at hj
  omega

theorem Ws.congrR {s t : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {rs : List (Nat × Nat)}
    (hf : Frm B rs s.mem t.mem) (hm : ∀ r ∈ rs, RMut r) {regs : List Reg} (k : Keep regs s t)
    (hr : .x0 ∉ regs) : Ws t B Z w := by
  have hh : ∀ i, i ∈ [sW, sStride] ∨ (8 ≤ i ∧ i < 16) → word t.mem B (8 * i) = word s.mem B (8 * i) := by
    intro i hi
    have hi' : i < 16 ∨ i = 28 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, sW, sStride, sFn] at hi; omega
    exact hf.word_eq (fun r hr => by
      rcases hm r hr with h | ⟨j, hj, rfl⟩
      · omega
      · have := rSlot_ne hj hi; dsimp only; omega)
      (by have := h.scr.nowrap; have := hdr_lt_slot w 16 (show 31 < 32 by decide); have := h.hZ; omega)
  exact ⟨h.scr.congr k.wr, (k.gpr .x0 hr).trans h.x0, (hh sW (.inl (by simp))).trans h.hw,
    (hh sStride (.inl (by simp))).trans h.hS,
    fun j hj => (hh (sArr j) (.inr (by unfold sArr; omega))).trans (h.harr j hj), h.hZ, h.w1, h.w2⟩

theorem rg_rmut {w : Nat} {js hs : List Nat} (h : ∀ i ∈ hs, rSlot i = true) : ∀ r ∈ rg w js hs, RMut r := by
  intro r hr
  simp only [rg, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨j, _, rfl⟩ | ⟨i, hi, rfl⟩
  · exact RMut.ofSlot _ _ _
  · exact RMut.hdr (h i hi)

theorem Ws.congrG {s t : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {js hs : List Nat}
    (hf : Frm B (rg w js hs) s.mem t.mem) (hhs : ∀ i ∈ hs, rSlot i = true) {regs : List Reg} (k : Keep regs s t)
    (hr : .x0 ∉ regs) : Ws t B Z w :=
  h.congrR hf (rg_rmut hhs) k hr

end VG.Proof.Rsa.AArch64
