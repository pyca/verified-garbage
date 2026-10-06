import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
import VerifiedGarbage.Impl.Rsa.X86_64.Recover

/-!
# `vg_rsa_recover_primes` on x86-64: the working space

The header slots the recovery changes besides the arrays (`RMut`: `-n⁻¹`,
the mask, the candidates' counters and masks, `t` and `sMo`), which keep the
working space (`Ws.congrR`); and the value of a number's low words
(`wv_mod`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The header slots the recovery changes: `-n⁻¹` (7), the mask (22), the
candidate's number (25), the counters and masks (26, 30, 31), `t` (27) and
`sMo` (29). -/
def rSlot (i : Nat) : Bool :=
  i == 7 || i == 22 || i == 25 || i == 26 || i == 27 || i == 29 || i == 30 || i == 31

/-- The ranges the recovery's pieces may change: arrays, and the slots of
`rSlot`. -/
def RMut (r : Nat × Nat) : Prop := 8 * 32 ≤ r.1 ∨ ∃ i, rSlot i = true ∧ r = (8 * i, 8)

theorem RMut.ofSlot (w j n : Nat) : RMut (Bignum.slot w j, n) :=
  Or.inl (by unfold Bignum.slot hdrBytes; omega)

theorem RMut.hdr {i : Nat} (h : rSlot i = true) : RMut (8 * i, 8) := Or.inr ⟨i, h, rfl⟩

theorem RMut.of_mut {r : Nat × Nat} (h : Mut r) : RMut r := by
  rcases h with h | rfl | rfl
  · exact Or.inl h
  · exact RMut.hdr (by decide)
  · exact RMut.hdr (by decide)

/-- A slot of `rSlot` is not `w`'s, the stride's or a base's. -/
theorem rSlot_ne {i j : Nat} (h : rSlot i = true) (hj : j ∈ [sW, sStride] ∨ (8 ≤ j ∧ j < 16)) :
    8 * j + 8 ≤ 8 * i ∨ 8 * i + 8 ≤ 8 * j := by
  simp only [rSlot, Bool.or_eq_true, beq_iff_eq] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false, sW, sStride, sFn] at hj
  omega

theorem Ws.congrR {s t : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {rs : List (Nat × Nat)}
    (hf : Frm B rs s.mem t.mem) (hm : ∀ r ∈ rs, RMut r) {regs : List Reg} (k : Keep regs s t)
    (hr : .rdi ∉ regs) : Ws t B Z w := by
  have hh : ∀ i, i ∈ [sW, sStride] ∨ (8 ≤ i ∧ i < 16) → word t.mem B (8 * i) = word s.mem B (8 * i) := by
    intro i hi
    have hi' : i < 16 ∨ i = 28 := by simp only [List.mem_cons, List.not_mem_nil, or_false, sW, sStride, sFn] at hi; omega
    exact hf.word_eq (fun r hr => by
      rcases hm r hr with h | ⟨j, hj, rfl⟩
      · omega
      · have := rSlot_ne hj hi; dsimp only; omega)
      (by have := h.scr.nowrap; have := hdr_lt_slot w 16 (show 31 < 32 by decide); have := h.hZ; omega)
  exact ⟨h.scr.congr k.2.2, (k.gpr hr).trans h.rdi, (hh sW (.inl (by simp))).trans h.hw,
    (hh sStride (.inl (by simp))).trans h.hS, fun j hj => (hh (sArr j) (.inr (by unfold sArr; omega))).trans (h.harr j hj),
    h.hZ, h.w1, h.w2⟩

/-- The low `j` words of a number of `w ≥ j` words. -/
theorem wv_mod (m : Mem) (B : Addr) (e : Nat) {j w : Nat} (hj : j ≤ w) :
    wv m B e w % 2 ^ (64 * j) = wv m B e j := by
  have e1 := wv_add m B e j (w - j)
  rw [show j + (w - j) = w by omega] at e1
  rw [e1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (wv_lt _ _ _ _)]

end VG.Proof.Rsa.X86_64
