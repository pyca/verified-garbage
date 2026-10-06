import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Candidate
import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs

/-!
# A candidate on AArch64: the working space, and instructions for `brun`

The candidate works in the layout of the RSA key routines (`Ws`), but also
keeps its own values in header slots, which `Ws.congr` does not allow: `KMut`
is any range of the working space but the header words that `Ws` depends on
(`w`, the bases and the stride), and `Ws.congr'` keeps `Ws` across changes
to such ranges. `exec_mul_w`, `exec_addImm_w`, `exec_movz_x'` and
`exec_movk_x` are the instructions `brun` does not know.
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- A range that `Ws` does not depend on: past the header, or a header
slot other than `w`, the bases and the stride. -/
def KMut (r : Nat × Nat) : Prop :=
  8 * 32 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * sW ∨ (8 * sMinv ≤ r.1 ∧ r.1 + r.2 ≤ 8 * sArr 0) ∨
    (8 * sArr 8 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * sStride) ∨ 8 * (sStride + 1) ≤ r.1

theorem KMut.ofSlot (w j n : Nat) : KMut (slot w j, n) := Or.inl (by unfold slot hdrBytes; omega)

/-- A header slot `i` that `Ws` does not depend on. -/
theorem KMut.hdr {i : Nat} (h : i < sW ∨ i = sMinv ∨ (sArr 8 ≤ i ∧ i < sStride) ∨ sStride < i) :
    KMut (8 * i, 8) := by
  simp only [KMut, sW, sMinv, sArr, sStride, sFn] at h ⊢; omega

theorem _root_.VG.Proof.Rsa.AArch64.Ws.congr' {s t : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {rs : List (Nat × Nat)}
    (hf : Frm B rs s.mem t.mem) (hm : ∀ r ∈ rs, KMut r) {regs : List Reg} (k : Keep regs s t)
    (hr : .x0 ∉ regs) : Ws t B Z w := by
  have hh : ∀ i, i ∈ [sW, sStride] ∨ (8 ≤ i ∧ i < 16) → word t.mem B (8 * i) = word s.mem B (8 * i) := by
    intro i hi
    have hi' : i = 6 ∨ (8 ≤ i ∧ i < 16) ∨ i = 28 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, sW, sStride, sFn] at hi; omega
    exact hf.word_eq (fun r hr => by
      have := hm r hr
      simp only [KMut, sW, sMinv, sArr, sStride, sFn] at this
      omega)
      (by have := h.scr.nowrap; have := hdr_lt_slot w 16 (show 31 < 32 by decide); have := h.hZ; omega)
  exact ⟨h.scr.congr k.wr, (k.gpr .x0 hr).trans h.x0, (hh sW (.inl (by simp))).trans h.hw,
    (hh sStride (.inl (by simp))).trans h.hS, fun j hj => (hh (sArr j) (.inr (by unfold sArr; omega))).trans (h.harr j hj),
    h.hZ, h.w1, h.w2⟩

/-- The working space keeps `Ws` across changes in arrays only. -/
theorem _root_.VG.Proof.Rsa.AArch64.Ws.congrA {s t : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {js : List Nat}
    (ha : Arrays B w js s.mem t.mem) {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) : Ws t B Z w :=
  h.congr' (Frm.of_arrays (rs := js.map fun j => (slot w j, 8 * (w + 2))) ha fun _ hj => List.mem_map_of_mem hj) (fun r hr => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hr; exact KMut.ofSlot w j _) k hr

/-- `cbz` on a register holding a small number. -/
theorem ofNat64_beq_zero {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n == 0) = decide (n = 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hp
  · rfl
  · have : BitVec.ofNat 64 n ≠ 0 := fun e => by
      have := congrArg BitVec.toNat e; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this; simp at this; omega
    rw [show (BitVec.ofNat 64 n == 0) = false from beq_eq_false_iff_ne.mpr this]
    exact (decide_eq_false (by omega)).symm

/-! ## Instructions -/

section
variable {s : State}

theorem exec_mul_w {d n m : Reg} :
    exec (.mul .w d n m) s = some (s.write .w d ((s.gpr n).setWidth 32 * (s.gpr m).setWidth 32)) := rfl

theorem exec_addImm_w {d n : Reg} {imm : Nat} (h : imm < 4096) :
    exec (.addImm .w d n imm) s = some (s.write .w d ((s.gpr n).setWidth 32 + BitVec.ofNat 32 imm)) := by
  simp [exec, h, State.read]

theorem exec_movz_x' {d : Reg} {imm : BitVec 16} {hw : Nat} (h : hw < 4) :
    exec (.movz .x d imm hw) s = some (s.write .x d (imm.setWidth 64 <<< (16 * hw))) := by
  simp only [exec, Size.bits, show 16 * hw < 64 by omega, ite_true]

theorem exec_movk_x {d : Reg} {imm : BitVec 16} {hw : Nat} (h : hw < 4) :
    exec (.movk .x d imm hw) s = some (s.write .x d ((s.gpr d &&& ~~~((0xFFFF : BitVec 64) <<< (16 * hw))) |||
      (imm.setWidth 64 <<< (16 * hw)))) := by
  simp only [exec, Size.bits, show 16 * hw < 64 by omega, ite_true, State.read, BitVec.setWidth_eq]

end

end VG.Proof.RsaKeyGen.AArch64
