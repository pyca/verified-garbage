module
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ws
public import VerifiedGarbage.Proof.Mont.Words32

import VerifiedGarbage.Proof.Mont.Arm.Dyn.Zeros
import VerifiedGarbage.Proof.Mont.Arm.Csub
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: selecting words

`selectW k src tmp o` writes `[o] = [tmp]` where the mask `r3` is all ones,
else `[src]` (`selectW_ok`); `[o]` may be `[src]`.
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_str wp_ldr wp_dp op2_imm op2_reg)

theorem selectW_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {k src tmp o : Nat} (b : Bool)
    (h3 : s.gpr .r3 = if b then BitVec.allOnes 32 else 0) (hk : 0 < k)
    (hsrc : src + 4 * k ≤ size) (htmp : tmp + 4 * k ≤ size) (hoz : o + 4 * k ≤ size)
    (h16s : src + 4 * k < 2 ^ 16) (h16t : tmp < 2 ^ 16) (h16o : o < 2 ^ 16)
    (hos : o = src ∨ o + 4 * k ≤ src ∨ src + 4 * k ≤ o) (hot : o + 4 * k ≤ tmp ∨ tmp + 4 * k ≤ o) :
    WP isa (selectW k src tmp o) s fun t => Ws t base size ∧
      (∀ j < k, w32 t.mem base (o + 4 * j) =
        if b then w32 s.mem base (tmp + 4 * j) else w32 s.mem base (src + 4 * j)) ∧
      Outside base o (4 * k) s.mem t.mem ∧ Rest [.r1, .r5, .r7, .r8, .r9, .r10] s t := by
  have hn := hs.nowrap
  unfold selectW
  refine WP.seq (wp_ptr (d := .r10) (by decide) (by omega) fun s₁ u₁ =>
    wp_ptr (d := .r8) (by decide) (by omega) fun s₂ u₂ =>
    wp_ptr (d := .r1) (by decide) (by omega) fun s₃ u₃ =>
    wp_ptr (d := .r9) (by decide) (by omega) fun t u₄ => WP.block_nil ?_)
  have R : Rest [.r1, .r5, .r7, .r8, .r9, .r10] s t :=
    (((u₁.rest (by simp)).trans (u₂.rest (by simp))).trans (u₃.rest (by simp))).trans (u₄.rest (by simp))
  have wt : Ws t base size := hs.of_rest R (by decide)
  have mt : t.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have p10 : t.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 src := by simp only [u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  have p8 : t.gpr .r8 = s.gpr .r12 + BitVec.ofNat 32 tmp := by simp only [u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  have p1 : t.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 o := by simp only [u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  have p9 : t.gpr .r9 = s.gpr .r12 + BitVec.ofNat 32 (src + 4 * k) := by simp only [u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  have r3 : t.gpr .r3 = s.gpr .r3 := R.gpr _ (by decide)
  clear u₁ u₂ u₃ u₄
  refine ptrLoop_ok (A := s.gpr .r12 + BitVec.ofNat 32 src) (step := 4) (k := k)
    (fun j u => Ws u base size ∧ Rest [.r1, .r5, .r7, .r8, .r9, .r10] s u ∧
      u.gpr .r8 = s.gpr .r12 + BitVec.ofNat 32 tmp + BitVec.ofNat 32 (4 * j) ∧
      u.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 o + BitVec.ofNat 32 (4 * j) ∧
      (∀ i < j, w32 u.mem base (o + 4 * i) =
        if b then w32 s.mem base (tmp + 4 * i) else w32 s.mem base (src + 4 * i)) ∧
      Outside base o (4 * j) s.mem u.mem)
    (by decide) hk (by omega) (fun j u u' ⟨a, c, d, e, f, g⟩ F => ⟨a.of_fupd F, c.trans (F.rest _),
      by rw [F.gpr]; exact d, by rw [F.gpr]; exact e, by rw [F.mem]; exact f, by rw [F.mem]; exact g⟩)
    ⟨wt, R, by rw [p8]; exact (BitVec.add_zero _).symm, by rw [p1]; exact (BitVec.add_zero _).symm,
      fun i hi => absurd hi (Nat.not_lt_zero _), by rw [mt]; exact Outside.refl _ _ _ _⟩
    p10 (by rw [p9, Offset.add_add]) ?_ fun u ⟨a, c, _, _, f, g⟩ _ => ⟨a, f, g, c⟩
  intro j hj u ⟨wu, Ru, p8u, p1u, Vu, Ou⟩ pu p9u
  have e12 : u.gpr .r12 = s.gpr .r12 := Ru.gpr _ (by decide)
  have r3u : u.gpr .r3 = s.gpr .r3 := Ru.gpr _ (by decide)
  -- The words read are not yet written.
  have xs : w32 u.mem base (src + 4 * j + 0) = w32 s.mem base (src + 4 * j) :=
    Ou.w32 (by omega) (by omega)
  have xt : w32 u.mem base (tmp + 4 * j + 0) = w32 s.mem base (tmp + 4 * j) :=
    Ou.w32 (by omega) (by omega)
  refine wp_ldr (by decide) (wu.ea (K := src + 4 * j) (at_ptr pu e12) (by omega)) (wu.read (d := src + 4 * j + 0) (n := 4) (by omega))
    fun u₁ v₁ => ?_
  have w₁ := wu.of_upd v₁ (by decide)
  refine wp_ldr (by decide) (w₁.ea (K := tmp + 4 * j) (at_ptr (by rw [v₁.other .r8 (by decide)]; exact p8u)
    (by rw [v₁.other .r12 (by decide)]; exact e12)) (by omega)) (w₁.read (d := tmp + 4 * j + 0) (n := 4) (by omega))
    fun u₂ v₂ => wp_dp (op2_reg _ _) fun u₃ v₃ => wp_dp (op2_reg _ _) fun u₄ v₄ => wp_dp (op2_reg _ _) fun u₅ v₅ => ?_
  have w₅ : Ws u₅ base size := (((w₁.of_upd v₂ (by decide)).of_upd v₃ (by decide)).of_upd v₄ (by decide)).of_upd v₅ (by decide)
  have m5 : u₅.mem = u.mem := by rw [v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  refine wp_str (by decide) (w₅.ea (K := o + 4 * j) (at_ptr (by simp only [v₅.get, v₄.get, v₃.get, v₂.get, v₁.get, reduceCtorEq, ↓reduceIte]; exact p1u)
    (by simp only [v₅.get, v₄.get, v₃.get, v₂.get, v₁.get, reduceCtorEq, ↓reduceIte]; exact e12)) (by omega)) (w₅.write (d := o + 4 * j + 0) (n := 4) (by omega))
    fun u₆ m₆ => wp_bump (by decide) fun u₇ v₇ => wp_bump (by decide) fun u₈ v₈ => wp_bump (by decide) fun u₉ v₉ =>
      WP.block_nil ?_
  have m9 : u₉.mem = u.mem.writeW (off base (o + 4 * j)) (u₅.gpr .r5) := by
    rw [v₉.mem, v₈.mem, v₇.mem, m₆.mem, m5, Nat.add_zero]
  have val : u₅.gpr .r5 = if b then u.mem.readW (off base (tmp + 4 * j + 0)) 32
      else u.mem.readW (off base (src + 4 * j + 0)) 32 := by
    simp only [v₅.get, v₄.get, v₃.get, v₂.get, v₁.get, reduceCtorEq, ↓reduceIte, VG.Proof.X25519.Arm.dpVal, r3u, h3]
    rw [v₁.mem, select_val]
  refine ⟨⟨((w₅.of_mupd m₆).of_upd v₇ (by decide) |>.of_upd v₈ (by decide)).of_upd v₉ (by decide),
    ⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h5, h7, h8, h9, h10⟩ := hr
    simp only [v₉.get, v₈.get, v₇.get, m₆.gpr, v₅.get, v₄.get, v₃.get, v₂.get, v₁.get, h1, h5, h7, h8, h10, ↓reduceIte]; exact Ru.gpr r (by simp [h1, h5, h7, h8, h9, h10])
  · rw [v₉.rd, v₈.rd, v₇.rd, m₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd]; exact Ru.rd
  · rw [v₉.wr, v₈.wr, v₇.wr, m₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr]; exact Ru.wr
  · rw [v₉.sp, v₈.sp, v₇.sp, m₆.sp, v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp]; exact Ru.sp
  · simp only [v₉.get, v₈.get, v₇.get, m₆.gpr, v₅.get, v₄.get, v₃.get, v₂.get, v₁.get, reduceCtorEq, ↓reduceIte]; exact ptr_step p8u
  · simp only [v₉.get, v₈.get, v₇.get, m₆.gpr, v₅.get, v₄.get, v₃.get, v₂.get, v₁.get, reduceCtorEq, ↓reduceIte]; exact ptr_step p1u
  · intro i hi
    rw [m9]
    rcases Nat.lt_or_ge i j with h | h
    · rw [w32_write_lt (by omega) (by omega), Vu i h]
    · rw [show i = j by omega, w32_write_self, val]
      cases b
      · exact xs
      · exact xt
  · rw [m9]
    exact (Ou.mono (Nat.le_refl _) (by omega)).trans ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega))
  · simp only [v₉.get, v₈.get, v₇.get, m₆.gpr, v₅.get, v₄.get, v₃.get, v₂.get, v₁.get, reduceCtorEq, ↓reduceIte]; exact ptr_step pu
  · simp only [v₉.get, v₈.get, v₇.get, m₆.gpr, v₅.get, v₄.get, v₃.get, v₂.get, v₁.get, reduceCtorEq, ↓reduceIte]; exact p9u

end VG.Proof.Mont.Arm.Dyn
