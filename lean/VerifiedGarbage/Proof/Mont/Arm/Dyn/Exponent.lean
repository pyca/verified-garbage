module

public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Context
import VerifiedGarbage.Proof.Mont.Arm.Dyn.ExponentParts
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Csub
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ws
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Zeros
import VerifiedGarbage.Proof.Mont.Arm.Csub
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Mont.Arm.Dyn.PowerTwo

/-! ### `Mont.Arm.Dyn.ExponentProduct`, which only this module used -/

section

/-! ### `Mont.Arm.Dyn.Select`, which only this module used -/

section

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
  refine WP.seq (wp_ptr (d := .r10) (by decide) (by omega_using [h16s]) fun s₁ u₁ =>
    wp_ptr (d := .r8) (by decide) (by omega_using [h16t]) fun s₂ u₂ =>
    wp_ptr (d := .r1) (by decide) (by omega_using [h16o]) fun s₃ u₃ =>
    wp_ptr (d := .r9) (by decide) (by omega_using [h16s]) fun t u₄ => WP.block_nil ?_)
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
    (by decide) hk (by omega_using [h16s]) (fun j u u' ⟨a, c, d, e, f, g⟩ F => ⟨a.of_fupd F, c.trans (F.rest _),
      by rw [F.gpr]; exact d, by rw [F.gpr]; exact e, by rw [F.mem]; exact f, by rw [F.mem]; exact g⟩)
    ⟨wt, R, by rw [p8]; exact (BitVec.add_zero _).symm, by rw [p1]; exact (BitVec.add_zero _).symm,
      fun i hi => absurd hi (Nat.not_lt_zero _), by rw [mt]; exact Outside.refl _ _ _ _⟩
    p10 (by rw [p9, Offset.add_add]) ?_ fun u ⟨a, c, _, _, f, g⟩ _ => ⟨a, f, g, c⟩
  intro j hj u ⟨wu, Ru, p8u, p1u, Vu, Ou⟩ pu p9u
  have e12 : u.gpr .r12 = s.gpr .r12 := Ru.gpr _ (by decide)
  have r3u : u.gpr .r3 = s.gpr .r3 := Ru.gpr _ (by decide)
  -- The words read are not yet written.
  have xs : w32 u.mem base (src + 4 * j + 0) = w32 s.mem base (src + 4 * j) :=
    Ou.w32 (by omega_using [hos, hj]) (by omega_using [h16s, hj])
  have xt : w32 u.mem base (tmp + 4 * j + 0) = w32 s.mem base (tmp + 4 * j) :=
    Ou.w32 (by omega_using [hot, hj]) (by omega_using [h16s, h16t, hj])
  refine wp_ldr (by decide) (wu.ea (K := src + 4 * j) (at_ptr pu e12) (by omega_using [hsrc, hj])) (wu.read (d := src + 4 * j + 0) (n := 4) (by omega_using [hsrc, hj]))
    fun u₁ v₁ => ?_
  have w₁ := wu.of_upd v₁ (by decide)
  refine wp_ldr (by decide) (w₁.ea (K := tmp + 4 * j) (at_ptr (by rw [v₁.other .r8 (by decide)]; exact p8u)
    (by rw [v₁.other .r12 (by decide)]; exact e12)) (by omega_using [htmp, hj])) (w₁.read (d := tmp + 4 * j + 0) (n := 4) (by omega_using [htmp, hj]))
    fun u₂ v₂ => wp_dp (op2_reg _ _) fun u₃ v₃ => wp_dp (op2_reg _ _) fun u₄ v₄ => wp_dp (op2_reg _ _) fun u₅ v₅ => ?_
  have w₅ : Ws u₅ base size := (((w₁.of_upd v₂ (by decide)).of_upd v₃ (by decide)).of_upd v₄ (by decide)).of_upd v₅ (by decide)
  have m5 : u₅.mem = u.mem := by rw [v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  refine wp_str (by decide) (w₅.ea (K := o + 4 * j) (at_ptr (by simp only [v₅.get, v₄.get, v₃.get, v₂.get, v₁.get, reduceCtorEq, ↓reduceIte]; exact p1u)
    (by simp only [v₅.get, v₄.get, v₃.get, v₂.get, v₁.get, reduceCtorEq, ↓reduceIte]; exact e12)) (by omega_using [hoz, hj])) (w₅.write (d := o + 4 * j + 0) (n := 4) (by omega_using [hoz, hj]))
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
    · rw [w32_write_lt (by omega_using [hoz, hn, hj]) (by omega_using [h]), Vu i h]
    · rw [show i = j by omega_using [hi, h], w32_write_self, val]
      cases b
      · exact xs
      · exact xt
  · rw [m9]
    exact (Ou.mono (Nat.le_refl _) (by omega_using [])).trans ((writeW32_outside _ _ _ (by omega_using [h16s, h16o, hj])).mono (by omega_using []) (by omega_using []))
  · simp only [v₉.get, v₈.get, v₇.get, m₆.gpr, v₅.get, v₄.get, v₃.get, v₂.get, v₁.get, reduceCtorEq, ↓reduceIte]; exact ptr_step pu
  · simp only [v₉.get, v₈.get, v₇.get, m₆.gpr, v₅.get, v₄.get, v₃.get, v₂.get, v₁.get, reduceCtorEq, ↓reduceIte]; exact p9u

end VG.Proof.Mont.Arm.Dyn

end

end


/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: the conditional product

`exponentProduct n` multiplies the result by the base where the exponent's
low bit is set (`exponentProduct_ok`): the product is always computed, and
selected under the bit's mask.
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_ldr)

/-- A context, after code that changed only header bytes past `m'` and
registers outside `dclob`'s complement. -/
theorem Context.of_outside {n size m d len : Nat} {base : Addr} {s t : State} (h : Context n m base size s)
    (w : Ws t base size) (O : Outside base d len s.mem t.mem) (hd : 4 ≤ d) (hl : d + len ≤ 256) :
    Context n m base size t := by
  have h0 := slot_header n 0
  have nw := h.ws.nowrap
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have sz := h.size_le
  refine ⟨w, h.size_le, h.small, h.n0, ?_, h.gt_one, ?_⟩
  · rw [O.val32 (by omega_using [hl, h0]) (by simp only [stride] at b0; omega_using [nw, b0, sz])]; exact h.modulus
  · rw [O.w32 (by simp only [invO]; omega_using [hd]) (by decide)]; exact h.inverse

/-- The memory the conditional product changes. -/
def productRanges (n : Nat) : List (Nat × Nat) :=
  [(maskO, 4), (slot n 10, 8 * n), (slot n 9, 8 * n), (slot n 1, 8 * n), (slot n 2, 4 * (8 * n + 2))]

theorem exponentProduct_ok {n size m y b : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (hy : val32 s.mem base (slot n 9) (2 * n) = y * 2 ^ (64 * n) % m)
    (hb : val32 s.mem base (slot n 8) (2 * n) = b * 2 ^ (64 * n) % m) :
    WP isa (exponentProduct n) s fun t => Context n m base size t ∧
      val32 t.mem base (slot n 9) (2 * n) =
        (if w32 s.mem base (slot n 11) % 2 = 1 then y * b else y) * 2 ^ (64 * n) % m ∧
      Outs base (productRanges n) s.mem t.mem ∧ Rest dclob s t := by
  have sz := h.size_le
  have sm := h.small
  have nw := h.ws.nowrap
  have hn := h.n0
  have hm0 : 0 < m := by have := h.gt_one; omega_using [this]
  have b11 := slot_bound (n := n) (i := 11) (by decide)
  have h0 := slot_header n 0
  have h11 := slot_header n 11
  have h8 : 8 ≤ size := by omega_using [sz, b11, h11]
  have nw' : base.toNat + contextBytes n ≤ 2 ^ 32 := by omega_using [sz, nw]
  unfold exponentProduct
  refine WP.seq (WP.mono (exponentMask_ok h.ws (n := n) (by simp only [expS, stride] at *; omega_using [sz, b11])
    (by simp only [expS, stride] at *; omega_using [sm, b11]) (by omega_using [h8])) fun s₁ ⟨w₁, M₁, O₁, R₁⟩ => ?_)
  have c₁ := h.of_outside w₁ O₁ (by decide) (by decide)
  have keep₁ (i : Nat) (hi : i < 12) : val32 s₁.mem base (slot n i) (2 * n) = val32 s.mem base (slot n i) (2 * n) := by
    have hd := slot_header n i
    have bd := slot_bound (n := n) hi
    exact O₁.val32 (by simp only [maskO]; omega_using [hd]) (by simp only [stride] at bd; omega_using [sm, bd])
  have hb₁ : val32 s₁.mem base (slot n 8) (2 * n) < m := by
    rw [keep₁ 8 (by decide), hb]; exact Nat.mod_lt _ hm0
  refine WP.seq (WP.mono (context_mul_ok c₁ (o := 10) (a := 9) (b := 8) (by decide) (by decide) (by decide) hb₁)
    fun s₂ ⟨c₂, K₂, lt₂, V₂⟩ => ?_)
  have mask₂ : w32 s₂.mem base maskO = w32 s₁.mem base maskO := by
    have h1 := slot_header n 1
    have h2 := slot_header n 2
    have h10 := slot_header n 10
    have := K₂.mem.val32 (d := maskO) (k := 1) (fun r hr => by
      simp only [opRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [maskO] <;> omega_arith) (by decide)
    simpa only [val32, Nat.mul_zero, Nat.add_zero] using this
  refine WP.seq (wp_ldr (by decide) (c₂.ws.ea12 (by simp only [maskO]; omega_using [h8])) (c₂.ws.read (d := maskO) (n := 4)
    (by simp only [maskO]; omega_using [h8])) fun s₃ u₃ => WP.block_nil ?_)
  have w₃ := c₂.ws.of_upd u₃ (by decide)
  have b9 := slot_bound (n := n) (i := 9) (by decide)
  have b10 := slot_bound (n := n) (i := 10) (by decide)
  have l910 := slot_le (n := n) (i := 9) (j := 10) (by decide)
  have r3 : s₃.gpr .r3 = if decide (w32 s.mem base (slot n 11) % 2 = 1) = true then BitVec.allOnes 32 else 0 := by
    rw [u₃.gpr]
    apply BitVec.eq_of_toNat_eq
    show w32 s₂.mem base maskO = _
    rw [mask₂, M₁]
    simp only [decide_eq_true_eq, expS]
    rfl
  refine WP.mono (selectW_ok w₃ (k := 2 * n) (src := slot n 9) (tmp := slot n 10) (o := slot n 9) _ r3 (by omega_using [hn])
    (by simp only [stride] at *; omega_using [sz, b9]) (by simp only [stride] at *; omega_using [sz, b10]) (by simp only [stride] at *; omega_using [sz, b9])
    (by simp only [stride] at *; omega_using [sm, b9]) (by simp only [stride] at *; omega_using [sm, b10]) (by simp only [stride] at *; omega_using [sm, b9])
    (.inl rfl) (.inl (by simp only [stride] at *; omega_using [l910]))) fun t ⟨wt, W, O, R⟩ => ?_
  have m₃ : s₃.mem = s₂.mem := u₃.mem
  rw [m₃] at W O
  rw [show 4 * (2 * n) = 8 * n by omega_using []] at O
  refine ⟨c₂.of_slot wt O (by decide), ?_, ?_, ?_⟩
  · have vp : val32 s₂.mem base (slot n 10) (2 * n) = y * b * 2 ^ (64 * n) % m := by
      have v := VG.Proof.Dsa.mont_product h.coprime (a := y) (b := b)
        (by rw [keep₁ 9 (by decide), hy, Nat.mod_mod]) (by rw [keep₁ 8 (by decide), hb, Nat.mod_mod]) V₂
      rwa [Nat.mod_eq_of_lt lt₂] at v
    have vy : val32 s₂.mem base (slot n 9) (2 * n) = y * 2 ^ (64 * n) % m := by
      rw [K₂.val32 (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw', keep₁ 9 (by decide), hy]
    by_cases hbit : w32 s.mem base (slot n 11) % 2 = 1
    · rw [val32_move (m := s₂.mem) (d := slot n 10) fun i hi => by
        rw [W i hi]; simp only [hbit, decide_true, ↓reduceIte], vp, ite_eq_left hbit]
    · rw [val32_congr (m := s₂.mem) fun i hi => by
        rw [W i hi]; simp only [hbit, decide_false, Bool.false_eq_true, ↓reduceIte], vy, ite_eq_right hbit]
  · have l1 := slot_le (n := n) (i := 1) (j := 9) (by decide)
    have l2 := slot_le (n := n) (i := 2) (j := 9) (by decide)
    have e6 : slot n 6 = slot n 2 + 4 * stride n := by simp only [slot]; omega_using []
    have l6 := slot_le (n := n) (i := 6) (j := 9) (by decide)
    have h1 := slot_header n 1
    refine ((Outs.of_outside O₁ (by simp [productRanges])).trans (K₂.mem.mono (by simp [productRanges]))).trans
      (Outs.of_outside O (by simp [productRanges]))
  · exact ((R₁.mono (by decide)).trans K₂.rest).trans ((u₃.rest (by decide)).trans (R.mono (by decide)))

end VG.Proof.Mont.Arm.Dyn

end

end


/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: exponentiation

`exponentiate n expWords` writes `[slot 9] = [slot 8]^[slot 11] mod m`
(`exponentiate_ok`), from one in slot 6 and `R² mod m` in slot 7: the base
and one are encoded, `32 expWords` steps (`exponentStep_ok`, counted in `lr`)
each square the base and multiply the result by it under the exponent's
low bit, which they shift out, and the result is decoded.
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_movw wp_subs)

/-- The memory an exponentiation's steps change. -/
def exponentRanges (n expWords : Nat) : List (Nat × Nat) :=
  productRanges n ++ [(slot n 8, 8 * n), (slot n 11, 4 * expWords)]

theorem exponentRanges_slot {n expWords i k : Nat} {base : Addr} {s t : State}
    (O : Outs base (exponentRanges n expWords) s.mem t.mem) (hi : i = 0 ∨ i = 6 ∨ i = 7) (hk : k ≤ 2 * n)
    (hn : base.toNat + contextBytes n ≤ 2 ^ 32) :
    val32 t.mem base (slot n i) k = val32 s.mem base (slot n i) k := by
  have e6 : slot n 6 = slot n 2 + 4 * stride n := by simp only [slot]; omega_arith
  have e7 : slot n 7 = slot n 6 + stride n := by simp only [slot]; omega_arith
  have e8 : slot n 8 = slot n 7 + stride n := by simp only [slot]; omega_arith
  have l89 := slot_le (n := n) (i := 8) (j := 9) (by decide)
  have l910 := slot_le (n := n) (i := 9) (j := 10) (by decide)
  have l1011 := slot_le (n := n) (i := 10) (j := 11) (by decide)
  have l01 := slot_le (n := n) (i := 0) (j := 1) (by decide)
  have l12 := slot_le (n := n) (i := 1) (j := 2) (by decide)
  have b11 := slot_bound (n := n) (i := 11) (by decide)
  have h0 := slot_header n 0
  simp only [stride] at *
  apply O.val32
  · intro r hr
    simp only [exponentRanges, productRanges, maskO, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      at hr
    rcases hi with rfl | rfl | rfl <;> rcases hr with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl) <;> omega_arith
  · rcases hi with rfl | rfl | rfl <;> omega_arith

theorem exponentBody_ok {n size m y b expWords : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (he : 0 < expWords) (hen : expWords ≤ 2 * n) (hew : expWords ≤ 1024)
    (hy : val32 s.mem base (slot n 9) (2 * n) = y * 2 ^ (64 * n) % m)
    (hb : val32 s.mem base (slot n 8) (2 * n) = b * 2 ^ (64 * n) % m) :
    WP isa (exponentBody n expWords) s fun t => Context n m base size t ∧
      val32 t.mem base (slot n 9) (2 * n) =
        (if val32 s.mem base (slot n 11) expWords % 2 = 1 then y * b else y) * 2 ^ (64 * n) % m ∧
      val32 t.mem base (slot n 8) (2 * n) = (b * b) * 2 ^ (64 * n) % m ∧
      val32 t.mem base (slot n 11) expWords = val32 s.mem base (slot n 11) expWords / 2 ∧
      Outs base (exponentRanges n expWords) s.mem t.mem ∧ Rest dclob s t := by
  have sz := h.size_le
  have sm := h.small
  have nw := h.ws.nowrap
  have hm0 : 0 < m := by have := h.gt_one; omega_arith
  have nw' : base.toNat + contextBytes n ≤ 2 ^ 32 := by omega_arith
  have b11 := slot_bound (n := n) (i := 11) (by decide)
  have h0 := slot_header n 0
  have l811 := slot_le (n := n) (i := 8) (j := 11) (by decide)
  have l911 := slot_le (n := n) (i := 9) (j := 11) (by decide)
  have l1011 := slot_le (n := n) (i := 10) (j := 11) (by decide)
  have l111 := slot_le (n := n) (i := 1) (j := 11) (by decide)
  have e6 : slot n 6 = slot n 2 + 4 * stride n := by simp only [slot]; omega_arith
  have l611 := slot_le (n := n) (i := 6) (j := 11) (by decide)
  unfold exponentBody
  refine WP.seq (WP.mono (exponentProduct_ok h hy hb) fun s₁ ⟨c₁, Y₁, O₁, R₁⟩ => ?_)
  have B₁ : val32 s₁.mem base (slot n 8) (2 * n) = b * 2 ^ (64 * n) % m := by
    rw [← hb]
    refine O₁.val32 (fun r hr => ?_) (by simp only [stride] at *; omega_arith)
    simp only [productRanges, maskO, List.mem_cons, List.not_mem_nil, or_false] at hr
    have l89 := slot_le (n := n) (i := 8) (j := 9) (by decide)
    have l810 := slot_le (n := n) (i := 8) (j := 10) (by decide)
    have l68 := slot_le (n := n) (i := 6) (j := 8) (by decide)
    have l18 := slot_le (n := n) (i := 1) (j := 8) (by decide)
    have h1 := slot_header n 1
    simp only [stride] at *
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> omega_arith
  have E₁ : val32 s₁.mem base (slot n 11) expWords = val32 s.mem base (slot n 11) expWords := by
    refine O₁.val32 (fun r hr => ?_) (by simp only [stride] at *; omega_arith)
    simp only [productRanges, maskO, List.mem_cons, List.not_mem_nil, or_false] at hr
    have h1 := slot_header n 1
    simp only [stride] at *
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> omega_arith
  have hb₁ : val32 s₁.mem base (slot n 8) (2 * n) < m := by rw [B₁]; exact Nat.mod_lt _ hm0
  refine WP.seq (WP.mono (context_mul_ok c₁ (o := 8) (a := 8) (b := 8) (by decide) (by decide) (by decide) hb₁)
    fun s₂ ⟨c₂, K₂, lt₂, V₂⟩ => ?_)
  have E₂ : val32 s₂.mem base (slot n 11) expWords = val32 s.mem base (slot n 11) expWords := by
    rw [K₂.val32 (by decide) hen (by decide) (by decide) (.inl (by decide)) nw', E₁]
  have Y₂ : val32 s₂.mem base (slot n 9) (2 * n) =
      (if val32 s.mem base (slot n 11) expWords % 2 = 1 then y * b else y) * 2 ^ (64 * n) % m := by
    rw [K₂.val32 (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw', Y₁]
    obtain ⟨k, rfl⟩ : ∃ k, expWords = k + 1 := ⟨expWords - 1, by omega_arith⟩
    rw [val32_parity]
  -- The shift.
  have l011 := slot_le (n := n) (i := 0) (j := 11) (by decide)
  have hE : slot n 11 + 4 * expWords ≤ size := by simp only [stride] at b11; omega_using [b11, sz, hen]
  have hE16 : slot n 11 < 2 ^ 16 := by simp only [stride] at b11; omega_using [b11, sm]
  have s0 : slot n 0 + 4 * (2 * n) ≤ slot n 11 := by simp only [stride] at l011; omega_using [l011]
  have s8 : slot n 8 + 4 * (2 * n) ≤ slot n 11 := by simp only [stride] at l811; omega_using [l811]
  have s9 : slot n 9 + 4 * (2 * n) ≤ slot n 11 := by simp only [stride] at l911; omega_using [l911]
  have hE64 : slot n 11 + 4 * expWords ≤ 2 ^ 64 := by omega_using [hE, nw]
  unfold shiftExponent
  refine wp_ptr (d := .r1) (by decide) (by simp only [expS]; exact hE16) fun s₃ u₃ => ?_
  have w₃ := c₂.ws.of_upd u₃ (by decide)
  refine WP.mono (shiftWords_ok (E := expS n) expWords 0 s₃ w₃ (by rw [u₃.gpr, u₃.other .r12 (by decide)])
    (by simp only [expS]; omega_using [hE]) (by omega_using [hew])) fun t ⟨wt, O, V, R⟩ => ?_
  simp only [Nat.mul_zero, Nat.add_zero, expS] at O V
  rw [u₃.mem] at O V
  have ct : Context n m base size t := by
    refine ⟨wt, c₂.size_le, c₂.small, c₂.n0, ?_, c₂.gt_one, ?_⟩
    · rw [O.val32 (.inl s0) (by omega_using [s0, hE64])]; exact c₂.modulus
    · rw [O.w32 (by simp only [invO]; omega_using [h0, l011]) (by decide)]; exact c₂.inverse
  refine ⟨ct, ?_, ?_, ?_, ?_, ?_⟩
  · rw [O.val32 (.inl s9) (by omega_using [s9, hE64])]; exact Y₂
  · rw [O.val32 (.inl s8) (by omega_using [s8, hE64])]
    have v := VG.Proof.Dsa.mont_product h.coprime (a := b) (b := b)
      (by rw [B₁, Nat.mod_mod]) (by rw [B₁, Nat.mod_mod]) V₂
    rwa [Nat.mod_eq_of_lt lt₂] at v
  · rw [V, E₂]
  · have h1 := slot_header n 1
    exact ((O₁.mono fun r hr => List.mem_append_left _ hr).trans (K₂.mem.mono (by simp [productRanges]))).trans
      (Outs.of_outside O (by simp))
  · exact (R₁.trans K₂.rest).trans ((u₃.rest (by decide)).trans (R.mono (by decide)))

theorem exponentStep_ok {n size m y b expWords k : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (he : 0 < expWords) (hen : expWords ≤ 2 * n) (hew : expWords ≤ 1024)
    (hy : val32 s.mem base (slot n 9) (2 * n) = y * 2 ^ (64 * n) % m)
    (hb : val32 s.mem base (slot n 8) (2 * n) = b * 2 ^ (64 * n) % m)
    (hk : 0 < k) (hk32 : k < 2 ^ 32) (hc : s.gpr .lr = BitVec.ofNat 32 k) :
    WP isa (exponentStep n expWords) s fun t =>
      t.gpr .lr = BitVec.ofNat 32 (k - 1) ∧ t.z = decide (k = 1) ∧ Context n m base size t ∧
      val32 t.mem base (slot n 9) (2 * n) =
        (if val32 s.mem base (slot n 11) expWords % 2 = 1 then y * b else y) * 2 ^ (64 * n) % m ∧
      val32 t.mem base (slot n 8) (2 * n) = (b * b) * 2 ^ (64 * n) % m ∧
      val32 t.mem base (slot n 11) expWords = val32 s.mem base (slot n 11) expWords / 2 ∧
      Outs base (exponentRanges n expWords) s.mem t.mem ∧ Rest (.lr :: dclob) s t := by
  unfold exponentStep
  refine WP.seq (WP.mono (exponentBody_ok h he hen hew hy hb) fun s₁ ⟨c₁, Y, B, E, O, R⟩ => ?_)
  refine wp_subs (VG.Proof.X25519.Arm.op2_imm (encodable_lt (n := 1) (by decide))) fun t u z => WP.block_nil ?_
  have l₁ : s₁.gpr .lr = BitVec.ofNat 32 k := by rw [R.gpr .lr (by decide)]; exact hc
  refine ⟨by rw [u.gpr, l₁, ofNat_sub_one hk hk32], ?_, ⟨c₁.ws.of_upd u (by decide), c₁.size_le, c₁.small, c₁.n0,
    by rw [u.mem]; exact c₁.modulus, c₁.gt_one, by rw [u.mem]; exact c₁.inverse⟩, by rw [u.mem]; exact Y,
    by rw [u.mem]; exact B, by rw [u.mem]; exact E, by rw [u.mem]; exact O,
    (R.mono (by decide)).trans (u.rest (by decide))⟩
  rw [z, l₁, ofNat_sub_one hk hk32, VG.Proof.X25519.Arm.ofNat_beq_zero (by omega_arith)]
  simp only [decide_eq_decide]
  omega_arith

/-- The invariant of the exponentiation's loop after `i` of its `steps` steps. -/
structure ExponentInv (n size m expWords target steps i : Nat) (base : Addr) (s t : State) : Prop where
  context : Context n m base size t
  counter : t.gpr .lr = BitVec.ofNat 32 (steps - i)
  bound : val32 t.mem base (slot n 11) expWords < 2 ^ (steps - i)
  value : ∃ y b,
    val32 t.mem base (slot n 9) (2 * n) = y * 2 ^ (64 * n) % m ∧
    val32 t.mem base (slot n 8) (2 * n) = b * 2 ^ (64 * n) % m ∧
    (y * b ^ val32 t.mem base (slot n 11) expWords) % m = target
  mem : Outs base (exponentRanges n expWords) s.mem t.mem
  rest : Rest (.lr :: dclob) s t

theorem exponentLoop_ok {n size m expWords a : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (he : 0 < expWords) (hen : expWords ≤ 2 * n) (hew : expWords ≤ 1024)
    (hy : val32 s.mem base (slot n 9) (2 * n) = 2 ^ (64 * n) % m)
    (hb : val32 s.mem base (slot n 8) (2 * n) = a * 2 ^ (64 * n) % m)
    (hc : s.gpr .lr = BitVec.ofNat 32 (32 * expWords)) :
    WP isa (.loop (exponentStep n expWords) .ne) s
      (ExponentInv n size m expWords (a ^ val32 s.mem base (slot n 11) expWords % m)
        (32 * expWords) (32 * expWords) base s) := by
  let steps := 32 * expWords
  let target := a ^ val32 s.mem base (slot n 11) expWords % m
  have hspos : 0 < steps := by dsimp [steps]; omega_arith
  have init : ExponentInv n size m expWords target steps 0 base s s := by
    refine ⟨h, ?_, ?_, ⟨1, a, ?_, hb, ?_⟩, Outs.refl _ _ _, Rest.refl _ _⟩
    · simpa only [Nat.sub_zero] using hc
    · simpa only [Nat.sub_zero] using val32_lt s.mem base (slot n 11) expWords
    · simpa only [Nat.one_mul] using hy
    · simp only [Nat.one_mul]; rfl
  refine WP.loop (M := isa)
    (fun k t => ∃ i, k = steps - i ∧ i < steps ∧ ExponentInv n size m expWords target steps i base s t)
    ?_ steps s ⟨0, rfl, hspos, init⟩
  rintro k t ⟨i, rfl, hi, I⟩
  obtain ⟨y, b, Y, B, V⟩ := I.value
  refine WP.mono (exponentStep_ok I.context he hen hew Y B (by omega_arith) (by dsimp [steps] at *; omega_arith) I.counter)
    fun u ⟨count, zf, C, Y', B', E', O, K⟩ => ?_
  have next : ExponentInv n size m expWords target steps (i + 1) base s u := by
    refine ⟨C, ?_, ?_, ⟨_, _, Y', B', ?_⟩, I.mem.trans O, I.rest.trans K⟩
    · rw [count, show steps - i - 1 = steps - (i + 1) by omega_arith]
    · rw [E']
      have hp : 2 ^ (steps - i) = 2 ^ (steps - (i + 1)) * 2 := by
        rw [show steps - i = steps - (i + 1) + 1 by omega_arith, Nat.pow_succ]
      have bound := I.bound
      rw [hp] at bound
      omega_arith
    · rw [E', exponent_step_value]
      exact V
  by_cases hdone : i + 1 = steps
  · refine .inl ⟨?_, ?_⟩
    · rw [VG.Proof.X25519.Arm.eval_ne, zf, decide_eq_true (by omega_arith)]; rfl
    · change ExponentInv n size m expWords target steps steps base s u
      rw [hdone] at next
      exact next
  · refine .inr ⟨?_, steps - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, next⟩
    rw [VG.Proof.X25519.Arm.eval_ne, zf, decide_eq_false (by omega_arith)]; rfl

theorem ExponentInv.finished {n size m expWords target steps : Nat} {base : Addr} {s t : State}
    (I : ExponentInv n size m expWords target steps steps base s t) :
    val32 t.mem base (slot n 9) (2 * n) = target * 2 ^ (64 * n) % m := by
  have bound := I.bound
  simp only [Nat.sub_self, Nat.pow_zero] at bound
  have ez : val32 t.mem base (slot n 11) expWords = 0 := by omega_arith
  obtain ⟨y, b, Y, _, V⟩ := I.value
  rw [ez, Nat.pow_zero, Nat.mul_one] at V
  rw [Y, Nat.mul_mod y, V, Nat.mul_mod_mod]

theorem exponentRanges_op {n expWords o : Nat} {base : Addr} {s t : State}
    (K : OpKeep n base o s t) (ho : o = 8 ∨ o = 9) : Outs base (exponentRanges n expWords) s.mem t.mem := by
  refine K.mem.mono ?_
  intro r hr
  simp only [opRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases ho with rfl | rfl <;> rcases hr with rfl | rfl | rfl <;> simp [exponentRanges, productRanges]

/-- `[slot 9] = [slot 8]^[slot 11] mod m`, the exponent `expWords` words, from
one in slot 6 and `R² mod m` in slot 7. -/
theorem exponentiate_ok {n size m expWords : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (he : 0 < expWords) (hen : expWords ≤ 2 * n) (hew : expWords ≤ 1024)
    (hone : val32 s.mem base (slot n 6) (2 * n) = 1)
    (hr2 : val32 s.mem base (slot n 7) (2 * n) = 2 ^ (128 * n) % m) :
    WP isa (exponentiate n expWords) s fun t =>
      Context n m base size t ∧
      val32 t.mem base (slot n 9) (2 * n) =
        val32 s.mem base (slot n 8) (2 * n) ^ val32 s.mem base (slot n 11) expWords % m ∧
      Outs base (exponentRanges n expWords) s.mem t.mem ∧ Rest (.lr :: dclob) s t := by
  have hm0 : 0 < m := by have := h.gt_one; omega_arith
  have nw' : base.toNat + contextBytes n ≤ 2 ^ 32 := by have := h.ws.nowrap; have := h.size_le; omega_arith
  unfold exponentiate
  refine WP.seq (WP.mono (context_mul_ok h (o := 9) (a := 7) (b := 6) (by decide) (by decide) (by decide)
    (by rw [hone]; exact h.gt_one)) fun s₁ ⟨c₁, K₁, lt₁, V₁⟩ => ?_)
  have Y₁ : val32 s₁.mem base (slot n 9) (2 * n) = 2 ^ (64 * n) % m :=
    mont_one h.coprime lt₁ (by rw [V₁, hone, hr2, Nat.mul_one, Nat.mod_mod])
  have R₁ : val32 s₁.mem base (slot n 7) (2 * n) = 2 ^ (128 * n) % m := by
    rw [K₁.val32 (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw', hr2]
  have B₁ := K₁.val32 (i := 8) (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw'
  have E₁ := K₁.val32 (i := 11) (by decide) hen (by decide) (by decide) (.inl (by decide)) nw'
  have O₁ : val32 s₁.mem base (slot n 6) (2 * n) = 1 := by
    rw [K₁.val32 (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw', hone]
  refine WP.seq (WP.mono (context_mul_ok c₁ (o := 8) (a := 8) (b := 7) (by decide) (by decide) (by decide)
    (by rw [R₁]; exact Nat.mod_lt _ hm0)) fun s₂ ⟨c₂, K₂, lt₂, V₂⟩ => ?_)
  have B₂ : val32 s₂.mem base (slot n 8) (2 * n) = val32 s.mem base (slot n 8) (2 * n) * 2 ^ (64 * n) % m :=
    mont_encode h.coprime lt₂ (by rw [V₂, R₁, B₁])
  have Y₂ : val32 s₂.mem base (slot n 9) (2 * n) = 2 ^ (64 * n) % m := by
    rw [K₂.val32 (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw', Y₁]
  have E₂ : val32 s₂.mem base (slot n 11) expWords = val32 s.mem base (slot n 11) expWords := by
    rw [K₂.val32 (by decide) hen (by decide) (by decide) (.inl (by decide)) nw', E₁]
  have O₂ : val32 s₂.mem base (slot n 6) (2 * n) = 1 := by
    rw [K₂.val32 (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw', O₁]
  refine WP.seq (wp_movw fun s₃ u₃ => WP.block_nil ?_)
  have c₃ : Context n m base size s₃ := ⟨c₂.ws.of_upd u₃ (by decide), c₂.size_le, c₂.small, c₂.n0,
    u₃.mem ▸ c₂.modulus, c₂.gt_one, u₃.mem ▸ c₂.inverse⟩
  refine WP.seq (WP.mono (exponentLoop_ok c₃ he hen hew (u₃.mem ▸ Y₂) (u₃.mem ▸ B₂)
    (by rw [u₃.gpr, movw_ofNat (by have := c₂.small; simp only [contextBytes, slot, stride] at this; omega_arith)]))
    fun s₄ I => ?_)
  have O₄ : val32 s₄.mem base (slot n 6) (2 * n) = 1 := by
    rw [exponentRanges_slot I.mem (.inr (.inl rfl)) (Nat.le_refl _) nw', u₃.mem, O₂]
  refine WP.mono (context_mul_ok I.context (o := 9) (a := 9) (b := 6) (by decide) (by decide) (by decide)
    (by rw [O₄]; exact h.gt_one)) fun t ⟨ct, Kt, ltt, Vt⟩ => ⟨ct, ?_, ?_, ?_⟩
  · have v := VG.Proof.Dsa.mont_decode (A := val32 s₄.mem base (slot n 9) (2 * n))
      (out := val32 t.mem base (slot n 9) (2 * n)) h.coprime (by rw [I.finished, Nat.mod_mod]) (by rw [Vt, O₄])
    rw [Nat.mod_eq_of_lt ltt, Nat.mod_mod, u₃.mem, E₂] at v
    exact v
  · have o₁ := exponentRanges_op (expWords := expWords) K₁ (.inr rfl)
    have o₂ := exponentRanges_op (expWords := expWords) K₂ (.inl rfl)
    have o₃ : Outs base (exponentRanges n expWords) s₂.mem s₃.mem := u₃.mem ▸ Outs.refl _ _ _
    exact (((o₁.trans o₂).trans o₃).trans I.mem).trans (exponentRanges_op Kt (.inr rfl))
  · exact ((((K₁.rest.trans K₂.rest).mono (by decide)).trans (u₃.rest (by decide))).trans I.rest).trans
      (Kt.rest.mono (by decide))

end VG.Proof.Mont.Arm.Dyn
