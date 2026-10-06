import VerifiedGarbage.Proof.X448.Arm.Finish
import VerifiedGarbage.Proof.X448.Arm.Inv
import VerifiedGarbage.Proof.Ed448.Ref
import VerifiedGarbage.Impl.Ed448.Arm.ScalarBase

/-!
# Ed448 base-point multiplication on ARMv7: the encoding

`baseEncode`: `Z` inverted into slot 21, `y = Y/Z` into slot 4 and
`x = X/Z` into slot 1; `x` fully reduced and its low bit kept in `r8`; `y`
copied into slot 1, fully reduced and written to the output's first 56
bytes, and the bit as the top bit of its 57th (RFC 8032 §5.2.2); then the
callee-saved registers restored (`baseEncode_ok`). The 57 bytes are
`encodePoint` of the point in slots 0–2 (`Proof.Ed448.encodePoint_code`).
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm VG.Proof.X448.Radix16
open VG.Impl.X448.Arm (slot X2 ACC ld saved)
open VG.Spec.Ed448 (bytesAt)

theorem invEnv_x0 (e : Env) : invEnv e 0 = e 0 := rfl

theorem bytesAt_57 (m : Mem) (q : Addr) :
    bytesAt m q 57 = Spec.X448.bytesAt m q 56 ++ [m (q + BitVec.ofNat 64 56)] := by
  simp only [bytesAt, Spec.X448.bytesAt, show 57 = 56 + 1 from rfl, List.range_succ, List.map_append,
    List.map_cons, List.map_nil]

/-- `r8 = 128 · (limb 0 of slot 1 mod 2)`. -/
theorem signBit_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block signBit) s fun t =>
      (t.gpr .r8).toNat = 128 * (limbs s.mem base X2 0 % 2) ∧ t.mem = s.mem ∧ Keeps [.r8] s t := by
  unfold signBit
  refine load_ok hs (by decide) fun u hu => ?_
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun v hv => ?_
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_lsl (by decide)) fun t ht =>
    WP.block_nil ⟨?_, by rw [ht.mem, hv.mem, hu.mem], rest_keeps ((hu.rest (by decide)).trans
      ((hv.rest (by decide)).trans (ht.rest (by decide))))⟩
  have h1 : (v.gpr .r8).toNat = limbs s.mem base X2 0 % 2 := by
    rw [hv.gpr]; change (u.gpr .r8 &&& 1#32).toNat = _
    rw [BitVec.toNat_and, show (1#32).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, hu.gpr]
    rfl
  rw [ht.gpr, VG.Proof.X25519.Arm.toNat_shl, h1, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The value of slot 1 mod 2 is its limb 0's. -/
theorem fe_mod2 (m : Mem) (base : Addr) : fe m base X2 % 2 = limbs m base X2 0 % 2 := by
  have h : ∀ n, valN (limbs m base X2) (n + 1) % 2 = limbs m base X2 0 % 2 := by
    intro n
    induction n with
    | zero => simp [valN]
    | succ n ih =>
      have e : (2 ^ 16) ^ (n + 1) * limbs m base X2 (n + 1) =
          2 * ((2 ^ 16) ^ n * 2 ^ 15 * limbs m base X2 (n + 1)) := by
        rw [Nat.pow_succ]; grind
      rw [valN_succ, Nat.add_mod, ih, radix, e, Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod]
  exact h 27

theorem byte56_write (m : Mem) (q : Addr) (v : Byte) :
    (m.writeW (q + BitVec.ofNat 64 56) v) (q + BitVec.ofNat 64 56) = v := by
  simp [Mem.writeW, Mem.write]

theorem bytes56_write {m : Mem} {q : Addr} (v : Byte) :
    Spec.X448.bytesAt (m.writeW (q + BitVec.ofNat 64 56) v) q 56 = Spec.X448.bytesAt m q 56 := by
  simp only [Spec.X448.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff _ q (by omega), Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  omega

def encodeFields : List FieldOp := [.mul 4 1 21, .mul 1 0 21]

theorem encodeFields_impl :
    encodeFields.map FieldOp.impl = [.mul (slot 4) (slot 1) (slot 21), .mul X2 (slot 0) (slot 21)] := by
  decide +kernel

/-- A word of the working space is beyond the output. -/
theorem far57 {base q : Addr} (hd : (⟨q, 57⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < 8192) : 57 ≤ ofs q (off base i) := by
  refine Nat.le_of_not_lt fun h => hd _ ?_
    (Offset.contains_base base (d := i) (n := 1) (k := 8192) (by omega) (by omega))
  simp only [Region.Contains]
  change ofs q (off base i) + 1 ≤ 57
  omega

/-- The registers the encoding may change. -/
def encRegs : List Reg := [.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

theorem baseEncode_ok {s : State} {base q : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    (hq : State.addr (s.gpr .r12) = q) (hfit : (s.gpr .r12).toNat + 57 ≤ 2 ^ 32)
    (hw : (⟨q, 57⟩ : Region) ∈ s.wr) (hd : (⟨q, 57⟩ : Region).Disjoint ⟨base, 8192⟩)
    {g : Reg → BitVec 32} (sv : Saved base g s.mem) :
    WP isa baseEncode s fun t =>
      bytesAt t.mem q 57 = Spec.Ed448.encodePoint ⟨E s.mem base 0, E s.mem base 1, E s.mem base 2⟩ ∧
      (∀ i < 8, t.gpr (saved[i]!) = g (saved[i]!)) ∧ Keeps encRegs s t ∧
      Frame [⟨base, 8192⟩, ⟨q, 57⟩] s.mem t.mem := by
  have hfar56 : ∀ j < 8192, 56 ≤ ofs q (off base j) := fun j hj => Nat.le_trans (by decide) (far57 hd hj)
  have hw56 : ∀ j < 57, InRegions s.wr (off q j) 1 := fun j hj =>
    ⟨_, hw, Offset.contains_base _ (by omega) (by omega)⟩
  unfold baseEncode
  refine WP.seq (WP.mono (invert_ok hs hb) fun s₁ ⟨k₁, b₁, e₁⟩ => ?_)
  have hs₁ := k₁.scr hs
  rw [← encodeFields_impl]
  refine WP.seq (WP.mono (ops_ok hs₁ b₁ encodeFields) fun s₂ ⟨k₂, b₂, e₂⟩ => ?_)
  have hs₂ := k₂.scr hs₁
  have ex : E s₂.mem base 1 = E s.mem base 0 * Proof.X448.invert (E s.mem base 2) := by
    rw [e₂, e₁]
    simp only [applyOps, encodeFields, FieldOp.apply, opMul, Function.update_self]
    rw [Function.update_of_ne (show (21 : Index) ≠ 4 by decide),
      Function.update_of_ne (show (0 : Index) ≠ 4 by decide), invEnv_x0, invEnv_eval]
  have ey : E s₂.mem base 4 = E s.mem base 1 * Proof.X448.invert (E s.mem base 2) := by
    rw [e₂, e₁]
    simp only [applyOps, encodeFields, FieldOp.apply, opMul]
    rw [Function.update_of_ne (show (4 : Index) ≠ 1 by decide), Function.update_self, invEnv_x2,
      invEnv_eval]
  simp only [List.append_assoc]
  -- `x` fully reduced, and its bit.
  refine VG.Proof.X25519.Arm.WP.append (freeze_ok hs₂ (b₂ 1)) fun s₃ ⟨bx₃, vx₃, m₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  refine VG.Proof.X25519.Arm.WP.append (signBit_ok hs₃) fun s₄ ⟨r₄, m₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have hx : (E s₂.mem base 1).val = fe s₂.mem base X2 % Spec.X448.P := Proof.X448.toFe_val _
  have bit : (s₄.gpr .r8).toNat = 128 * ((E s.mem base 0 * Proof.X448.invert (E s.mem base 2)).val % 2) := by
    rw [r₄, ← fe_mod2, vx₃, ← hx, ex]
  have E₄ : E s₄.mem base = E s₂.mem base := by
    rw [m₄, E_update (o := 1) m₃]
    funext i
    by_cases hi : i = 1
    · subst hi; rw [Function.update_self]
      change Proof.X448.toFe (fe s₃.mem base X2) = Proof.X448.toFe (fe s₂.mem base X2)
      rw [vx₃]; exact Proof.X448.toFe_mod _
    · rw [Function.update_of_ne hi]
  have b₄ : BoundedEnv s₄.mem base := m₄ ▸ bounded_update (o := 1) m₃ b₂ bx₃
  -- `y` into slot 1, fully reduced.
  refine VG.Proof.X25519.Arm.WP.append (copyE hs₄ b₄ 1 4) fun s₅ ⟨k₅, b₅, e₅⟩ => ?_
  have hs₅ := k₅.scr hs₄
  refine VG.Proof.X25519.Arm.WP.append (freeze_ok hs₅ (b₅ 1)) fun s₆ ⟨by₆, vy₆, m₆, k₆⟩ => ?_
  have hs₆ := hs₅.of_keeps k₆ (by decide)
  have y₆ : fe s₆.mem base X2 = (E s.mem base 1 * Proof.X448.invert (E s.mem base 2)).val := by
    have hy : (E s₅.mem base 1).val = fe s₅.mem base X2 % Spec.X448.P := Proof.X448.toFe_val _
    have h5 : E s₅.mem base 1 = E s₄.mem base 4 := by
      rw [e₅]; exact Function.update_self _ _ _
    rw [vy₆, ← hy, h5, E₄, ey]
  -- The output.
  have r12₆ : s₆.gpr .r12 = s.gpr .r12 := by
    rw [k₆.1 _ (by decide), k₅.regs.1 _ (by decide), k₄.1 _ (by decide), k₃.1 _ (by decide),
      k₂.regs.1 _ (by decide), k₁.regs.1 _ (by decide)]
  have wr₆ : s₆.wr = s.wr := by
    rw [k₆.2.2, k₅.regs.2.2, k₄.2.2, k₃.2.2, k₂.regs.2.2, k₁.regs.2.2]
  refine VG.Proof.X25519.Arm.WP.append (output_ok (p := q) hs₆ by₆ (by rw [r12₆]; exact hq)
    (by rw [r12₆]; omega) (fun j hj => by rw [wr₆]; exact hw56 j (by omega)) hfar56)
    fun s₇ ⟨v₇, o₇, k₇⟩ => ?_
  have r8₇ : s₇.gpr .r8 = s₄.gpr .r8 := by
    rw [k₇.1 _ (by decide), k₆.1 _ (by decide), k₅.regs.1 _ (by decide)]
  refine VG.Proof.X25519.Arm.wp_strb (a := q + BitVec.ofNat 64 56) (by decide)
    (by rw [k₇.1 _ (by decide), r12₆]; rw [VG.Arm.addr_add (by omega), hq])
    (by rw [k₇.2.2, wr₆]; exact hw56 56 (by decide)) fun s₈ u₈ => ?_
  -- The saved registers.
  have sv₂ : Saved base g s₂.mem := (sv.outside2 k₁.mem (by decide) (by decide)).outside2 k₂.mem
    (by decide) (by decide)
  have sv₄ : Saved base g s₄.mem := m₄ ▸ sv₂.field m₃ (by decide)
  have sv₆ : Saved base g s₆.mem := (sv₄.outside2 k₅.mem (by decide) (by decide)).field m₆ (by decide)
  have o₈ : Outside q 0 57 s₆.mem s₈.mem := by
    refine (o₇.mono (by decide) (by decide)).trans fun x hx => ?_
    rw [u₈.mem]
    exact writeW8_outside _ _ _ (d := 56) (by decide) (by omega)
  have w₈ : ∀ d, d + 4 ≤ 8192 → word s₈.mem base d = word s₆.mem base d := fun d hd4 =>
    Mem.readW_congr fun i hi => by
      rw [Offset.add_add]
      exact o₈ _ (Or.inr (far57 hd (i := d + i) (by omega)))
  have sv₈ : Saved base g s₈.mem := fun i hi => (w₈ _ (by omega)).trans (sv₆ i hi)
  have hs₈ : Scr s₈ base := hs₆.of_keeps (k₇.trans (rest_keeps (u₈.rest clob))) (by decide)
  refine WP.mono (restore_ok hs₈ sv₈) fun t ⟨rt, mt, kt⟩ => ?_
  refine ⟨?_, rt, ?_, ?_⟩
  · rw [mt, bytesAt_57, u₈.mem, bytes56_write, byte56_write, v₇, y₆, r8₇, Proof.Ed448.encodePoint_code]
    refine congrArg (fun b => _ ++ [b]) ?_
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, bit]
  · refine (k₁.regs.mono ?_).trans ((k₂.regs.mono ?_).trans ((k₃.mono ?_).trans ((k₄.mono ?_).trans
      ((k₅.regs.mono ?_).trans ((k₆.mono ?_).trans ((k₇.mono ?_).trans
      ((rest_keeps (u₈.rest encRegs)).trans (kt.mono ?_))))))))
    all_goals intro r hr; revert r; decide
  · have fw : Outside base 0 8192 s.mem s₆.mem :=
      (((((k₁.mem.whole (by decide) (by decide)).trans (k₂.mem.whole (by decide) (by decide))).trans
        (m₃.whole (by decide))).trans (by rw [m₄]; exact Outside.refl _ _ _ _)).trans
        (k₅.mem.whole (by decide) (by decide))).trans (m₆.whole (by decide))
    rw [mt]
    exact ((Outside.frame fw).mono (by simp)).trans ((Outside.frame o₈).mono (by simp))

end VG.Proof.Ed448.Arm
