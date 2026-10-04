import VerifiedGarbage.Proof.Ed448.AArch64.BaseField
import VerifiedGarbage.Proof.X448.AArch64.Weak.Main

/-!
# Ed448 base-point multiplication on AArch64: the encoding

`encode`, for `R = (X : Y : Z)` in slots 0–2: `Z` inverted into slot 21 (X448's
addition chain, `invert_ok`); `Y` kept in slot 3 and `x = X/Z` fully reduced in
`X2` (slot 1), its low bit stored as the top bit of the output's byte 56;
then `Y` back in `X2`, and X448's `finish` writes `Y/Z` fully reduced to the
output's first 56 bytes and restores `x19` and `x20`. Together, the 57 bytes
are `encodePoint R` (`encodePoint_code`).
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keep Keeps off word limbs Outside Outside2 Saved ofs workRegs
  write1_eq writeW8_apply)
open VG.Proof.X448.AArch64.Weak (E F BoundedEnv FieldOp applyOps opMul opCopy invEnv invEnv_eval
  invEnv_x2 invert_ok ops_ok IKeep)
open VG.Impl.X448.AArch64 (ld st slot X2 ACC TMP)

/-- `x` of slot 0 survives the inversion's addition chain. -/
theorem invEnv_x1 (e : Fin 22 → Spec.X448.Fe) : invEnv e 0 = e 0 := rfl

theorem signByte_val (w : BitVec 64) :
    (((w <<< 63) >>> 56).setWidth 32).setWidth 8 = BitVec.ofNat 8 (128 * (w.toNat % 2)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.reducePow]
  have := w.isLt
  omega

/-- The top bit of byte 56 of the output: the low bit of `X2`'s first word. -/
theorem signByte_ok {s : State} {base p : Addr} (hs : Scr s base) (hp : s.gpr .x1 = p)
    (hw : InRegions s.wr (p + BitVec.ofNat 64 56) 1) :
    WP isa (.block ([ld .x4 X2, .lsl .x .x4 .x4 63, .lsr .x .x4 .x4 56, .strb .x4 .x1 56] : List Instr)) s
      fun t => t.mem = s.mem.writeW (p + BitVec.ofNat 64 56)
          (BitVec.ofNat 8 (128 * ((word s.mem base X2).toNat % 2))) ∧ Keeps [.x4] s t := by
  have hr := hs.read (d := X2) (n := 8) (by decide)
  have enc : X2 % 8 = 0 ∧ X2 < 4096 * 8 := by decide
  have enc1 : (56 : Nat) % 1 = 0 ∧ (56 : Nat) < 4096 * 1 := by decide
  apply WP.of_runBlock
  simp only [ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, Size.bits,
    State.load, State.store, State.read, enc, enc1, and_self, BitVec.setWidth_eq, hs.x3, hp, hr, hw,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, Nat.reduceLT, Nat.reduceMul,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    VG.Proof.X448.AArch64.read8_eq, write1_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, (fun r hr => ?_), rfl, rfl⟩
  · rw [signByte_val]
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]

/-- A legacy slot (sixteen limbs below `2^28`) is a weak one. -/
theorem bounded_of_legacy {m : Mem} {base : Addr} {o : Nat} (h : VG.Proof.X448.AArch64.Bounded m base o) :
    VG.Proof.Curve448.AArch64.Bounded m base o := fun i hi =>
  Nat.lt_trans (h i (by omega)) (by decide)

/-- The low bit of sixteen 28-bit limbs is that of the first. -/
theorem valN_mod_two (f : Nat → Nat) : VG.Proof.X448.valN f 16 % 2 = f 0 % 2 := by
  rw [show (16 : Nat) = 1 + 15 from rfl, VG.Proof.X448.valN_split]
  simp only [VG.Proof.X448.valN, VG.Proof.X448.radix, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.pow_one]
  omega

theorem bytesAt_57 (m : Mem) (p : Addr) :
    Spec.Ed448.bytesAt m p 57 = Spec.X448.bytesAt m p 56 ++ [m (p + BitVec.ofNat 64 56)] := by
  rw [VG.Proof.Ed448.bytesAt_eq]
  simp only [Spec.X25519.bytesAt, Spec.X448.bytesAt, List.range_succ, List.map_append, List.map_cons,
    List.map_nil]

/-- `encode`: the 57 bytes at `p` are the encoding of `R` (slots 0–2), and
`x19` and `x20` are restored from the working space. -/
theorem encode_ok {s : State} {base p : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    (hp : s.gpr .x1 = p) (hw : ∀ j < 57, InRegions s.wr (off p j) 1)
    (hpd : ∀ j < 57, 8192 ≤ ofs base (off p j)) (hfar : ∀ j < 8192, 57 ≤ ofs p (off base j))
    {g : Reg → BitVec 64} (sv : Saved base g s.mem) :
    WP isa encode s fun t =>
      t.gpr .x19 = g .x19 ∧ t.gpr .x20 = g .x20 ∧ Keeps (.x19 :: .x20 :: workRegs) s t ∧
      Frame [⟨base, 8192⟩, ⟨p, 57⟩] s.mem t.mem ∧
      Spec.Ed448.bytesAt t.mem p 57 = Spec.Ed448.encodePoint (pt (E s.mem base) 0 1 2) := by
  -- Memory beyond the working space, and the output's byte 56.
  have far56 : 8192 ≤ ofs base (p + 56#64) := hpd 56 (by decide)
  have fr : ∀ {m m' : Mem}, Outside base 0 8192 m m' → Frame [⟨base, 8192⟩, ⟨p, 57⟩] m m' :=
    fun h => (VG.Proof.X448.AArch64.Outside.frame h).mono (by simp)
  rw [encode]
  refine WP.seq (WP.mono (invert_ok hs hb) fun s1 ⟨k1, b1, e1⟩ => ?_)
  have hs1 := k1.scr hs
  rw [sign]
  refine WP.seq (WP.seq (WP.mono (show WP isa (Impl.X448.AArch64.Weak.ops
      [.copy (slot 3) (slot 1), .mul (slot 1) (slot 0) (slot 21)]) s1 _ from
      ops_ok hs1 b1 [FieldOp.copy 3 1, FieldOp.mul 1 0 21]) fun s2 ⟨k2, b2, e2⟩ => ?_))
  have hs2 := k2.scr hs1
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.toLegacy_ok hs2 (o := X2) (by decide) (by decide) (b2 1))
    fun s3 ⟨k3, l3, v3⟩ => ?_
  have hs3 := hs2.of_keeps k3.keeps (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.freeze_ok hs3 l3) fun s4 ⟨l4, v4, m4, k4⟩ => ?_
  have hs4 := hs3.of_keeps k4 (by decide)
  have p4 : s4.gpr .x1 = p := by
    rw [k4.1 _ (by decide), k3.keeps.1 _ (by decide), k2.regs.1 _ (by decide), k1.regs.1 _ (by decide)]
    exact hp
  have w4 : s4.wr = s.wr := by rw [k4.2.2, k3.keeps.2.2, k2.regs.2.2, k1.regs.2.2]
  refine WP.mono (signByte_ok hs4 p4 (by rw [w4]; exact hw 56 (by decide))) fun s5 ⟨m5, k5⟩ => ?_
  have hs5 := hs4.of_keeps k5 (by decide)
  -- `s2` to `s5` changed only `X2` (slot 1), the coefficients and byte 56 of the output.
  have o25 : VG.Proof.X448.AArch64.FieldMem base X2 s2.mem s4.mem := k3.mem.trans m4
  have m45 : ∀ x, ofs base x < 8192 → s5.mem x = s4.mem x := fun x hx => by
    rw [m5, writeW8_apply, ite_eq_right_iff.mpr]
    intro h; subst h; exact absurd far56 (by omega)
  have l25 : ∀ i : Fin 22, i ≠ 1 → ∀ j < 16, limbs s5.mem base (slot i.val) j = limbs s2.mem base (slot i.val) j := by
    intro i hi j hj
    have hsep := VG.Proof.X448.AArch64.Weak.slot_sep hi
    have hi22 := i.isLt
    have hne : i.val ≠ 1 := fun h => hi (Fin.ext h)
    rw [← o25.limbs (d := slot i.val) (by simp only [X2, slot]; omega) (by simp only [slot, ACC]; omega) hj]
    exact congrArg BitVec.toNat (Mem.readW_congr fun k hk => (m45 _ (by
      simp only [ofs]
      rw [Offset.add_add, Mem.sub_ofNat_toNat base (by simp only [slot]; omega)]
      simp only [slot]; omega)).symm).symm
  have e25 : ∀ i : Fin 22, i ≠ 1 → E s5.mem base i = E s2.mem base i := fun i hi =>
    congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr fun j hj => l25 i hi j (by omega))
  have w45 : ∀ d, d + 8 ≤ 8192 → word s5.mem base d = word s4.mem base d := fun d hd =>
    Mem.readW_congr fun k hk => m45 _ (by
      simp only [ofs]
      rw [Offset.add_add, Mem.sub_ofNat_toNat base (by omega)]
      omega)
  have b5 : BoundedEnv s5.mem base := by
    intro i j hj
    by_cases hi : i = 1
    · subst hi
      have := bounded_of_legacy l4 j hj
      change (word s5.mem base (X2 + 8 * j)).toNat < _
      rw [w45 _ (by simp only [X2, slot]; omega)]
      exact this
    · rw [show limbs s5.mem base (slot i.val) j = limbs s2.mem base (slot i.val) j from l25 i hi j (by omega)]
      exact b2 i j hj
  -- `Y` back in `X2`.
  refine WP.seq (WP.mono (show WP isa (Impl.X448.AArch64.Weak.ops [.copy X2 (slot 3)]) s5 _ from
    ops_ok hs5 b5 [FieldOp.copy 1 3]) fun s6 ⟨k6, b6, e6⟩ => ?_)
  have hs6 := k6.scr hs5
  have p6 : s6.gpr .x1 = p := by rw [k6.regs.1 _ (by decide), k5.1 _ (by decide)]; exact p4
  have w6 : s6.wr = s.wr := by rw [k6.regs.2.2, k5.2.2]; exact w4
  have sv5 : Saved base g s5.mem := by
    have sv4 : Saved base g s4.mem :=
      ((sv.outside2 k1.mem (by decide) (by decide)).outside2 k2.mem (by decide) (by decide)).field o25
        (by decide)
    exact ⟨(w45 0 (by decide)).trans sv4.1, (w45 8 (by decide)).trans sv4.2⟩
  refine WP.mono (VG.Proof.X448.AArch64.Weak.finish_ok hs6 b6 p6
    (fun j hj => by rw [w6]; exact hw j (by omega)) (fun j hj => Nat.le_trans (by decide) (hfar j hj))
    (sv5.outside2 k6.mem (by decide) (by decide))) fun t ⟨t19, t20, kt, ft, vt⟩ => ?_
  -- The values.
  have x1 : E s2.mem base 1 = E s.mem base 0 * Proof.X448.invert (E s.mem base 2) := by
    rw [e2, ← invEnv_eval, ← invEnv_x1 (E s.mem base), ← e1]; rfl
  have y6 : E s6.mem base 1 = E s.mem base 1 := by
    rw [e6, show applyOps [FieldOp.copy 1 3] (E s5.mem base) 1 = E s5.mem base 3 from rfl,
      e25 3 (by decide), e2, ← invEnv_x2 (E s.mem base), ← e1]; rfl
  have i6 : E s6.mem base 21 = Proof.X448.invert (E s.mem base 2) := by
    rw [e6, show applyOps [FieldOp.copy 1 3] (E s5.mem base) 21 = E s5.mem base 21 from rfl,
      e25 21 (by decide), e2, ← invEnv_eval, ← e1]; rfl
  -- The sign: the low bit of `x`, fully reduced.
  have sgn : (word s4.mem base X2).toNat % 2 =
      (E s.mem base 0 * Proof.X448.invert (E s.mem base 2)).val % 2 := by
    rw [← x1]
    have hv : (E s2.mem base 1).val = VG.Proof.X448.AArch64.fe s3.mem base X2 % Spec.X448.P := by
      have : VG.Proof.X448.toFe (VG.Proof.X448.AArch64.fe s3.mem base X2) = E s2.mem base 1 := v3
      rw [← this]; rfl
    rw [hv, ← v4, show VG.Proof.X448.AArch64.fe s4.mem base X2 =
      VG.Proof.X448.valN (limbs s4.mem base X2) 16 from rfl, valN_mod_two]
    rfl
  have byte : t.mem (p + BitVec.ofNat 64 56) = BitVec.ofNat 8 (128 * ((E s.mem base 0 *
      Proof.X448.invert (E s.mem base 2)).val % 2)) := by
    have hout : ∀ r ∈ ([⟨base, 8192⟩, ⟨p, 56⟩] : List Region), ¬ r.Contains (p + BitVec.ofNat 64 56) 1 := by
      intro r hr hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only [Region.Contains] at hc
        change 8192 ≤ ofs base (p + BitVec.ofNat 64 56) at far56
        simp only [ofs] at far56
        omega
      · simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat] at hc
        omega
    rw [ft _ hout]
    rw [show s6.mem (p + BitVec.ofNat 64 56) = s5.mem (p + BitVec.ofNat 64 56) from
      k6.mem _ (by simp only [ofs] at far56 ⊢; omega) (by simp only [ofs, ACC] at far56 ⊢; omega)]
    rw [m5, writeW8_apply]
    simp only [ite_true, sgn]
  refine ⟨t19, t20, ?_, ?_, ?_⟩
  · refine (((((k1.regs.mono ?_).trans (k2.regs.mono ?_)).trans (k3.keeps.mono ?_)).trans (k4.mono ?_)).trans
      (k5.mono ?_)).trans ((k6.regs.mono ?_).trans (kt.mono ?_))
    all_goals decide
  · have f5 : Frame [⟨base, 8192⟩, ⟨p, 57⟩] s4.mem s5.mem := by
      rw [m5]
      refine (Frame.refl _ _).writeW (r := ⟨p, 57⟩) (by simp) _ ?_
      simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
      omega
    have ft' : Frame [⟨base, 8192⟩, ⟨p, 57⟩] s6.mem t.mem := fun x hx => ft x fun r hr hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hx _ (by simp) hc
      · exact hx ⟨p, 57⟩ (by simp) (by simp only [Region.Contains] at hc ⊢; omega)
    exact ((((fr (k1.mem.whole (by decide) (by decide))).trans (fr (k2.mem.whole (by decide) (by decide)))).trans
      (fr (o25.whole (by decide)))).trans f5).trans ((fr (k6.mem.whole (by decide) (by decide))).trans ft')
  · rw [bytesAt_57, vt, byte, VG.Proof.X448.encodeUCoordinate_eq, y6, i6]
    exact (encodePoint_code _ _ _).symm

end VG.Proof.Ed448.AArch64
