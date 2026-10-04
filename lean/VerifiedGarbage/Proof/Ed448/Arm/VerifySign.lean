import VerifiedGarbage.Proof.Ed448.Arm.VerifyDecodeY

/-!
# Ed448 verification's equation on ARMv7: the sign of a decoded point

`decodeSign_ok`: with the candidate `x` in slot `xo` and `-x` in slot 12,
`x` fully reduced in slot 1; `BAD |= 0` exactly when `x ≠ 0` or the sign bit
(`SIGN`) is 0; and `x` swapped with `-x` under the mask of its low bit
differing from the sign bit (RFC 8032 §5.2.3, step 4).
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm VG.Proof.X448.Radix16
open VG.Impl.X448.Arm (slot X2 ACC TMP ld st copy freeze cswap)
open VG.Proof.X25519.Arm (wp_dp wp_mov op2_lsr op2_imm op2_reg)

/-- `r2 = ⋁` the limbs of slot 1: 0 exactly when they all are. -/
theorem orLimbs_ok {s : State} {base : Addr} (hs : Scr s base) (hb : Bounded s.mem base X2) :
    WP isa (.block orLimbs) s fun t =>
      (t.gpr .r2).toNat < 65536 ∧ (t.gpr .r2 = 0 ↔ ∀ i < 28, limbs s.mem base X2 i = 0) ∧
        t.mem = s.mem ∧ Keeps [.r2, .r3] s t := by
  unfold orLimbs
  refine load_ok hs (by decide) fun u hu => ?_
  let inv := fun n (t : State) =>
    (t.gpr .r2).toNat < 65536 ∧ (t.gpr .r2 = 0 ↔ ∀ i < n + 1, limbs s.mem base X2 i = 0) ∧
      t.mem = s.mem ∧ Keeps [.r2, .r3] s t
  have h0 : inv 0 u := by
    refine ⟨?_, ?_, hu.mem, rest_keeps (hu.rest (by decide))⟩
    · rw [hu.gpr]; exact hb 0 (by decide)
    · rw [hu.gpr]
      exact ⟨fun h i hi => by rw [show i = 0 by omega]; exact congrArg BitVec.toNat h,
        fun h => BitVec.eq_of_toNat_eq (h 0 (by decide))⟩
  refine wp_range_flatMap (M := isa) (N := 27) inv (fun n t hn ⟨tb, tz, tm, tk⟩ => ?_) 27 (by decide) u h0
  refine load_ok (hs.of_keeps tk (by decide)) (by simp only [X2, slot]; omega) fun v hv => ?_
  refine wp_dp (op2_reg _ _) fun w hw => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · rw [hw.gpr]; change (v.gpr .r2 ||| v.gpr .r3).toNat < _
    rw [hv.other _ (by decide), hv.gpr, BitVec.toNat_or, tm]
    exact Nat.or_lt_two_pow (n := 16) tb (hb (n + 1) (by omega))
  · rw [hw.gpr]; change v.gpr .r2 ||| v.gpr .r3 = 0 ↔ _
    rw [hv.other _ (by decide), hv.gpr, tm]
    refine BitVec.or_eq_zero_iff.trans ((and_congr_left fun _ => tz).trans ?_)
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h1 i hi
      · exact congrArg BitVec.toNat h2
    · intro h
      exact ⟨fun i hi => h i (by omega), BitVec.eq_of_toNat_eq (h (n + 1) (by omega))⟩
  · rw [hw.mem, hv.mem, tm]
  · exact tk.trans (rest_keeps ((hv.rest (by decide)).trans (hw.rest (by decide))))

theorem isZero16 (x : BitVec 32) (h : x.toNat < 65536) :
    (x - 1) >>> 31 = if x = 0 then 1 else 0 := by
  by_cases hx : x = 0
  · subst hx; decide
  · rw [ite_eq_right hx]
    have hx' : x.toNat ≠ 0 := fun e => hx (BitVec.eq_of_toNat_eq e)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
    change (2 ^ 32 - 1 + x.toNat) % 2 ^ 32 / 2 ^ 31 = 0
    omega

theorem zeroSign : ∀ z : Bool, ∀ sb < 2,
    (((if z then 1 else 0 : BitVec 32) &&& BitVec.ofNat 32 sb) = 0 ↔ ¬(z = true ∧ sb = 1)) ∧
      ((if z then 1 else 0 : BitVec 32) &&& BitVec.ofNat 32 sb).toNat < 65536 := by decide

theorem negMask : ∀ a < 2, ∀ sb < 2,
    (0 : BitVec 32) - (BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 sb) = mask (decide (a ≠ sb)) := by decide

theorem and1 (w : BitVec 32) : w &&& 1 = BitVec.ofNat 32 (w.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := w.toNat % 2) (by omega)]

/-- After the `x = 0` check (`r2`, 0 exactly when `Z`): `BAD |= 0` exactly when
not both `Z` and the sign bit, and `r5` the mask of the low bit `l₀` differing
from it. -/
theorem signTail_ok {s : State} {base : Addr} (hs : Scr s base) {Z : Prop} (h2 : (s.gpr .r2).toNat < 65536)
    (hz : s.gpr .r2 = 0 ↔ Z) {sb : Nat} (hsb : sb < 2) (hsign : word s.mem base SIGN = BitVec.ofNat 32 sb) :
    WP isa (.block [.dp .sub .r2 .r2 (.imm 1), .mov .r2 (.shifted .r2 .lsr 31), ld .r3 SIGN,
      .dp .and .r2 .r2 (.reg .r3), .dp .orr .r12 .r12 (.reg .r2),
      ld .r2 X2, .dp .and .r2 .r2 (.imm 1), .dp .eor .r2 .r2 (.reg .r3), .mov .r5 (.imm 0),
      .dp .sub .r5 .r5 (.reg .r2)]) s fun t =>
      BadUpd (¬(Z ∧ sb = 1)) (s.gpr .r12) (t.gpr .r12) ∧
        t.gpr .r5 = mask (decide (limbs s.mem base X2 0 % 2 ≠ sb)) ∧ t.mem = s.mem ∧
        Keeps [.r2, .r3, .r5, .r12] s t := by
  refine wp_dp (op2_imm (by decide)) fun u1 v1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun u2 v2 => ?_
  have s2 := (hs.of_upd v1 (by decide) (by decide)).of_upd v2 (by decide) (by decide)
  refine load_ok s2 (by decide) fun u3 v3 => ?_
  refine wp_dp (op2_reg _ _) fun u4 v4 => ?_
  refine wp_dp (op2_reg _ _) fun u5 v5 => ?_
  have s5 := ((s2.of_upd v3 (by decide) (by decide)).of_upd v4 (by decide) (by decide)).of_upd v5
    (by decide) (by decide)
  refine load_ok s5 (by decide) fun u6 v6 => ?_
  refine wp_dp (op2_imm (by decide)) fun u7 v7 => ?_
  refine wp_dp (op2_reg _ _) fun u8 v8 => ?_
  refine wp_mov (op2_imm (by decide)) fun u9 v9 => ?_
  refine wp_dp (op2_reg _ _) fun t vt => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · have e2 : u2.gpr .r2 = if s.gpr .r2 = 0 then 1 else 0 := by
      rw [v2.gpr, v1.gpr]; exact isZero16 _ h2
    have e4 : u4.gpr .r2 = (if s.gpr .r2 = 0 then 1 else 0 : BitVec 32) &&& BitVec.ofNat 32 sb := by
      rw [v4.gpr]; change u3.gpr .r2 &&& u3.gpr .r3 = _
      rw [v3.other _ (by decide), e2, v3.gpr, v2.mem, v1.mem, hsign]
    have z := zeroSign (decide (s.gpr .r2 = 0)) sb hsb
    simp only [decide_eq_true_eq] at z
    have e12 : t.gpr .r12 = s.gpr .r12 ||| u4.gpr .r2 := by
      rw [vt.other _ (by decide), v9.other _ (by decide), v8.other _ (by decide), v7.other _ (by decide),
        v6.other _ (by decide), v5.gpr]
      change u4.gpr .r12 ||| u4.gpr .r2 = _
      rw [v4.other _ (by decide), v3.other _ (by decide), v2.other _ (by decide), v1.other _ (by decide)]
    refine ⟨u4.gpr .r2, ?_, ?_, e12⟩
    · rw [e4]; exact z.2
    · rw [e4, z.1, hz]
  · rw [vt.gpr]; change u9.gpr .r5 - u9.gpr .r2 = _
    rw [v9.gpr, v9.other _ (by decide), v8.gpr]
    change (0 : BitVec 32) - (u7.gpr .r2 ^^^ u7.gpr .r3) = _
    rw [v7.gpr, v7.other _ (by decide)]
    change (0 : BitVec 32) - ((u6.gpr .r2 &&& 1) ^^^ u6.gpr .r3) = _
    rw [v6.gpr, v6.other _ (by decide), v5.other _ (by decide), v4.other _ (by decide), v3.gpr,
      v5.mem, v4.mem, v3.mem, v2.mem, v1.mem, hsign, and1]
    exact negMask _ (Nat.mod_lt _ (by decide)) sb hsb
  · rw [vt.mem, v9.mem, v8.mem, v7.mem, v6.mem, v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]
  · exact rest_keeps ((v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans ((v5.rest (by decide)).trans ((v6.rest (by decide)).trans
      ((v7.rest (by decide)).trans ((v8.rest (by decide)).trans ((v9.rest (by decide)).trans
      (vt.rest (by decide)))))))))))

theorem sel_sign : ∀ a < 2, ∀ sb < 2, decide (a ≠ sb) = !((a == 1) == (sb == 1)) := by decide

theorem fe_zero_iff {m : Mem} {base : Addr} {o : Nat} (hb : Bounded m base o) :
    (∀ i < 28, limbs m base o i = 0) ↔ fe m base o = 0 := by
  have z : valN (fun _ => 0) 28 = 0 := valN_zero 28
  constructor
  · intro h; exact (valN_congr h).trans z
  · intro h; exact valN_inj hb (fun _ _ => by decide) (h.trans z.symm)

/-- `decodeSign xo`, with `-x` in slot 12 and the sign bit `sb` at `SIGN`. -/
theorem decodeSign_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    (xo : Index) (hxo : xo = 6 ∨ xo = 8) {sb : Nat} (hsb : sb < 2)
    (hsign : word s.mem base SIGN = BitVec.ofNat 32 sb)
    (hneg : E s.mem base 12 = (E s.mem base xo - E s.mem base xo) - E s.mem base xo) :
    WP isa (.block (decodeSign xo.val)) s fun t =>
      CKeep base s t ∧ BoundedEnv t.mem base ∧
      BadUpd (¬(E s.mem base xo = 0 ∧ sb = 1)) (s.gpr .r12) (t.gpr .r12) ∧
      E t.mem base xo = (if ((E s.mem base xo).val % 2 == 1) == (sb == 1) then E s.mem base xo
        else (E s.mem base xo - E s.mem base xo) - E s.mem base xo) ∧
      (∀ i : Index, i ≠ 1 → i ≠ 12 → i ≠ xo → E t.mem base i = E s.mem base i) := by
  have hx1 : xo ≠ 1 := by rcases hxo with rfl | rfl <;> decide
  have hx12 : xo ≠ 12 := by rcases hxo with rfl | rfl <;> decide
  have sx := slot_range xo
  have hX2v : X2 = 192 := rfl
  have hA : ACC = 3584 := rfl
  have hX2 : X2 = slot (1 : Index).val := rfl
  have s1x : slot xo.val + 112 ≤ X2 ∨ X2 + 112 ≤ slot xo.val := by rw [hX2]; exact slot_sep hx1
  unfold decodeSign
  simp only [List.append_assoc]
  refine VG.Proof.X25519.Arm.WP.append (copy_ok hs (o := X2) (a := slot xo.val) (by decide) (by omega)
    (Or.inr (by omega))) fun s1 ⟨f1, m1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  have bd1 : Bounded s1.mem base X2 := fun i hi => by rw [f1 i hi]; exact hb xo i hi
  refine VG.Proof.X25519.Arm.WP.append (freeze_ok hs1 bd1) fun s2 ⟨b2, v2, m2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  refine VG.Proof.X25519.Arm.WP.append (orLimbs_ok hs2 b2) fun s3 ⟨r3b, r3z, m3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by decide)
  -- `x` and its value in slot 1
  have fx : fe s2.mem base X2 = (E s.mem base xo).val := by
    rw [v2, show fe s1.mem base X2 = fe s.mem base (slot xo.val) from valN_congr f1]; rfl
  have zero : (∀ i < 28, limbs s2.mem base X2 i = 0) ↔ E s.mem base xo = 0 := by
    rw [fe_zero_iff b2, fx]; exact Fin.val_eq_zero_iff
  have sign3 : word s3.mem base SIGN = BitVec.ofNat 32 sb := by
    rw [m3, m2.word (Or.inl (by simp only [SIGN]; omega)) (by decide),
      m1.word (Or.inl (by simp only [SIGN]; omega)) (by decide), hsign]
  rw [zero] at r3z
  refine VG.Proof.X25519.Arm.WP.append (signTail_ok hs3 r3b r3z hsb sign3) fun s4 ⟨b4, c4, m4, k4⟩ => ?_
  have hs4 := hs3.of_keeps k4 (by decide)
  have bd4 : BoundedEnv s4.mem base := by
    intro i j hj
    by_cases h1 : i = 1
    · subst i; rw [m4, m3]; exact b2 j hj
    · have si := slot_range i
      have s1i : slot i.val + 112 ≤ X2 ∨ X2 + 112 ≤ slot i.val := by rw [hX2]; exact slot_sep h1
      rw [m4, m3, m2.limbs s1i (by omega) hj, m1.limbs (by omega) (by omega) hj]; exact hb i j hj
  refine WP.mono (cswapE hs4 bd4 xo 12 hx12 c4) fun t ⟨kt, bt, _, et⟩ => ?_
  have e4 : ∀ i : Index, i ≠ 1 → E s4.mem base i = E s.mem base i := by
    intro i h1
    have si := slot_range i
    have s1i : slot i.val + 112 ≤ X2 ∨ X2 + 112 ≤ slot i.val := by rw [hX2]; exact slot_sep h1
    simp only [E, F]
    rw [m4, m3, m2.fe s1i (by omega), m1.fe (by omega) (by omega)]
  have l0 : limbs s3.mem base X2 0 % 2 = (E s.mem base xo).val % 2 := by
    rw [m3, ← fe_mod2, fx]
  refine ⟨⟨?_, ?_⟩, bt, ?_, ?_, fun i h1 h12 hx => ?_⟩
  · refine (((k1.mono ?_).trans ((k2.mono ?_).trans ((k3.mono ?_).trans (k4.mono ?_)))).trans
      (kt.regs.mono ?_)) <;> intro r hr <;> revert r <;> decide
  · have e : s4.mem = s2.mem := by rw [m4, m3]
    exact ((outC m1 (by decide) (by decide)).trans (fmC m2 (by decide) (by decide))).trans
      (by rw [← e]; exact kt.mem)
  · have r12 : s3.gpr .r12 = s.gpr .r12 := by
      rw [k3.1 _ (by decide), k2.1 _ (by decide), k1.1 _ (by decide)]
    rw [kt.regs.1 _ (by decide), ← r12]
    exact b4
  · rw [et]
    simp only [opSwap, Function.update_of_ne hx12, Function.update_self]
    rw [e4 xo hx1, e4 12 (by decide), hneg, l0, sel_sign _ (Nat.mod_lt _ (by decide)) sb hsb]
    cases ((E s.mem base xo).val % 2 == 1) == (sb == 1) <;> rfl
  · rw [et]
    simp only [opSwap, Function.update_of_ne h12, Function.update_of_ne hx]
    exact e4 i h1

end VG.Proof.Ed448.Arm
