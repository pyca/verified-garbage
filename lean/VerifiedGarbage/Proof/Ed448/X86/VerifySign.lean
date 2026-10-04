import VerifiedGarbage.Proof.Ed448.X86.VerifyDecodeY
import VerifiedGarbage.Proof.Ed448.X86.BaseEncode

/-!
# Ed448 verification's equation on x86 (32-bit): the sign of a decoded point

`decodeSign_ok`: with the candidate `x` in slot `xo` and `-x` in slot 12,
`x` fully reduced in slot 1; `BAD |= 0` exactly when `x ≠ 0` or the sign bit
(`SIGN`) is 0; and `x` swapped with `-x` under the mask of its low bit
differing from the sign bit (RFC 8032 §5.2.3, step 4).
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Impl.X448.X86 (slot X2 ACC TMP ld st copy freeze cswap sc)

/-- `edx = ⋁` the limbs of slot 1: 0 exactly when they all are. -/
theorem orLimbs_ok {s : State} {base : Addr} (hs : Scr s base) (hb : Bounded s.mem base X2) :
    WP isa (.block orLimbs) s fun t =>
      (t.gpr .edx).toNat < 65536 ∧ (t.gpr .edx = 0 ↔ ∀ i < 28, limbs s.mem base X2 i = 0) ∧
        t.mem = s.mem ∧ Keeps [.edx] s t := by
  unfold orLimbs
  refine load_ok hs (by decide) fun u hu => ?_
  let inv := fun n (t : State) =>
    (t.gpr .edx).toNat < 65536 ∧ (t.gpr .edx = 0 ↔ ∀ i < n + 1, limbs s.mem base X2 i = 0) ∧
      t.mem = s.mem ∧ Keeps [.edx] s t
  have h0 : inv 0 u := by
    refine ⟨?_, ?_, hu.mem, hu.rest (by simp)⟩
    · rw [hu.gpr]; exact hb 0 (by decide)
    · rw [hu.gpr]
      exact ⟨fun h i hi => by rw [show i = 0 by omega]; exact congrArg BitVec.toNat h,
        fun h => BitVec.eq_of_toNat_eq (h 0 (by decide))⟩
  refine wp_range_flatMap (M := isa) (N := 27) inv (fun n t hn ⟨tb, tz, tm, tk⟩ => ?_) 27 (by decide) u h0
  have ht := hs.of_keeps tk (by decide)
  refine wp_alu (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (rd_sc ht (by simp only [X2, slot]; omega))
    fun w hw _ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · rw [hw.gpr]; change (t.gpr .edx ||| word t.mem base (X2 + 4 * (n + 1))).toNat < _
    rw [BitVec.toNat_or, tm]
    exact Nat.or_lt_two_pow (n := 16) tb (hb (n + 1) (by omega))
  · rw [hw.gpr]; change t.gpr .edx ||| word t.mem base (X2 + 4 * (n + 1)) = 0 ↔ _
    rw [tm]
    refine BitVec.or_eq_zero_iff.trans ((and_congr_left fun _ => tz).trans ?_)
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h1 i hi
      · exact congrArg BitVec.toNat h2
    · intro h
      exact ⟨fun i hi => h i (by omega), BitVec.eq_of_toNat_eq (h (n + 1) (by omega))⟩
  · rw [hw.mem, tm]
  · exact tk.trans (hw.rest (by simp))

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

/-- After the `x = 0` check (`edx`, 0 exactly when `Z`): `BAD |= 0` exactly
when not both `Z` and the sign bit, and `ebx` the mask of the low bit `l₀`
differing from it. -/
theorem signTail_ok {s : State} {base : Addr} (hs : Scr s base) {Z : Prop} (h2 : (s.gpr .edx).toNat < 65536)
    (hz : s.gpr .edx = 0 ↔ Z) {sb : Nat} (hsb : sb < 2) (hsign : word s.mem base SIGN = BitVec.ofNat 32 sb) :
    WP isa (.block (([.alu .sub .edx (.imm 1), .shift .shr .edx 31, .alu .and .edx (.mem (sc SIGN))] :
      List Instr) ++ orBad .edx ++ ([ld .eax X2, .alu .and .eax (.imm 1), .alu .xor .eax (.mem (sc SIGN)),
      .mov .ebx (.imm 0), .alu .sub .ebx (.reg .eax)] : List Instr))) s fun t =>
      BadUpd (¬(Z ∧ sb = 1)) (word s.mem base BAD) (word t.mem base BAD) ∧
        t.gpr .ebx = mask (decide (limbs s.mem base X2 0 % 2 ≠ sb)) ∧ Outside base BAD 4 s.mem t.mem ∧
        Keeps [.eax, .ebx, .edx] s t := by
  simp only [List.cons_append, List.nil_append]
  refine wp_alu (Or.inr (Or.inl rfl)) rfl fun u1 v1 _ => ?_
  refine wp_shift (by decide) fun u2 v2 => ?_
  have s2 := (hs.of_upd v1 (by decide)).of_upd v2 (by decide)
  refine wp_alu (Or.inr (Or.inr (Or.inl rfl))) (rd_sc s2 (by decide)) fun u3 v3 _ => ?_
  have s3 := s2.of_upd v3 (by decide)
  have e3 : u3.gpr .edx = (if s.gpr .edx = 0 then 1 else 0 : BitVec 32) &&& BitVec.ofNat 32 sb := by
    rw [v3.gpr]; change u2.gpr .edx &&& word u2.mem base SIGN = _
    rw [v2.gpr, v2.mem, v1.mem, hsign, v1.gpr]
    exact congrArg (· &&& _) (isZero16 _ h2)
  have z := zeroSign (decide (s.gpr .edx = 0)) sb hsb
  simp only [decide_eq_true_eq] at z
  rw [← e3] at z
  change WP isa (.block (orBad .edx ++ [ld .eax X2, .alu .and .eax (.imm 1), .alu .xor .eax (.mem (sc SIGN)),
    .mov .ebx (.imm 0), .alu .sub .ebx (.reg .eax)])) u3 _
  rw [WP.block_append_iff]
  refine WP.mono (orBad_ok s3 (by decide) (P := ¬(Z ∧ sb = 1)) z.2 (z.1.trans (by rw [hz]))) fun u4 ⟨b4, o4, k4⟩ => ?_
  have s4 := s3.of_keeps k4 (by decide)
  refine load_ok s4 (by decide) fun u5 v5 => ?_
  have s5 := s4.of_upd v5 (by decide)
  refine wp_alu (Or.inr (Or.inr (Or.inl rfl))) rfl fun u6 v6 _ => ?_
  have s6 := s5.of_upd v6 (by decide)
  refine wp_alu (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (rd_sc s6 (by decide)) fun u7 v7 _ => ?_
  refine wp_mov rfl fun u8 v8 => ?_
  refine wp_alu (Or.inr (Or.inl rfl)) rfl fun t vt _ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · have m3 : u3.mem = s.mem := by rw [v3.mem, v2.mem, v1.mem]
    have e : word t.mem base BAD = word u4.mem base BAD := by
      rw [vt.mem, v8.mem, v7.mem, v6.mem, v5.mem]
    rw [e, ← m3]
    exact b4
  · rw [vt.gpr]; change u8.gpr .ebx - u8.gpr .eax = _
    rw [v8.gpr, v8.other _ (by decide), v7.gpr]
    change (0 : BitVec 32) - (u6.gpr .eax ^^^ word u6.mem base SIGN) = _
    rw [v6.gpr]
    change (0 : BitVec 32) - ((u5.gpr .eax &&& 1) ^^^ word u6.mem base SIGN) = _
    rw [v5.gpr, v6.mem, v5.mem, and1]
    have sg : word u4.mem base SIGN = BitVec.ofNat 32 sb := by
      rw [o4.word (Or.inr (by decide)) (by decide), v3.mem, v2.mem, v1.mem, hsign]
    have l0 : (word u4.mem base X2).toNat = limbs s.mem base X2 0 := by
      rw [o4.word (Or.inr (by decide)) (by decide), v3.mem, v2.mem, v1.mem]; rfl
    rw [sg, l0]
    exact negMask _ (Nat.mod_lt _ (by decide)) sb hsb
  · intro x hx
    rw [vt.mem, v8.mem, v7.mem, v6.mem, v5.mem, o4 x hx, v3.mem, v2.mem, v1.mem]
  · exact (v1.rest (by simp)).trans ((v2.rest (by simp)).trans ((v3.rest (by simp)).trans
      ((k4.mono (by simp)).trans ((v5.rest (by simp)).trans ((v6.rest (by simp)).trans
      ((v7.rest (by simp)).trans ((v8.rest (by simp)).trans (vt.rest (by simp)))))))))

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
      BadUpd (¬(E s.mem base xo = 0 ∧ sb = 1)) (word s.mem base BAD) (word t.mem base BAD) ∧
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
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok hs (o := X2) (a := slot xo.val) (by decide) (by omega)
    (Or.inr (by omega))) fun s1 ⟨f1, m1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  have bd1 : Bounded s1.mem base X2 := fun i hi => by rw [f1 i hi]; exact hb xo i hi
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok hs1 bd1) fun s2 ⟨b2, v2, m2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (orLimbs_ok hs2 b2) fun s3 ⟨r3b, r3z, m3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by decide)
  have fx : fe s2.mem base X2 = (E s.mem base xo).val := by
    rw [v2, show fe s1.mem base X2 = fe s.mem base (slot xo.val) from valN_congr f1]; rfl
  have zero : (∀ i < 28, limbs s2.mem base X2 i = 0) ↔ E s.mem base xo = 0 := by
    rw [fe_zero_iff b2, fx]; exact Fin.val_eq_zero_iff
  have sign3 : word s3.mem base SIGN = BitVec.ofNat 32 sb := by
    rw [m3, m2.word (Or.inl (by simp only [SIGN]; omega)) (by decide),
      m1.word (Or.inl (by simp only [SIGN]; omega)) (by decide), hsign]
  rw [zero] at r3z
  rw [← List.append_assoc, ← List.append_assoc, WP.block_append_iff]
  refine WP.mono (signTail_ok hs3 r3b r3z hsb sign3) fun s4 ⟨b4, c4, m4, k4⟩ => ?_
  have hs4 := hs3.of_keeps k4 (by decide)
  have e4 : ∀ i : Index, i ≠ 1 → ∀ j < 28, limbs s4.mem base (slot i.val) j = limbs s.mem base (slot i.val) j := by
    intro i h1 j hj
    have si := slot_range i
    have s1i : slot i.val + 112 ≤ X2 ∨ X2 + 112 ≤ slot i.val := by rw [hX2]; exact slot_sep h1
    rw [m4.limbs (Or.inr (by simp only [BAD]; omega)) (by omega) hj, m3, m2.limbs s1i (by omega) hj,
      m1.limbs (by omega) (by omega) hj]
  have bd4 : BoundedEnv s4.mem base := by
    intro i j hj
    by_cases h1 : i = 1
    · subst i
      rw [m4.limbs (Or.inr (by simp only [BAD, slot]; omega)) (by decide) hj, m3]; exact b2 j hj
    · rw [e4 i h1 j hj]; exact hb i j hj
  refine WP.mono (cswapE hs4 bd4 xo 12 hx12 c4) fun t ⟨kt, bt, _, et⟩ => ?_
  have E4 : ∀ i : Index, i ≠ 1 → E s4.mem base i = E s.mem base i := fun i h1 => by
    simp only [E, F]; exact congrArg Proof.X448.toFe (valN_congr (e4 i h1))
  have l0 : limbs s3.mem base X2 0 % 2 = (E s.mem base xo).val % 2 := by
    rw [m3, ← fe_mod2, fx]
  have bad3 : word s3.mem base BAD = word s.mem base BAD := by
    rw [m3, m2.word (Or.inl (by simp only [BAD]; omega)) (by simp only [BAD, ACC]; omega),
      m1.word (Or.inl (by simp only [BAD]; omega)) (by decide)]
  refine ⟨⟨?_, ?_⟩, bt, ?_, ?_, fun i h1 h12 hx => ?_⟩
  · refine (((k1.mono ?_).trans ((k2.mono ?_).trans ((k3.mono ?_).trans (k4.mono ?_)))).trans
      (kt.regs.mono ?_)) <;> intro r hr <;> revert r <;> decide
  · exact (((outB m1 (by decide) (by decide)).trans (fmB m2 (by decide) (by decide))).trans
      (by rw [← m3]; exact (BMem.of_bad m4))).trans (BMem.of_outside2 kt.mem)
  · rw [kt.mem.word (Or.inl (by decide)) (Or.inl (by decide)) (by decide), ← bad3]
    exact b4
  · rw [et]
    simp only [opSwap, Function.update_of_ne hx12, Function.update_self]
    rw [E4 xo hx1, E4 12 (by decide), hneg, l0, sel_sign _ (Nat.mod_lt _ (by decide)) sb hsb]
    cases ((E s.mem base xo).val % 2 == 1) == (sb == 1) <;> rfl
  · rw [et]
    simp only [opSwap, Function.update_of_ne h12, Function.update_of_ne hx]
    exact E4 i h1

end VG.Proof.Ed448.X86
