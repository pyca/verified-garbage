import VerifiedGarbage.Proof.Ed448.X86.VerifyS

/-!
# Ed448 verification's equation on x86 (32-bit): the `y` of a point

`decodeY_ok`: the 57 bytes of an encoded point at `q` (the argument read from
the stack into `esi`): the twenty-eight limbs of the first 56 (`y₀`) into
slot `yo`, the sign bit (bit 7 of the last byte `b`) to `SIGN`, and
`BAD |= 0` exactly when bits 0–6 of `b` are 0 and `y₀ < p` (`y₀` is equal to
its full reduction, in slot 1).
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Impl.X448.X86 (slot X2 ACC TMP ld st copy freeze at_)

theorem loadLimbs_ok {s : State} {base q : Addr} (hs : Scr s base) (hq : (s.gpr .esi).setWidth 64 = q)
    (hfit : (s.gpr .esi).toNat + 57 ≤ 2 ^ 32)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1)
    (hd : ∀ j < 56, 8192 ≤ ofs base (q + BitVec.ofNat 64 j)) {o : Nat} (ho : 16 ≤ o ∧ o + 112 ≤ 4096) :
    WP isa (.block (loadLimbs o)) s fun t =>
      (∀ i < 28, limbs t.mem base o i = decoded s.mem q i) ∧
        Outside base o 112 s.mem t.mem ∧ Keeps [.eax, .edx] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base o i = decoded s.mem q i) ∧
      Outside base o 112 s.mem t.mem ∧ Keeps [.eax, .edx] s t
  refine wp_range_flatMap (M := isa) (N := 28) inv (fun n t hn ⟨tf, tm, tk⟩ => ?_) 28 (by decide) s
    ⟨fun _ h => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩
  have byte : ∀ j < 56, t.mem (q + BitVec.ofNat 64 j) = s.mem (q + BitVec.ofNat 64 j) :=
    fun j hj => tm _ (Or.inr (by have := hd j hj; omega))
  have eq : decoded t.mem q n = decoded s.mem q n := by
    simp only [decoded, byteN]; rw [byte _ (by omega), byte _ (by omega)]
  have te : t.gpr .esi = s.gpr .esi := tk.1 _ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (byteLimb_ok (src := 0) (q := q)
    (by rw [te, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero, hq]) (by rw [te]; omega) hn
    (by rw [tk.2.1, tk.2.2]; exact hr)) fun u ⟨u3, um, uk⟩ => ?_
  refine store_ok ((hs.of_keeps tk (by decide)).of_keeps uk (by decide)) (by omega) fun v hv =>
    WP.block_nil ⟨fun i hi => ?_, tm.trans ?_, tk.trans (uk.trans (hv.rest _))⟩
  · change (word v.mem base (o + 4 * i)).toNat = _
    rw [hv.mem, um, word_write t.mem base (by omega) (by omega)]
    by_cases h : i = n
    · rw [ite_eq_left h, h, u3, eq, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.lt_trans (decoded_lt s.mem q n) (by decide))]
    · rw [ite_eq_right h]; exact tf i (by omega)
  · rw [hv.mem, um]; exact (writeW_outside _ _ _ (by omega)).mono (by omega) (by omega)

/-- The last byte `b`: `SIGN = b / 128` and `eax = b mod 128`. -/
theorem signByte_ok {s : State} {base q : Addr} (hs : Scr s base) (hq : (s.gpr .esi).setWidth 64 = q)
    (hfit : (s.gpr .esi).toNat + 57 ≤ 2 ^ 32) (hr : InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 56) 1) :
    WP isa (.block signByte) s fun t =>
      (t.gpr .eax).toNat = (s.mem (q + BitVec.ofNat 64 56)).toNat % 128 ∧
      t.mem = s.mem.writeW (off base SIGN) (BitVec.ofNat 32 ((s.mem (q + BitVec.ofNat 64 56)).toNat / 128)) ∧
      Keeps [.eax, .edx] s t := by
  unfold signByte
  refine wp_load8 (a := q + BitVec.ofNat 64 56)
    (by rw [show (56 : Nat) = 0 + 56 from rfl]
        exact ea_esi (by rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero, hq]) (by omega)) hr
    fun u hu => ?_
  refine wp_mov rfl fun v hv => ?_
  refine wp_shift (by decide) fun w hw => ?_
  have sw := ((hs.of_upd hu (by decide)).of_upd hv (by decide)).of_upd hw (by decide)
  refine store_ok sw (by decide) fun x hx => ?_
  refine wp_alu (Or.inr (Or.inr (Or.inl rfl))) rfl fun y hy _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [hy.gpr]; change (x.gpr .eax &&& 0x7f#32).toNat = _
    rw [hx.gpr, hw.other _ (by decide), hv.other _ (by decide), hu.gpr, BitVec.toNat_and,
      BitVec.toNat_setWidth, show (0x7f#32).toNat = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    have := (s.mem (q + BitVec.ofNat 64 56)).isLt
    omega
  · rw [hy.mem, hx.mem, hw.mem, hv.mem, hu.mem, hw.gpr]
    change s.mem.writeW _ (v.gpr .edx >>> 7) = _
    rw [hv.gpr, hu.gpr]
    congr 1
    apply BitVec.eq_of_toNat_eq
    have := (s.mem (q + BitVec.ofNat 64 56)).isLt
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  · exact (hu.rest (by simp)).trans ((hv.rest (by simp)).trans ((hw.rest (by simp)).trans
      ((hx.rest _).trans (hy.rest (by simp)))))

/-- `decodeY yo`, for the pointer `p` in `esi`. -/
theorem decodeY_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    {p : BitVec 32} (hp : s.gpr .esi = p) (hfit : p.toNat + 57 ≤ 2 ^ 32)
    (hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (p.setWidth 64 + BitVec.ofNat 64 j) 1)
    (hd : ∀ j < 57, 8192 ≤ ofs base (p.setWidth 64 + BitVec.ofNat 64 j)) (yo : Index) (hyo : yo ≠ 1) :
    WP isa (.block (decodeY yo.val)) s fun t =>
      VKeep base s t ∧ BoundedEnv t.mem base ∧
      word t.mem base SIGN = BitVec.ofNat 32 ((s.mem (p.setWidth 64 + BitVec.ofNat 64 56)).toNat / 128) ∧
      BadUpd ((s.mem (p.setWidth 64 + BitVec.ofNat 64 56)).toNat % 128 = 0 ∧
        valN (decoded s.mem (p.setWidth 64)) 28 < Spec.X448.P) (word s.mem base BAD) (word t.mem base BAD) ∧
      E t.mem base yo = Proof.X448.toFe (valN (decoded s.mem (p.setWidth 64)) 28) ∧
      (∀ i : Index, i ≠ 1 → i ≠ yo → E t.mem base i = E s.mem base i) := by
  generalize hq : p.setWidth 64 = q at hr hd ⊢
  have sy := slot_range yo
  have hX2v : X2 = 192 := rfl
  have hA : ACC = 3584 := rfl
  have hX2 : X2 = slot (1 : Index).val := rfl
  have s1y : slot yo.val + 112 ≤ X2 ∨ X2 + 112 ≤ slot yo.val := by rw [hX2]; exact slot_sep hyo
  unfold decodeY
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loadLimbs_ok hs (by rw [hp, hq]) (by rw [hp]; exact hfit)
    (fun j hj => hr j (by omega)) (fun j hj => hd j (by omega))
    (o := slot yo.val) ⟨by omega, by omega⟩) fun s1 ⟨f1, m1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  have b56 : s1.mem (q + BitVec.ofNat 64 56) = s.mem (q + BitVec.ofNat 64 56) :=
    m1 _ (Or.inr (by have := hd 56 (by decide); omega))
  rw [WP.block_append_iff]
  refine WP.mono (signByte_ok hs1 (q := q) (by rw [k1.1 _ (by decide), hp, hq])
    (by rw [k1.1 _ (by decide), hp]; exact hfit) (by rw [k1.2.1, k1.2.2]; exact hr 56 (by decide)))
    fun s2 ⟨r2, m2, k2⟩ => ?_
  rw [b56] at r2 m2
  have hs2 := hs1.of_keeps k2 (by decide)
  have o2 : Outside base SIGN 4 s1.mem s2.mem := by rw [m2]; exact writeW_outside _ _ _ (by decide)
  have l2 : ∀ i < 28, limbs s2.mem base (slot yo.val) i = decoded s.mem q i := fun i hi => by
    rw [o2.limbs (Or.inr (by simp only [SIGN]; omega)) (by omega) hi, f1 i hi]
  rw [WP.block_append_iff]
  refine WP.mono (orBad_ok (s := s2) hs2 (by decide)
    (P := (s.mem (q + BitVec.ofNat 64 56)).toNat % 128 = 0)
    (by rw [r2]; omega) (by rw [← r2]; exact ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩))
    fun s3 ⟨b3, m3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by decide)
  have l3 : ∀ i < 28, limbs s3.mem base (slot yo.val) i = decoded s.mem q i := fun i hi => by
    rw [m3.limbs (Or.inr (by simp only [BAD]; omega)) (by omega) hi, l2 i hi]
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok hs3 (o := X2) (a := slot yo.val) (by decide) (by omega)
    (Or.inr (by omega))) fun s4 ⟨f4, m4, k4⟩ => ?_
  have hs4 := hs3.of_keeps k4 (by decide)
  have bd4 : Bounded s4.mem base X2 := fun i hi => by rw [f4 i hi, l3 i hi]; exact decoded_lt _ _ _
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok hs4 bd4) fun s5 ⟨b5, v5, m5, k5⟩ => ?_
  have hs5 := hs4.of_keeps k5 (by decide)
  have l5 : ∀ i < 28, limbs s5.mem base (slot yo.val) i = decoded s.mem q i := fun i hi => by
    rw [m5.limbs s1y (by omega) hi, m4.limbs (by omega) (by omega) hi, l3 i hi]
  have by5 : Bounded s5.mem base (slot yo.val) := fun i hi => by rw [l5 i hi]; exact decoded_lt _ _ _
  refine WP.mono (diffSlot_ok hs5 (by omega) b5 by5) fun t ⟨tb, tm, tk⟩ => ?_
  have fe5 : fe s5.mem base X2 = valN (decoded s.mem q) 28 % Spec.X448.P := by
    rw [v5]; exact congrArg (· % Spec.X448.P) ((valN_congr f4).trans (valN_congr l3))
  have fy5 : fe s5.mem base (slot yo.val) = valN (decoded s.mem q) 28 := valN_congr l5
  have tl : ∀ dd, 64 ≤ dd → dd + 112 ≤ 2880 → ∀ j < 28, limbs t.mem base dd j = limbs s5.mem base dd j :=
    fun dd h1 h2 j hj => tm.limbs (Or.inr (by simp only [BAD]; omega)) (by omega) hj
  have other : ∀ i : Index, i ≠ 1 → i ≠ yo → ∀ j < 28,
      limbs t.mem base (slot i.val) j = limbs s.mem base (slot i.val) j := by
    intro i hi1 hiy j hj
    have si := slot_range i
    have s1i : slot i.val + 112 ≤ X2 ∨ X2 + 112 ≤ slot i.val := by rw [hX2]; exact slot_sep hi1
    have syi := slot_sep hiy
    rw [tl _ si.1 si.2 j hj, m5.limbs s1i (by omega) hj, m4.limbs (by omega) (by omega) hj,
      m3.limbs (Or.inr (by simp only [BAD]; omega)) (by omega) hj,
      o2.limbs (Or.inr (by simp only [SIGN]; omega)) (by omega) hj, m1.limbs (by omega) (by omega) hj]
  have bad3 : word s5.mem base BAD = word s3.mem base BAD := by
    rw [m5.word (Or.inl (by simp only [BAD]; omega)) (by simp only [BAD, ACC]; omega),
      m4.word (Or.inl (by simp only [BAD]; omega)) (by decide)]
  have bad2 : word s2.mem base BAD = word s.mem base BAD := by
    rw [o2.word (Or.inl (by decide)) (by decide), m1.word (Or.inl (by simp only [BAD]; omega)) (by decide)]
  refine ⟨⟨?_, ?_⟩, fun i j hj => ?_, ?_, ?_, ?_, fun i h1 hy => ?_⟩
  · refine ((k1.mono ?_).trans ((k2.mono ?_).trans ((k3.mono ?_).trans
      ((k4.mono ?_).trans (k5.mono ?_))))).trans (tk.mono ?_) <;> intro r hr <;> revert r <;> decide
  · exact (((((outV m1 (by omega) (by omega)).trans (outV o2 (by decide) (by decide))).trans
      (outV m3 (by decide) (by decide))).trans (outV m4 (by decide) (by decide))).trans
      (fmV m5 (by decide) (by decide))).trans (outV tm (by decide) (by decide))
  · have si := slot_range i
    rw [tl _ si.1 si.2 j hj]
    by_cases h1 : i = 1
    · subst i; exact b5 j hj
    · by_cases hy : i = yo
      · subst i; exact by5 j hj
      · rw [← tl _ si.1 si.2 j hj, other i h1 hy j hj]; exact hb i j hj
  · rw [tm.word (Or.inr (by decide)) (by decide), m5.word (Or.inl (by simp only [SIGN]; omega)) (by decide),
      m4.word (Or.inl (by simp only [SIGN]; omega)) (by decide),
      m3.word (Or.inr (by decide)) (by decide), m2]
    exact Mem.readW_writeW_self32 _ _ _
  · rw [bad3] at tb
    rw [bad2] at b3
    have h := b3.trans tb
    refine h.congr (and_congr_right fun _ => ?_)
    rw [limbs_eq_iff b5 by5, fe5, fy5]
    exact Nat.mod_eq_iff_lt (NeZero.ne Spec.X448.P)
  · simp only [E, F]
    rw [show fe t.mem base (slot yo.val) = fe s5.mem base (slot yo.val) from valN_congr (tl _ sy.1 sy.2),
      fy5]
  · simp only [E, F]
    exact congrArg Proof.X448.toFe (valN_congr (other i h1 hy))

end VG.Proof.Ed448.X86
