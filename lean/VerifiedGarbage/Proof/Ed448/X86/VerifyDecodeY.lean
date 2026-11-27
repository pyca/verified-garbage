module
public import VerifiedGarbage.Proof.Ed448.X86.VerifyChecks

public import VerifiedGarbage.Proof.Ed448.X86.VerifyS
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.X448.X86.Freeze
import VerifiedGarbage.Proof.X448.X86.Copy
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Ed448 verification's equation on x86 (32-bit): the `y` of a point

`decodeY_ok`: the 57 bytes of an encoded point at `q` (the argument read from
the stack into `esi`): the fourteen words of the first 56 (`y₀`) into
slot `yo`, the sign bit (bit 7 of the last byte `b`) to `SIGN`, and
`BAD |= 0` exactly when bits 0–6 of `b` are 0 and `y₀ < p` (`y₀` is equal to
its full reduction, in slot 1).
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448.X86 VG.Proof.X448.X86
open VG.Impl.X448.X86 (slot X2 ACC ld st copy freeze at_)
open VG.Proof.X25519.X86 (num num_congr)

theorem loadLimbs_ok {s : State} {base q : Addr} (hs : Scr s base) (hq : (s.gpr .esi).setWidth 64 = q)
    (hfit : (s.gpr .esi).toNat + 57 ≤ 2 ^ 32)
    (hr : ∀ k < 14, InRegions (s.rd ++ s.wr) (off q (4 * k)) 4)
    (hd : ∀ j < 56, 8192 ≤ ofs base (q + BitVec.ofNat 64 j)) {o : Nat} (ho : 16 ≤ o ∧ o + 56 ≤ 4096) :
    WP isa (.block (loadLimbs o)) s fun t =>
      (∀ i < 14, limbs t.mem base o i = strW s.mem q i) ∧
        Outside base o 56 s.mem t.mem ∧ Keeps [.eax] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base o i = strW s.mem q i) ∧
      Outside base o 56 s.mem t.mem ∧ Keeps [.eax] s t
  refine wp_range_flatMap (M := isa) (N := 14) inv (fun n t hn ⟨tf, tm, tk⟩ => ?_) 14 (by decide) s
    ⟨fun _ h => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩
  obtain eq : t.mem.readW (off q (4 * n)) 32 = s.mem.readW (off q (4 * n)) 32 :=
    (Mem.readW_congr fun j hj => by
      rw [off, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact (tm _ (Or.inr (by have := hd (4 * n + j) (by omega_using [hn, hj]); omega_using [ho, this]))).symm).symm
  obtain te : t.gpr .esi = s.gpr .esi := tk.1 _ (by decide)
  refine wp_load (a := off q (4 * n)) (by
    change addr (t.gpr .esi) (4 * n) = _
    rw [te, addr_eq (by omega_using [hfit, hn]), hq]) (by rw [tk.2.1, tk.2.2]; exact hr n hn) fun u hu => ?_
  refine store_ok ((hs.of_keeps tk (by decide)).of_upd hu (by decide)) (by omega_using [ho, hn]) fun v hv =>
    WP.block_nil ⟨fun i hi => ?_, tm.trans ?_, tk.trans ((hu.rest (by simp)).trans (hv.rest _))⟩
  · change (word v.mem base (o + 4 * i)).toNat = _
    rw [hv.mem, hu.mem, hu.gpr, word_write t.mem base (by omega_using [ho, hn]) (by omega_using [ho, hn, hi])]
    by_cases h : i = n
    · rw [ite_eq_left h, h, eq]
    · rw [ite_eq_right h]; exact tf i (by omega_using [hi, h])
  · rw [hv.mem, hu.mem]; exact (writeW_outside _ _ _ (by omega_using [ho, hn])).mono (by omega_using []) (by omega_using [hn])

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
        exact ea_esi (by rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero, hq]) (by omega_using [hfit])) hr
    fun u hu => ?_
  refine wp_mov rfl fun v hv => ?_
  refine wp_shift (by decide) fun w hw => ?_
  obtain sw := ((hs.of_upd hu (by decide)).of_upd hv (by decide)).of_upd hw (by decide)
  refine store_ok sw (by decide) fun x hx => ?_
  refine wp_alu (Or.inr (Or.inr (Or.inl rfl))) rfl fun y hy _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [hy.gpr]; change (x.gpr .eax &&& 0x7f#32).toNat = _
    rw [hx.gpr, hw.other _ (by decide), hv.other _ (by decide), hu.gpr, BitVec.toNat_and,
      BitVec.toNat_setWidth, show (0x7f#32).toNat = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    have := (s.mem (q + BitVec.ofNat 64 56)).isLt
    omega_using []
  · rw [hy.mem, hx.mem, hw.mem, hv.mem, hu.mem, hw.gpr]
    change s.mem.writeW _ (v.gpr .edx >>> 7) = _
    rw [hv.gpr, hu.gpr]
    congr 1
    apply BitVec.eq_of_toNat_eq
    have := (s.mem (q + BitVec.ofNat 64 56)).isLt
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega_using []
  · exact (hu.rest (by simp)).trans ((hv.rest (by simp)).trans ((hw.rest (by simp)).trans
      ((hx.rest _).trans (hy.rest (by simp)))))

/-- `decodeY yo`, for the pointer `p` in `esi`. -/
theorem decodeY_ok {s : State} {base : Addr} (hs : Scr s base)
    {p : BitVec 32} (hp : s.gpr .esi = p) (hfit : p.toNat + 57 ≤ 2 ^ 32)
    (hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (p.setWidth 64 + BitVec.ofNat 64 j) 1)
    (hr4 : ∀ k < 14, InRegions (s.rd ++ s.wr) (off (p.setWidth 64) (4 * k)) 4)
    (hd : ∀ j < 57, 8192 ≤ ofs base (p.setWidth 64 + BitVec.ofNat 64 j)) (yo : Index) (hyo : yo ≠ 1) :
    WP isa (.block (decodeY yo.val)) s fun t =>
      VKeep base s t ∧
      word t.mem base SIGN = BitVec.ofNat 32 ((s.mem (p.setWidth 64 + BitVec.ofNat 64 56)).toNat / 128) ∧
      BadUpd ((s.mem (p.setWidth 64 + BitVec.ofNat 64 56)).toNat % 128 = 0 ∧
        num (strW s.mem (p.setWidth 64)) 14 < Spec.X448.P) (word s.mem base BAD) (word t.mem base BAD) ∧
      E t.mem base yo = Proof.X448.toFe (num (strW s.mem (p.setWidth 64)) 14) ∧
      (∀ i : Index, i ≠ 1 → i ≠ yo → E t.mem base i = E s.mem base i) := by
  generalize hq : p.setWidth 64 = q at hr hr4 hd ⊢
  obtain sy := slot_range yo
  have hX2v : X2 = 192 := rfl
  have hA : ACC = 3584 := rfl
  have hX2 : X2 = slot (1 : Index).val := rfl
  obtain s1y : slot yo.val + 56 ≤ X2 ∨ X2 + 56 ≤ slot yo.val := by rw [hX2]; exact slot_sep hyo
  unfold decodeY
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loadLimbs_ok hs (by rw [hp, hq]) (by rw [hp]; exact hfit)
    hr4 (fun j hj => hd j (by omega_using [hj]))
    (o := slot yo.val) ⟨by omega_using [sy], by omega_using [sy]⟩) fun s1 ⟨f1, m1, k1⟩ => ?_
  obtain hs1 := hs.of_keeps k1 (by decide)
  obtain b56 : s1.mem (q + BitVec.ofNat 64 56) = s.mem (q + BitVec.ofNat 64 56) :=
    m1 _ (Or.inr (by have := hd 56 (by decide); omega_using [sy, this]))
  rw [WP.block_append_iff]
  refine WP.mono (signByte_ok hs1 (q := q) (by rw [k1.1 _ (by decide), hp, hq])
    (by rw [k1.1 _ (by decide), hp]; exact hfit) (by rw [k1.2.1, k1.2.2]; exact hr 56 (by decide)))
    fun s2 ⟨r2, m2, k2⟩ => ?_
  rw [b56] at r2 m2
  obtain hs2 := hs1.of_keeps k2 (by decide)
  obtain o2 : Outside base SIGN 4 s1.mem s2.mem := by rw [m2]; exact writeW_outside _ _ _ (by decide)
  obtain l2 : ∀ i < 14, limbs s2.mem base (slot yo.val) i = strW s.mem q i := fun i hi => by
    rw [o2.limbs (Or.inr (by simp only [SIGN]; omega_using [sy])) (by omega_using [sy]) hi, f1 i hi]
  rw [WP.block_append_iff]
  refine WP.mono (orBad_ok (s := s2) hs2 (by decide)
    (P := (s.mem (q + BitVec.ofNat 64 56)).toNat % 128 = 0)
    (by rw [← r2]; exact ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩))
    fun s3 ⟨b3, m3, k3⟩ => ?_
  obtain hs3 := hs2.of_keeps k3 (by decide)
  obtain l3 : ∀ i < 14, limbs s3.mem base (slot yo.val) i = strW s.mem q i := fun i hi => by
    rw [m3.limbs (Or.inr (by simp only [BAD]; omega_using [sy])) (by omega_using [sy]) hi, l2 i hi]
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok hs3 (o := X2) (a := slot yo.val) (by decide) (by omega_using [sy])
    (Or.inr (by omega_using [s1y]))) fun s4 ⟨f4, m4, k4⟩ => ?_
  obtain hs4 := hs3.of_keeps k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok hs4) fun s5 ⟨v5, m5, k5⟩ => ?_
  obtain hs5 := hs4.of_keeps k5 (by decide)
  obtain l5 : ∀ i < 14, limbs s5.mem base (slot yo.val) i = strW s.mem q i := fun i hi => by
    rw [m5.limbs s1y (by omega_using [sy, hA]) hi, m4.limbs (by omega_using [s1y]) (by omega_using [sy]) hi, l3 i hi]
  refine WP.mono (diffSlot_ok hs5 (by omega_using [sy])) fun t ⟨tb, tm, tk⟩ => ?_
  obtain fe5 : fe s5.mem base X2 = num (strW s.mem q) 14 % Spec.X448.P := by
    rw [v5]; exact congrArg (· % Spec.X448.P) ((num_congr f4).trans (num_congr l3))
  obtain fy5 : fe s5.mem base (slot yo.val) = num (strW s.mem q) 14 := num_congr l5
  obtain tl : ∀ dd, 64 ≤ dd → dd + 56 ≤ 2880 → ∀ j < 14, limbs t.mem base dd j = limbs s5.mem base dd j :=
    fun dd h1 h2 j hj => tm.limbs (Or.inr (by simp only [BAD]; omega_using [h1])) (by omega_using [h2]) hj
  obtain other : ∀ i : Index, i ≠ 1 → i ≠ yo → ∀ j < 14,
      limbs t.mem base (slot i.val) j = limbs s.mem base (slot i.val) j := by
    intro i hi1 hiy j hj
    obtain si := slot_range i
    obtain s1i : slot i.val + 56 ≤ X2 ∨ X2 + 56 ≤ slot i.val := by rw [hX2]; exact slot_sep hi1
    obtain syi := slot_sep hiy
    rw [tl _ si.1 si.2 j hj, m5.limbs s1i (by omega_using [hA, si]) hj, m4.limbs (by omega_using [s1i]) (by omega_using [si]) hj,
      m3.limbs (Or.inr (by simp only [BAD]; omega_using [si])) (by omega_using [si]) hj,
      o2.limbs (Or.inr (by simp only [SIGN]; omega_using [si])) (by omega_using [si]) hj, m1.limbs (by omega_using [syi]) (by omega_using [si]) hj]
  obtain bad3 : word s5.mem base BAD = word s3.mem base BAD := by
    rw [m5.word (Or.inl (by simp only [BAD]; omega_using [hX2v])) (by simp only [BAD, ACC]; omega_using []),
      m4.word (Or.inl (by simp only [BAD]; omega_using [hX2v])) (by decide)]
  obtain bad2 : word s2.mem base BAD = word s.mem base BAD := by
    rw [o2.word (Or.inl (by decide)) (by decide), m1.word (Or.inl (by simp only [BAD]; omega_using [sy])) (by decide)]
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, fun i h1 hy => ?_⟩
  · refine ((k1.mono ?_).trans ((k2.mono ?_).trans ((k3.mono ?_).trans
      ((k4.mono ?_).trans (k5.mono ?_))))).trans (tk.mono ?_) <;> intro r hr <;> revert r <;> decide
  · exact (((((outV m1 (by omega_using [sy]) (by omega_using [sy])).trans (outV o2 (by decide) (by decide))).trans
      (outV m3 (by decide) (by decide))).trans (outV m4 (by decide) (by decide))).trans
      (fmV m5 (by decide) (by decide))).trans (outV tm (by decide) (by decide))
  · rw [tm.word (Or.inr (by decide)) (by decide), m5.word (Or.inl (by simp only [SIGN]; omega_using [hX2v])) (by decide),
      m4.word (Or.inl (by simp only [SIGN]; omega_using [hX2v])) (by decide),
      m3.word (Or.inr (by decide)) (by decide), m2]
    exact Mem.readW_writeW_self32 _ _ _
  · rw [bad3] at tb
    rw [bad2] at b3
    obtain h := b3.trans tb
    refine h.congr (and_congr_right fun _ => ?_)
    rw [limbs_eq_iff, fe5, fy5]
    exact Nat.mod_eq_iff_lt (NeZero.ne Spec.X448.P)
  · simp only [E, F]
    rw [show fe t.mem base (slot yo.val) = fe s5.mem base (slot yo.val) from num_congr (tl _ sy.1 sy.2),
      fy5]
  · simp only [E, F]
    exact congrArg Proof.X448.toFe (num_congr (other i h1 hy))

end VG.Proof.Ed448.X86
