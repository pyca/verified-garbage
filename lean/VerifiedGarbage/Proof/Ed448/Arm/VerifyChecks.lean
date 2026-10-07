import VerifiedGarbage.Proof.Ed448.Arm.VerifyField
import VerifiedGarbage.Proof.X448.Arm.Freeze

/-!
# Ed448 verification's equation on ARMv7: accumulating checks

`BAD` (`r10`) accumulates checks: a check of `P` ORs into it a word below
`2^16` that is 0 exactly when `P` holds (`BadUpd`). Comparing the limbs of
slot 1 with those of another slot (`diffSlot_ok`), and two slots' field
elements, fully reduced (`eqSlots_ok`).
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm VG.Proof.X448.Radix16
open VG.Impl.X448.Arm (slot X2 ACC TMP ld copy freeze)

/-! ## The accumulated word -/

/-- `b'` is `b` ORed with a word below `2^16` that is 0 exactly when `P` holds. -/
def BadUpd (P : Prop) (b b' : BitVec 32) : Prop :=
  ∃ c : BitVec 32, c.toNat < 65536 ∧ (c = 0 ↔ P) ∧ b' = b ||| c

theorem BadUpd.trans {P Q : Prop} {b b' b'' : BitVec 32} (h : BadUpd P b b') (h' : BadUpd Q b' b'') :
    BadUpd (P ∧ Q) b b'' := by
  obtain ⟨c, hc, hp, rfl⟩ := h
  obtain ⟨c', hc', hq, rfl⟩ := h'
  refine ⟨c ||| c', ?_, ?_, BitVec.or_assoc _ _ _⟩
  · rw [BitVec.toNat_or]; exact Nat.or_lt_two_pow (n := 16) hc hc'
  · rw [← hp, ← hq]; exact BitVec.or_eq_zero_iff

theorem BadUpd.congr {P Q : Prop} {b b' : BitVec 32} (h : BadUpd P b b') (e : P ↔ Q) : BadUpd Q b b' := by
  obtain ⟨c, hc, hp, rfl⟩ := h
  exact ⟨c, hc, hp.trans e, rfl⟩

theorem BadUpd.rfl' {b : BitVec 32} : BadUpd True b b :=
  ⟨0, by decide, ⟨fun _ => trivial, fun _ => rfl⟩, (BitVec.or_zero).symm⟩

theorem orBad_ok {s : State} {P : Prop} (hc : (s.gpr .r3).toNat < 65536) (hp : s.gpr .r3 = 0 ↔ P) :
    WP isa (.block orBad) s fun t =>
      BadUpd P (s.gpr .r10) (t.gpr .r10) ∧ t.mem = s.mem ∧ Keeps [.r10] s t := by
  unfold orBad
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun t ht =>
    WP.block_nil ⟨⟨s.gpr .r3, hc, hp, ht.gpr⟩, ht.mem, rest_keeps (ht.rest (by decide))⟩

/-! ## Comparing limbs -/

theorem xor_limb {x y : BitVec 32} (hx : x.toNat < radix) (hy : y.toNat < radix) :
    (x ^^^ y).toNat < 65536 ∧ (x ^^^ y = 0 ↔ x.toNat = y.toNat) := by
  refine ⟨?_, BitVec.xor_eq_zero_iff.trans ⟨fun h => h ▸ rfl, BitVec.eq_of_toNat_eq⟩⟩
  rw [BitVec.toNat_xor]; exact Nat.xor_lt_two_pow (n := 16) hx hy

theorem diffLimb_ok {s : State} {base : Addr} (hs : Scr s base) {a i : Nat} (ha : a + 112 ≤ 4096)
    (hi : i < 28) (h1 : limbs s.mem base X2 i < radix) (h2 : limbs s.mem base a i < radix) :
    WP isa (.block (diffLimb a i)) s fun t =>
      BadUpd (limbs s.mem base X2 i = limbs s.mem base a i) (s.gpr .r10) (t.gpr .r10) ∧
        t.mem = s.mem ∧ Keeps [.r3, .r2, .r10] s t := by
  unfold diffLimb
  refine load_ok hs (by simp only [X2, slot]; omega) fun u hu => ?_
  refine load_ok (hs.of_upd hu (by decide) (by decide)) (by omega) fun v hv => ?_
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun w hw => ?_
  have x := xor_limb (x := word s.mem base (X2 + 4 * i)) (y := word s.mem base (a + 4 * i)) h1 h2
  refine WP.mono (orBad_ok (P := limbs s.mem base X2 i = limbs s.mem base a i)
    (by rw [hw.gpr, hv.other _ (by decide), hu.gpr, hv.gpr, hu.mem]; exact x.1)
    (by rw [hw.gpr, hv.other _ (by decide), hu.gpr, hv.gpr, hu.mem]; exact x.2))
    fun t ⟨tb, tm, tk⟩ => ⟨?_, ?_, ?_⟩
  · rw [hw.other _ (by decide), hv.other _ (by decide), hu.other _ (by decide)] at tb; exact tb
  · rw [tm, hw.mem, hv.mem, hu.mem]
  · exact (rest_keeps (ws := [.r3, .r2, .r10]) ((hu.rest (by decide)).trans ((hv.rest (by decide)).trans
      (hw.rest (by decide))))).trans (tk.mono (by decide))

theorem diffSlot_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (ha : a + 112 ≤ 4096)
    (h1 : Bounded s.mem base X2) (h2 : Bounded s.mem base a) :
    WP isa (.block (diffSlot a)) s fun t =>
      BadUpd (∀ i < 28, limbs s.mem base X2 i = limbs s.mem base a i) (s.gpr .r10) (t.gpr .r10) ∧
        t.mem = s.mem ∧ Keeps [.r3, .r2, .r10] s t := by
  let inv := fun n (t : State) =>
    BadUpd (∀ i < n, limbs s.mem base X2 i = limbs s.mem base a i) (s.gpr .r10) (t.gpr .r10) ∧
      t.mem = s.mem ∧ Keeps [.r3, .r2, .r10] s t
  refine wp_range_flatMap (M := isa) (N := 28) inv (fun n t hn ⟨tb, tm, tk⟩ => ?_) 28 (by decide) s
    ⟨BadUpd.rfl'.congr ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ => trivial⟩, rfl,
      Keeps.refl _ _⟩
  refine WP.mono (diffLimb_ok (hs.of_keeps tk (by decide)) ha hn (tm ▸ h1 n hn) (tm ▸ h2 n hn))
    fun u ⟨ub, um, uk⟩ => ⟨?_, um.trans tm, tk.trans uk⟩
  rw [tm] at ub
  refine (tb.trans ub).congr ⟨fun ⟨h, h'⟩ i hi => ?_, fun h => ⟨fun i hi => h i (by omega), h n (by omega)⟩⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · exact h i hi
  · exact h'

/-! ## Comparing field elements -/

theorem slot_range (i : Index) : 64 ≤ slot i.val ∧ slot i.val + 112 ≤ 2880 := by
  have := i.isLt
  simp only [slot]
  omega

theorem outC {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (h1 : 64 ≤ o)
    (h2 : o + n ≤ 2880) : Outside2 base 64 2816 ACC 512 m m' := fun p hp _ => h p (by omega)

theorem fmC {base : Addr} {o : Nat} {m m' : Mem} (h : FieldMem base o m m') (h1 : 64 ≤ o)
    (h2 : o + 112 ≤ 2880) : Outside2 base 64 2816 ACC 512 m m' := fun p hp hq => h p (by omega) hq

theorem outV {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (h1 : 32 ≤ o)
    (h2 : o + n ≤ 2880) : Outside2 base 32 2848 ACC 512 m m' := fun p hp _ => h p (by omega)

theorem fmV {base : Addr} {o : Nat} {m m' : Mem} (h : FieldMem base o m m') (h1 : 32 ≤ o)
    (h2 : o + 112 ≤ 2880) : Outside2 base 32 2848 ACC 512 m m' := fun p hp hq => h p (by omega) hq

theorem valN_inj {f g : Nat → Nat} :
    ∀ {n}, (∀ i < n, f i < radix) → (∀ i < n, g i < radix) → valN f n = valN g n → ∀ i < n, f i = g i
  | 0, _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, hf, hg, h, i, hi => by
    rw [valN_succ, valN_succ] at h
    have lf := valN_lt (n := n) (fun j hj => hf j (by omega))
    have lg := valN_lt (n := n) (fun j hj => hg j (by omega))
    have hp : 0 < radix ^ n := Nat.pow_pos (by decide)
    have e1 : f n = g n := by
      have := congrArg (· / radix ^ n) h
      simp only [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt lf, Nat.div_eq_of_lt lg, Nat.zero_add] at this
      exact this
    rw [e1] at h
    have e0 : valN f n = valN g n := by omega
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact valN_inj (fun j hj => hf j (by omega)) (fun j hj => hg j (by omega)) e0 i hi
    · exact e1

theorem limbs_eq_iff {m : Mem} {base : Addr} {a b : Nat} (ha : Bounded m base a) (hb : Bounded m base b) :
    (∀ i < 28, limbs m base a i = limbs m base b i) ↔ fe m base a = fe m base b :=
  ⟨fun h => valN_congr h, fun h => valN_inj ha hb h⟩

/-- Slots `a` and `b` compared: `BAD |= 0` exactly when they hold the same field
element; slot `a` holds the same element, fully reduced, and slot 1 is
overwritten. -/
theorem eqSlots_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (a b : Index)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) :
    WP isa (.block (eqSlots (slot a.val) (slot b.val))) s fun t =>
      CKeep base s t ∧ BoundedEnv t.mem base ∧ (∀ i : Index, i ≠ 1 → E t.mem base i = E s.mem base i) ∧
        BadUpd (E s.mem base a = E s.mem base b) (s.gpr .r10) (t.gpr .r10) := by
  have sa := slot_range a
  have sb := slot_range b
  have hX2v : X2 = 192 := rfl
  have hA : ACC = 3584 := rfl
  have hX2 : X2 = slot (1 : Index).val := rfl
  have s1a : slot a.val + 112 ≤ X2 ∨ X2 + 112 ≤ slot a.val := by rw [hX2]; exact slot_sep ha1
  have s1b : slot b.val + 112 ≤ X2 ∨ X2 + 112 ≤ slot b.val := by rw [hX2]; exact slot_sep hb1
  have sab := slot_sep hab
  unfold eqSlots
  simp only [List.append_assoc]
  -- slot 1 = slot a
  refine VG.Proof.X25519.Arm.WP.append (copy_ok hs (o := X2) (a := slot a.val) (by decide) (by omega)
    (Or.inr (by omega))) fun s1 ⟨f1, m1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  have bd1 : Bounded s1.mem base X2 := fun i hi => by rw [f1 i hi]; exact hb a i hi
  refine VG.Proof.X25519.Arm.WP.append (freeze_ok hs1 bd1) fun s2 ⟨b2, v2, m2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  -- slot a = slot 1
  refine VG.Proof.X25519.Arm.WP.append (copy_ok hs2 (o := slot a.val) (a := X2) (by omega) (by decide)
    (Or.inr (by omega))) fun s3 ⟨f3, m3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by decide)
  -- slot 1 = slot b
  refine VG.Proof.X25519.Arm.WP.append (copy_ok hs3 (o := X2) (a := slot b.val) (by decide) (by omega)
    (Or.inr (by omega))) fun s4 ⟨f4, m4, k4⟩ => ?_
  have hs4 := hs3.of_keeps k4 (by decide)
  -- what each stage leaves
  have lb3 : ∀ i < 28, limbs s3.mem base (slot b.val) i = limbs s.mem base (slot b.val) i := by
    intro i hi
    rw [m3.limbs (by omega) (by omega) hi, m2.limbs s1b (by omega) hi,
      m1.limbs (by omega) (by omega) hi]
  have bd4 : Bounded s4.mem base X2 := fun i hi => by rw [f4 i hi, lb3 i hi]; exact hb b i hi
  refine VG.Proof.X25519.Arm.WP.append (freeze_ok hs4 bd4) fun s5 ⟨b5, v5, m5, k5⟩ => ?_
  have hs5 := hs4.of_keeps k5 (by decide)
  have la5 : ∀ i < 28, limbs s5.mem base (slot a.val) i = limbs s2.mem base X2 i := by
    intro i hi
    rw [m5.limbs s1a (by omega) hi, m4.limbs (by omega) (by omega) hi, f3 i hi]
  have ba5 : Bounded s5.mem base (slot a.val) := fun i hi => by rw [la5 i hi]; exact b2 i hi
  refine WP.mono (diffSlot_ok hs5 (by omega) b5 ba5) fun t ⟨tb, tm, tk⟩ => ?_
  -- the values
  have fa : fe s5.mem base (slot a.val) = fe s.mem base (slot a.val) % Spec.X448.P := by
    rw [show fe s5.mem base (slot a.val) = fe s2.mem base X2 from valN_congr la5, v2]
    exact congrArg (· % Spec.X448.P) (valN_congr f1)
  have fb : fe s5.mem base X2 = fe s.mem base (slot b.val) % Spec.X448.P := by
    rw [v5]; exact congrArg (· % Spec.X448.P) ((valN_congr f4).trans (valN_congr lb3))
  -- the other slots
  have other : ∀ i : Index, i ≠ 1 → i ≠ a → ∀ j < 28,
      limbs t.mem base (slot i.val) j = limbs s.mem base (slot i.val) j := by
    intro i hi1 hia j hj
    have si := slot_range i
    have s1i : slot i.val + 112 ≤ X2 ∨ X2 + 112 ≤ slot i.val := by rw [hX2]; exact slot_sep hi1
    have sai := slot_sep hia
    rw [tm, m5.limbs s1i (by omega) hj, m4.limbs (by omega) (by omega) hj,
      m3.limbs (by omega) (by omega) hj, m2.limbs s1i (by omega) hj,
      m1.limbs (by omega) (by omega) hj]
  refine ⟨⟨?_, ?_⟩, fun i j hj => ?_, fun i hi => ?_, ?_⟩
  · refine (((k1.mono ?_).trans ((k2.mono ?_).trans ((k3.mono ?_).trans ((k4.mono ?_).trans
      (k5.mono ?_))))).trans (tk.mono ?_)) <;> intro r hr <;> revert r <;> decide
  · rw [tm]
    exact ((((outC m1 (by decide) (by decide)).trans (fmC m2 (by decide) (by decide))).trans
      (outC m3 (by omega) (by omega))).trans (outC m4 (by decide) (by decide))).trans
      (fmC m5 (by decide) (by decide))
  · by_cases h1 : i = 1
    · subst i; rw [tm]; exact b5 j hj
    · by_cases ha' : i = a
      · subst i; rw [tm]; exact ba5 j hj
      · rw [other i h1 ha' j hj]; exact hb i j hj
  · by_cases ha' : i = a
    · subst i
      simp only [E, F]
      rw [tm, fa, Proof.X448.toFe_mod]
    · simp only [E, F]
      exact congrArg Proof.X448.toFe (valN_congr (other i hi ha'))
  · have r10 : s5.gpr .r10 = s.gpr .r10 := by
      rw [k5.1 _ (by decide), k4.1 _ (by decide), k3.1 _ (by decide), k2.1 _ (by decide),
        k1.1 _ (by decide)]
    rw [r10] at tb
    refine tb.congr ?_
    rw [limbs_eq_iff b5 ba5, fb, fa]
    simp only [E, F, Proof.X448.toFe_eq_iff]
    exact eq_comm
