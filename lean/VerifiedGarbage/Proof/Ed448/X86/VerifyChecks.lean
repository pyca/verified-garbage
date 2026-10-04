import VerifiedGarbage.Proof.Ed448.X86.VerifyField
import VerifiedGarbage.Proof.X448.X86.Freeze
import VerifiedGarbage.Proof.X448.X86.Copy

/-!
# Ed448 verification's equation on x86 (32-bit): accumulating checks

The word at `BAD` accumulates checks: a check of `P` ORs into it a word below
`2^16` that is 0 exactly when `P` holds (`BadUpd`). Comparing the limbs of
slot 1 with those of another slot (`diffSlot_ok`), and two slots' field
elements, fully reduced (`eqSlots_ok`). `CKeep` is what the comparisons and
the field programs may change: the field operations' registers, the counter
`esi`, and the working space at `BAD`, in the slots and from `ACC`.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Impl.X448.X86 (slot X2 ACC TMP ld copy freeze)

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

theorem BadUpd.of_eq {P : Prop} {b b' b'' : BitVec 32} (h : BadUpd P b b') (e : b'' = b') :
    BadUpd P b b'' := e ▸ h

theorem BadUpd.zero {P : Prop} {b : BitVec 32} (h : BadUpd P 0 b) : (b = 0 ↔ P) ∧ b.toNat < 65536 := by
  obtain ⟨c, hc, hp, rfl⟩ := h
  have e : (0 : BitVec 32) ||| c = c := BitVec.zero_or
  rw [e]
  exact ⟨hp, hc⟩

/-- The working space changes only at `BAD`, in the slots and from `ACC`. -/
def BMem (base : Addr) (m m' : Mem) : Prop :=
  ∀ p, (ofs base p < BAD ∨ BAD + 4 ≤ ofs base p) → (ofs base p < 64 ∨ 2880 ≤ ofs base p) →
    (ofs base p < ACC ∨ ACC + 512 ≤ ofs base p) → m' p = m p

theorem BMem.refl (base : Addr) (m : Mem) : BMem base m m := fun _ _ _ _ => rfl

theorem BMem.trans {base : Addr} {m₁ m₂ m₃ : Mem} (h₁ : BMem base m₁ m₂) (h₂ : BMem base m₂ m₃) :
    BMem base m₁ m₃ := fun p a b c => (h₂ p a b c).trans (h₁ p a b c)

theorem BMem.of_outside2 {base : Addr} {m m' : Mem} (h : Outside2 base 64 2816 ACC 512 m m') :
    BMem base m m' := fun p _ hb hc => h p hb hc

theorem BMem.of_bad {base : Addr} {m m' : Mem} (h : Outside base BAD 4 m m') : BMem base m m' :=
  fun p ha _ _ => h p ha

theorem BMem.widen {base : Addr} {m m' : Mem} (h : BMem base m m') : Outside2 base 16 2864 ACC 512 m m' :=
  fun p ha hc => h p (by simp only [BAD]; omega) (by omega) hc

theorem BMem.word {base : Addr} {m m' : Mem} (h : BMem base m m') {d : Nat}
    (hb : d + 4 ≤ BAD ∨ BAD + 4 ≤ d) (hs : d + 4 ≤ 64 ∨ 2880 ≤ d) (ha : d + 4 ≤ ACC ∨ ACC + 512 ≤ d)
    (hd : d + 4 ≤ 8192) : word m' base d = word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [ofs_off base (by omega)]; omega)
    (by rw [ofs_off base (by omega)]; omega) (by rw [ofs_off base (by omega)]; omega)).symm).symm

/-- What comparisons and field programs may change. -/
structure CKeep (base : Addr) (s t : State) : Prop where
  regs : Keeps (.esi :: workRegs) s t
  mem : BMem base s.mem t.mem

theorem CKeep.refl (base : Addr) (s : State) : CKeep base s s := ⟨Keeps.refl _ _, BMem.refl _ _⟩

theorem CKeep.trans {base : Addr} {s t u : State} (h : CKeep base s t) (h' : CKeep base t u) :
    CKeep base s u := ⟨h.regs.trans h'.regs, h.mem.trans h'.mem⟩

theorem CKeep.toV {base : Addr} {s t : State} (h : CKeep base s t) : VKeep base s t :=
  ⟨h.regs, h.mem.widen⟩

theorem CKeep.scr {base : Addr} {s t : State} (h : CKeep base s t) (hs : Scr s base) : Scr t base :=
  hs.of_keeps h.regs (by decide)

theorem IKeep.toC {base : Addr} {s t : State} (h : IKeep base s t) : CKeep base s t :=
  ⟨h.regs, BMem.of_outside2 h.mem⟩

theorem Keep.toC {base : Addr} {s t : State} (h : Keep base s t) : CKeep base s t := IKeep.toC h.ikeep

/-! ## What the field programs keep -/

theorem Keep.bad {base : Addr} {s t : State} (h : Keep base s t) :
    word t.mem base BAD = word s.mem base BAD :=
  h.mem.word (Or.inl (by decide)) (Or.inl (by decide)) (by decide)

theorem IKeep.bad {base : Addr} {s t : State} (h : IKeep base s t) :
    word t.mem base BAD = word s.mem base BAD :=
  h.mem.word (Or.inl (by decide)) (Or.inl (by decide)) (by decide)

theorem CKeep.sign {base : Addr} {s t : State} (h : CKeep base s t) :
    word t.mem base SIGN = word s.mem base SIGN :=
  h.mem.word (Or.inr (by decide)) (Or.inl (by decide)) (Or.inl (by decide)) (by decide)

theorem orBad_ok {s : State} {base : Addr} (hs : Scr s base) {r : Reg} (hre : r ≠ .edi) {P : Prop}
    (hc : (s.gpr r).toNat < 65536) (hp : s.gpr r = 0 ↔ P) :
    WP isa (.block (orBad r)) s fun t =>
      BadUpd P (word s.mem base BAD) (word t.mem base BAD) ∧ Outside base BAD 4 s.mem t.mem ∧
        Keeps [r] s t := by
  unfold orBad
  refine wp_alu (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (rd_sc hs (by decide)) fun u hu _ => ?_
  refine store_ok (hs.of_upd hu (Ne.symm hre)) (by decide) fun v hv => WP.block_nil ⟨?_, ?_, ?_⟩
  · refine ⟨s.gpr r, hc, hp, ?_⟩
    rw [hv.mem, hu.mem, hu.gpr]
    change (s.mem.writeW (off base BAD) (s.gpr r ||| word s.mem base BAD)).readW (off base BAD) 32 = _
    rw [Mem.readW_writeW_self32]
    exact BitVec.or_comm _ _
  · rw [hv.mem, hu.mem]; exact writeW_outside _ _ _ (by decide)
  · exact (hu.rest (by simp)).trans (hv.rest _)

/-! ## Comparing limbs -/

theorem xor_limb {x y : BitVec 32} (hx : x.toNat < radix) (hy : y.toNat < radix) :
    (x ^^^ y).toNat < 65536 ∧ (x ^^^ y = 0 ↔ x.toNat = y.toNat) := by
  refine ⟨?_, BitVec.xor_eq_zero_iff.trans ⟨fun h => h ▸ rfl, BitVec.eq_of_toNat_eq⟩⟩
  rw [BitVec.toNat_xor]; exact Nat.xor_lt_two_pow (n := 16) hx hy

theorem diffLimb_ok {s : State} {base : Addr} (hs : Scr s base) {a i : Nat} (ha : a + 112 ≤ 4096)
    (hi : i < 28) :
    WP isa (.block (diffLimb a i)) s fun t =>
      t.gpr .ecx = s.gpr .ecx ||| (word s.mem base (X2 + 4 * i) ^^^ word s.mem base (a + 4 * i)) ∧
        t.mem = s.mem ∧ Keeps [.eax, .ecx] s t := by
  unfold diffLimb
  refine load_ok hs (by simp only [X2, slot]; omega) fun u hu => ?_
  have us := hs.of_upd hu (by decide)
  refine wp_alu (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (rd_sc us (by omega)) fun v hv _ => ?_
  refine wp_alu (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) rfl fun w hw _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [hw.gpr]
    change v.gpr .ecx ||| v.gpr .eax = _
    rw [hv.gpr, hv.other _ (by decide), hu.other _ (by decide), hu.gpr, hu.mem]
    rfl
  · rw [hw.mem, hv.mem, hu.mem]
  · exact (hu.rest (by simp)).trans ((hv.rest (by simp)).trans (hw.rest (by simp)))

theorem diffSlot_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (ha : a + 112 ≤ 4096)
    (h1 : Bounded s.mem base X2) (h2 : Bounded s.mem base a) :
    WP isa (.block (diffSlot a)) s fun t =>
      BadUpd (∀ i < 28, limbs s.mem base X2 i = limbs s.mem base a i) (word s.mem base BAD)
        (word t.mem base BAD) ∧ Outside base BAD 4 s.mem t.mem ∧ Keeps [.eax, .ecx] s t := by
  unfold diffSlot
  refine wp_mov rfl fun u hu => ?_
  have us := hs.of_upd hu (by decide)
  let inv := fun n (t : State) =>
    (t.gpr .ecx).toNat < 65536 ∧ (t.gpr .ecx = 0 ↔ ∀ i < n, limbs s.mem base X2 i = limbs s.mem base a i) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx] s t
  change WP isa (.block ((List.range 28).flatMap (diffLimb a) ++ orBad .ecx)) u _
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (N := 28) inv (fun n t hn ⟨tb, tz, tm, tk⟩ => ?_) 28
    (by decide) u ⟨by rw [hu.gpr]; decide, by rw [hu.gpr]; exact ⟨fun _ _ h => absurd h (Nat.not_lt_zero _),
      fun _ => rfl⟩, hu.mem, hu.rest (by simp)⟩) fun t ⟨tb, tz, tm, tk⟩ => ?_
  · refine WP.mono (diffLimb_ok (hs.of_keeps tk (by decide)) ha hn) fun v ⟨vc, vm, vk⟩ => ?_
    rw [tm] at vc
    have x := xor_limb (h1 n hn) (h2 n hn)
    refine ⟨?_, ?_, vm.trans tm, tk.trans (vk.mono (by simp))⟩
    · rw [vc, BitVec.toNat_or]; exact Nat.or_lt_two_pow (n := 16) tb x.1
    · rw [vc]
      refine BitVec.or_eq_zero_iff.trans ((and_congr tz x.2).trans ?_)
      constructor
      · rintro ⟨h, h'⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact h i hi
        · exact h'
      · intro h
        exact ⟨fun i hi => h i (by omega), h n (by omega)⟩
  · refine WP.mono (orBad_ok (hs.of_keeps tk (by decide)) (by decide) tb tz) fun v ⟨vb, vo, vk⟩ => ?_
    rw [tm] at vb vo
    exact ⟨vb, vo, tk.trans (vk.mono (by simp))⟩

/-! ## Comparing field elements -/

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

theorem outB {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (h1 : 64 ≤ o)
    (h2 : o + n ≤ 2880) : BMem base m m' := fun p _ hp _ => h p (by omega)

theorem fmB {base : Addr} {o : Nat} {m m' : Mem} (h : FieldMem base o m m') (h1 : 64 ≤ o)
    (h2 : o + 112 ≤ 2880) : BMem base m m' := fun p _ hp hq => h p (by omega) hq

/-- Slots `a` and `b` compared: `BAD |= 0` exactly when they hold the same field
element; slot `a` holds the same element, fully reduced, and slot 1 is
overwritten. -/
theorem eqSlots_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (a b : Index)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) :
    WP isa (.block (eqSlots (slot a.val) (slot b.val))) s fun t =>
      CKeep base s t ∧ BoundedEnv t.mem base ∧ (∀ i : Index, i ≠ 1 → E t.mem base i = E s.mem base i) ∧
        BadUpd (E s.mem base a = E s.mem base b) (word s.mem base BAD) (word t.mem base BAD) := by
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
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok hs (o := X2) (a := slot a.val) (by decide) (by omega)
    (Or.inr (by omega))) fun s1 ⟨f1, m1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  have bd1 : Bounded s1.mem base X2 := fun i hi => by rw [f1 i hi]; exact hb a i hi
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok hs1 bd1) fun s2 ⟨b2, v2, m2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  -- slot a = slot 1
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok hs2 (o := slot a.val) (a := X2) (by omega) (by decide)
    (Or.inr (by omega))) fun s3 ⟨f3, m3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by decide)
  -- slot 1 = slot b
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok hs3 (o := X2) (a := slot b.val) (by decide) (by omega)
    (Or.inr (by omega))) fun s4 ⟨f4, m4, k4⟩ => ?_
  have hs4 := hs3.of_keeps k4 (by decide)
  have lb3 : ∀ i < 28, limbs s3.mem base (slot b.val) i = limbs s.mem base (slot b.val) i := by
    intro i hi
    rw [m3.limbs (by omega) (by omega) hi, m2.limbs s1b (by omega) hi,
      m1.limbs (by omega) (by omega) hi]
  have bd4 : Bounded s4.mem base X2 := fun i hi => by rw [f4 i hi, lb3 i hi]; exact hb b i hi
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok hs4 bd4) fun s5 ⟨b5, v5, m5, k5⟩ => ?_
  have hs5 := hs4.of_keeps k5 (by decide)
  have la5 : ∀ i < 28, limbs s5.mem base (slot a.val) i = limbs s2.mem base X2 i := by
    intro i hi
    rw [m5.limbs s1a (by omega) hi, m4.limbs (by omega) (by omega) hi, f3 i hi]
  have ba5 : Bounded s5.mem base (slot a.val) := fun i hi => by rw [la5 i hi]; exact b2 i hi
  refine WP.mono (diffSlot_ok hs5 (by omega) b5 ba5) fun t ⟨tb, tm, tk⟩ => ?_
  have fa : fe s5.mem base (slot a.val) = fe s.mem base (slot a.val) % Spec.X448.P := by
    rw [show fe s5.mem base (slot a.val) = fe s2.mem base X2 from valN_congr la5, v2]
    exact congrArg (· % Spec.X448.P) (valN_congr f1)
  have fb : fe s5.mem base X2 = fe s.mem base (slot b.val) % Spec.X448.P := by
    rw [v5]; exact congrArg (· % Spec.X448.P) ((valN_congr f4).trans (valN_congr lb3))
  have tl : ∀ d, 64 ≤ d → d + 112 ≤ 2880 → ∀ j < 28, limbs t.mem base d j = limbs s5.mem base d j :=
    fun d h1 h2 j hj => tm.limbs (Or.inr (by simp only [BAD]; omega)) (by omega) hj
  have other : ∀ i : Index, i ≠ 1 → i ≠ a → ∀ j < 28,
      limbs t.mem base (slot i.val) j = limbs s.mem base (slot i.val) j := by
    intro i hi1 hia j hj
    have si := slot_range i
    have s1i : slot i.val + 112 ≤ X2 ∨ X2 + 112 ≤ slot i.val := by rw [hX2]; exact slot_sep hi1
    have sai := slot_sep hia
    rw [tl _ si.1 si.2 j hj, m5.limbs s1i (by omega) hj, m4.limbs (by omega) (by omega) hj,
      m3.limbs (by omega) (by omega) hj, m2.limbs s1i (by omega) hj,
      m1.limbs (by omega) (by omega) hj]
  refine ⟨⟨?_, ?_⟩, fun i j hj => ?_, fun i hi => ?_, ?_⟩
  · refine (((k1.mono ?_).trans ((k2.mono ?_).trans ((k3.mono ?_).trans ((k4.mono ?_).trans
      (k5.mono ?_))))).trans (tk.mono ?_)) <;> intro r hr <;> revert r <;> decide
  · exact (((((outB m1 (by decide) (by decide)).trans (fmB m2 (by decide) (by decide))).trans
      (outB m3 (by omega) (by omega))).trans (outB m4 (by decide) (by decide))).trans
      (fmB m5 (by decide) (by decide))).trans (BMem.of_bad tm)
  · have si := slot_range i
    rw [tl _ si.1 si.2 j hj]
    by_cases h1 : i = 1
    · subst i; exact b5 j hj
    · by_cases ha' : i = a
      · subst i; exact ba5 j hj
      · rw [← tl _ si.1 si.2 j hj, other i h1 ha' j hj]; exact hb i j hj
  · by_cases ha' : i = a
    · subst i
      simp only [E, F]
      rw [show fe t.mem base (slot a.val) = fe s5.mem base (slot a.val) from
        valN_congr (tl _ sa.1 sa.2), fa, Proof.X448.toFe_mod]
    · simp only [E, F]
      exact congrArg Proof.X448.toFe (valN_congr (other i hi ha'))
  · have bad5 : word s5.mem base BAD = word s.mem base BAD := by
      rw [m5.word (Or.inl (by simp only [BAD]; omega)) (by simp only [BAD, ACC]; omega),
        m4.word (Or.inl (by simp only [BAD]; omega)) (by decide),
        m3.word (Or.inl (by simp only [BAD]; omega)) (by decide),
        m2.word (Or.inl (by simp only [BAD]; omega)) (by simp only [BAD, ACC]; omega),
        m1.word (Or.inl (by simp only [BAD]; omega)) (by decide)]
    rw [bad5] at tb
    refine tb.congr ?_
    rw [limbs_eq_iff b5 ba5, fb, fa]
    simp only [E, F, Proof.X448.toFe_eq_iff]
    exact eq_comm

end VG.Proof.Ed448.X86
