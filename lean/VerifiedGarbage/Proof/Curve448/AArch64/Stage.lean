module

public import VerifiedGarbage.Impl.Curve448.AArch64
public import VerifiedGarbage.Proof.Curve448.AArch64.Normalize
public import VerifiedGarbage.Proof.X448.AArch64.Mul
public import VerifiedGarbage.Proof.X448.Wide.Memory
import VerifiedGarbage.Proof.X448.Wide.CoefficientIO
import VerifiedGarbage.Proof.X448.Wide.Pass
import VerifiedGarbage.Proof.X448.Wide.Fold
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Curve448.AArch64.Copy`, which the modules that import this one used -/

section

/-!
# X448 on AArch64: copying field elements

Untrusted: everything here is checked by Lean. Eight persistent limbs are copied. Source and destination are
equal or disjoint; every limb is copied without changing its representation.
-/

@[expose] public section

namespace VG.Proof.Curve448.AArch64

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st)
open VG.Proof.X448.AArch64
open VG.Impl.Curve448.AArch64

theorem copyStep_ok {s : State} {base : Addr} (hs : Scr s base) {o a i : Nat}
    (ho : o + 128 ≤ 8192) (ha : a + 128 ≤ 8192) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0) (hi : i < 8) :
    WP isa (.block [ld .x4 (a + 8 * i), st .x4 (o + 8 * i)]) s fun t =>
      t.mem = s.mem.writeW (off base (o + 8 * i)) (word s.mem base (a + 8 * i)) ∧ Keeps clob s t := by
  have l := hs.read (d := a + 8 * i) (n := 8) (by omega_using [ha, hi])
  have w := hs.write (d := o + 8 * i) (n := 8) (by omega_using [ho, hi])
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := ⟨by omega_using [ha8], by omega_using [ha, hi]⟩
  have oe : (o + 8 * i) % 8 = 0 ∧ o + 8 * i < 32768 := ⟨by omega_using [ho8], by omega_using [ho, hi]⟩
  apply WP.of_runBlock
  simp only [ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    State.read, State.load, State.store, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.wr_write, BitVec.setWidth_eq, ae, oe, and_self, hs.x3, l, w,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, read8_eq, write8_eq,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, (fun r hr => ?_), rfl, rfl⟩
  exact RegUpd.gpr_write_of_ne _ _ _ (fun h => hr (by subst r; decide))

theorem copy_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : o + 128 ≤ 8192) (ha : a + 128 ≤ 8192) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (hsep : o = a ∨ o + 128 ≤ a ∨ a + 128 ≤ o) :
    WP isa (.block (copy o a)) s fun t =>
      (∀ i < 8, limbs t.mem base o i = limbs s.mem base a i) ∧
      Outside base o 128 s.mem t.mem ∧ Keeps clob s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base o i = limbs s.mem base a i) ∧
    (∀ i, n ≤ i → i < 8 → limbs t.mem base a i = limbs s.mem base a i) ∧
    Outside base o 128 s.mem t.mem ∧ Keeps clob s t
  have st : ∀ n t, n < 8 → inv n t →
      WP isa (.block [ld .x4 (a + 8 * n), st .x4 (o + 8 * n)]) t (inv (n + 1)) := by
    intro n t hn ⟨tf, ta, tm, tk⟩
    refine WP.mono (copyStep_ok (hs.of_keeps tk (by decide)) ho ha ho8 ha8 hn) fun u ⟨um, uk⟩ => ?_
    have out : Outside base (o + 8 * n) 8 t.mem u.mem := by
      rw [um]; exact writeW_outside _ _ _ (by omega_using [ho, hn])
    refine ⟨?_, ?_, tm.trans (out.mono (by omega_using []) (by omega_using [hn])), tk.trans uk⟩
    · intro i hi
      change (word u.mem base (o + 8 * i)).toNat = _
      rw [um, word_write t.mem base (by omega_using [ho, hn]) (by omega_using [ho, hn, hi])]
      by_cases h : i = n
      · rw [ite_eq_left h, h]; exact ta n (by omega_using []) hn
      · rw [ite_eq_right h]; exact tf i (by omega_using [hi, h])
    · intro i hi hi'
      change (word u.mem base (a + 8 * i)).toNat = _
      rw [out.word (by rcases hsep with h | h | h <;> omega_arith) (by omega_using [ha, hi'])]
      exact ta i (by omega_using [hi]) hi'
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv st 8 (by decide) s ?_)
    fun t ⟨tf, _, tm, tk⟩ => ⟨tf, tm, tk⟩
  exact ⟨fun _ hi => by omega, fun _ _ _ => rfl, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.Curve448.AArch64

end

end

@[expose] public section

namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ld st TMP ACC)
open VG.Proof.X448.AArch64

/-- Stage all inputs before writing the output, including aliasing cases. -/
theorem stage_ok {s : State} {base : Addr} (hs : Scr s base)
    {code : Nat → List Instr} {f : Nat → Nat}
    (heval : ∀ i < 8, ∀ t, Scr t base → Outside base TMP 128 s.mem t.mem →
      WP isa (.block (code i)) t fun u =>
        pair (u.gpr .x4) (u.gpr .x5) = f i ∧ u.mem = t.mem ∧ Keeps clob t u) :
    WP isa (.block ((List.range 8).flatMap (fun i => code i ++ Impl.Curve448.AArch64.storeCoeff i))) s fun t =>
      (∀ i < 8, coeff t.mem base TMP i = f i) ∧
      Outside base TMP 128 s.mem t.mem ∧ Keeps clob s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, coeff t.mem base TMP i = f i) ∧
    Outside base TMP 128 s.mem t.mem ∧ Keeps clob s t
  have step : ∀ n t, n < 8 → inv n t →
      WP isa (.block (code n ++ Impl.Curve448.AArch64.storeCoeff n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    rw [WP.block_append_iff]
    refine WP.mono (heval n hn t (hs.of_keeps tk (by decide)) tm) fun u ⟨uv, um, uk⟩ => ?_
    refine WP.mono (storeAt_ok ((hs.of_keeps tk (by decide)).of_keeps uk (by decide))
      (o := TMP) (k := n) (by simp only [TMP]; omega_using [hn]) (by decide)) fun v ⟨vm, vk⟩ => ?_
    have out : Outside base (TMP + 16 * n) 16 t.mem v.mem := by
      rw [vm, um]; exact putCoeff_outside _ _ _ _ (by simp only [TMP]; omega_using [hn])
    refine ⟨?_, tm.trans (out.mono (by omega_using []) (by omega_using [hn])), tk.trans (uk.trans (vk.mono (by decide)))⟩
    intro i hi
    rw [vm, coeff_put _ base _ _ (by simp only [TMP]; omega_using [hn]) (by simp only [TMP]; omega_using [hn, hi])]
    by_cases h : i = n
    · subst i; rw [ite_eq_left rfl]; exact uv
    · rw [ite_eq_right h, um]; exact tf i (by omega_using [hi, h])
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

theorem input_limb {base : Addr} {a : Nat} {m m' : Mem}
    (h : Outside base TMP 128 m m') (ha : Slot a) {i : Nat} (hi : i < 8) :
    limbs m' base a i = limbs m base a i :=
  h.limbs (Or.inl (Nat.le_trans ha (by decide))) (Nat.le_trans ha (by decide)) (by omega_using [hi])

theorem stage_normalize {s : State} {base : Addr} (hs : Scr s base)
    {code : Nat → List Instr} {o : Nat} (ho : Slot o) (ho8 : o % 8 = 0)
    {f : Nat → Nat} (hb : Within (2 ^ 118) f)
    (heval : ∀ i < 8, ∀ t, Scr t base → Outside base TMP 128 s.mem t.mem →
      WP isa (.block (code i)) t fun u =>
        pair (u.gpr .x4) (u.gpr .x5) = f i ∧ u.mem = t.mem ∧ Keeps clob t u) :
    WP isa (.block ((List.range 8).flatMap (fun i => code i ++ Impl.Curve448.AArch64.storeCoeff i) ++
      Impl.Curve448.AArch64.normalize o)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ fe t.mem base o % Spec.X448.P = valN f 8 % Spec.X448.P := by
  rw [WP.block_append_iff]
  refine WP.mono (stage_ok hs heval) fun u ⟨uf, um, uk⟩ => ?_
  refine WP.mono (normalize_ok (hs.of_keeps uk (by decide)) ho ho8 uf hb) fun t ⟨tf, tm, tk⟩ => ?_
  refine ⟨⟨uk.trans (tk.mono (by decide)), (FieldMem.work um (by decide) (by decide)).trans tm⟩, ?_, ?_⟩
  · intro i hi; rw [tf i hi]; exact twice_weak hb i hi
  · rw [show fe t.mem base o = valN (folded (folded f)) 8 from valN_congr tf, twice_mod]

theorem small_carry {f : Nat → Nat} {n : Nat} (h : ∀ i < n, f i < radix * 6) : carry f n < 7 := by
  induction n with
  | zero => simp only [carry]; decide
  | succ n ih =>
    have hi := ih (fun i hi => h i (by omega_using [hi]))
    have hn := h n (by omega_using [])
    simp only [carry, radix] at *
    omega_using [hi, hn]

theorem pointFinish_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) {f : Nat → Nat}
    (hf : ∀ i < 8, coeff s.mem base TMP i = f i) (hb : Within (radix * 6) f) :
    WP isa (.block (Impl.Curve448.AArch64.pointFinish o)) s fun t =>
      (∀ i < 8, limbs t.mem base o i = folded f i) ∧ FieldMem base o s.mem t.mem ∧ Keeps clob s t := by
  have cap : ∀ i < 8, f i < 2 ^ 63 + radix := by
    intro i hi; exact Nat.lt_trans (hb i hi) (by decide)
  have out : Within weakBound (folded f) := by
    intro i _
    have hd := digit_lt f i
    have hc := small_carry hb
    simp only [folded, weakBound]
    split <;> omega_arith
  rw [Impl.Curve448.AArch64.pointFinish, List.append_assoc, WP.block_append_iff]
  refine WP.mono (tailPass_ok hs (o := TMP) (by decide) (by decide) (Or.inl rfl) false
    (fun _ => rfl) hf cap) fun u ⟨uf, uc, um, uk⟩ => ?_
  simp only [encoded, Bool.false_eq_true, ite_false] at uf
  rw [WP.block_append_iff]
  refine WP.mono (fold_ok (hs.of_keeps uk (by decide)) uf uc
    (Nat.lt_trans (small_carry hb) (by decide))) fun v ⟨vf, vm, vk⟩ => ?_
  refine WP.mono (collect_ok ((hs.of_keeps uk (by decide)).of_keeps vk (by decide)) ho ho8 vf out)
    fun t ⟨tf, tm, tk⟩ => ?_
  exact ⟨tf, (FieldMem.work um (by decide) (by decide)).trans
    ((FieldMem.work vm (by decide) (by decide)).trans (.output tm)),
    (uk.mono (by decide)).trans ((vk.mono (by decide)).trans (tk.mono (by decide)))⟩
theorem stage_point {s : State} {base : Addr} (hs : Scr s base)
    {code : Nat → List Instr} {o : Nat} (ho : Slot o) (ho8 : o % 8 = 0)
    {f : Nat → Nat} (hb : Within (radix * 6) f)
    (heval : ∀ i < 8, ∀ t, Scr t base → Outside base TMP 128 s.mem t.mem →
      WP isa (.block (code i)) t fun u =>
        pair (u.gpr .x4) (u.gpr .x5) = f i ∧ u.mem = t.mem ∧ Keeps clob t u) :
    WP isa (.block ((List.range 8).flatMap (fun i => code i ++ Impl.Curve448.AArch64.storeCoeff i) ++
      Impl.Curve448.AArch64.pointFinish o)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ fe t.mem base o % Spec.X448.P = valN f 8 % Spec.X448.P := by
  rw [WP.block_append_iff]
  refine WP.mono (stage_ok hs heval) fun u ⟨uf, um, uk⟩ => ?_
  refine WP.mono (pointFinish_ok (hs.of_keeps uk (by decide)) ho ho8 uf hb) fun t ⟨tf, tm, tk⟩ => ?_
  refine ⟨⟨uk.trans tk, (FieldMem.work um (by decide) (by decide)).trans tm⟩, ?_, ?_⟩
  · intro i hi
    rw [tf i hi]
    have hd := digit_lt f i
    have hc := small_carry hb
    simp only [folded, weakBound]
    split <;> omega_arith
  · rw [show fe t.mem base o = valN (folded f) 8 from valN_congr tf, folded_mod]

end VG.Proof.Curve448.AArch64
