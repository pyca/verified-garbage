module

public import VerifiedGarbage.Impl.Curve448.AArch64
public import VerifiedGarbage.Proof.X448.Wide.Column
import VerifiedGarbage.Proof.X448.Wide.Fold
import VerifiedGarbage.Proof.X448.Wide.Pass
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.X448.Wide.Representation
public import VerifiedGarbage.Proof.X448.AArch64.Mem
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.X448.Wide.Memory
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! ### `Curve448.AArch64.Collect`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ld st TMP ACC)
open VG.Proof.X448.AArch64

theorem coeff_low {m : Mem} {base : Addr} {i v : Nat}
    (h : coeff m base TMP i = v) (hv : v < 2 ^ 64) :
    (word m base (TMP + 16 * i)).toNat = v := by
  have low := (word m base (TMP + 16 * i)).isLt
  simp only [coeff, pair] at h
  omega_using [h, hv]

theorem collectStep_ok {s : State} {base : Addr} (hs : Scr s base) {o i : Nat}
    (ho : o + 128 ≤ ACC) (ho8 : o % 8 = 0) (hi : i < 8) :
    WP isa (.block [ld .x4 (TMP + 16 * i), st .x4 (o + 8 * i)]) s fun t =>
      t.mem = s.mem.writeW (off base (o + 8 * i)) (word s.mem base (TMP + 16 * i)) ∧
      Keeps [.x4] s t := by
  have l := hs.read (d := TMP + 16 * i) (n := 8) (by simp only [TMP]; omega_using [hi])
  have w := hs.write (d := o + 8 * i) (n := 8) (by simp only [ACC] at ho; omega_using [ho, hi])
  have ae : (TMP + 16 * i) % 8 = 0 ∧ TMP + 16 * i < 32768 := by simp only [TMP]; omega_using [hi]
  have oe : (o + 8 * i) % 8 = 0 ∧ o + 8 * i < 32768 := by simp only [ACC] at ho; omega_using [ho, ho8, hi]
  apply WP.of_runBlock
  simp only [ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    State.read, State.load, State.store, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.wr_write, BitVec.setWidth_eq, ae, oe, and_self, hs.x3, l, w,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, read8_eq, write8_eq,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, (fun r hr => ?_), rfl, rfl⟩
  exact RegUpd.gpr_write_of_ne _ _ _ (fun h => hr (by subst r; decide))

theorem collect_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (ho : o + 128 ≤ ACC) (ho8 : o % 8 = 0) {f : Nat → Nat}
    (hf : ∀ i < 8, coeff s.mem base TMP i = f i) (hb : Within weakBound f) :
    WP isa (.block (Impl.Curve448.AArch64.collect o)) s fun t =>
      (∀ i < 8, limbs t.mem base o i = f i) ∧
      Outside base o 128 s.mem t.mem ∧ Keeps [.x4] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base o i = f i) ∧
    Outside base o 128 s.mem t.mem ∧ Keeps [.x4] s t
  have step : ∀ n t, n < 8 → inv n t →
      WP isa (.block [ld .x4 (TMP + 16 * n), st .x4 (o + 8 * n)]) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (collectStep_ok (hs.of_keeps tk (by decide)) ho ho8 hn) fun u ⟨um, uk⟩ => ?_
    have out : Outside base (o + 8 * n) 8 t.mem u.mem := by
      rw [um]; exact writeW_outside _ _ _ (by simp only [ACC] at ho; omega_using [ho, hn])
    refine ⟨?_, tm.trans (out.mono (by omega_using []) (by omega_using [hn])), tk.trans uk⟩
    intro i hi
    change (word u.mem base (o + 8 * i)).toNat = _
    rw [um, word_write t.mem base (by simp only [ACC] at ho; omega_using [ho, hn])
      (by simp only [ACC] at ho; omega_using [ho, hn, hi])]
    by_cases h : i = n
    · subst i
      rw [ite_eq_left rfl, tm.word (Or.inr (by simp only [ACC, TMP] at ho ⊢; omega_using [ho]))
        (by simp only [TMP]; omega_using [hn])]
      exact coeff_low (hf n hn) (Nat.lt_trans (hb n hn) (by decide))
    · rw [ite_eq_right h]; exact tf i (by omega_using [hi, h])
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩
end VG.Proof.Curve448.AArch64

end

end

/-! ### `Curve448.AArch64.Memory`, which the modules that import this one used -/

section

@[expose] public section

namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Proof.X448.AArch64

abbrev fe (m : Mem) (base : Addr) (o : Nat) : Nat := VG.Proof.X448.Wide.valN (limbs m base o) 8
abbrev F (m : Mem) (base : Addr) (o : Nat) : Spec.X448.Fe := VG.Proof.X448.toFe (fe m base o)
def Bounded (m : Mem) (base : Addr) (o : Nat) : Prop := Within weakBound (limbs m base o)

theorem field_fe {base : Addr} {o : Nat} {m m' : Mem}
    (h : FieldMem base o m m') {d : Nat}
    (hd : d + 128 ≤ o ∨ o + 128 ≤ d) (hw : d + 128 ≤ Impl.X448.AArch64.ACC) :
    fe m' base d = fe m base d :=
  VG.Proof.X448.Wide.valN_congr (fun i hi => h.limbs hd hw (by omega_using [hi] : i < 16))

end VG.Proof.Curve448.AArch64

end

end

/-! Untrusted: reduce wide coefficients to eight limbs with explicit headroom. -/

@[expose] public section

namespace VG.Proof.Curve448.AArch64

open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ACC TMP)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem normalize_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (ho : o + 128 ≤ ACC) (ho8 : o % 8 = 0) {f : Nat → Nat}
    (hf : ∀ i < 8, coeff s.mem base TMP i = f i) (hb : ∀ i < 8, f i < 2 ^ 118) :
    WP isa (.block (Impl.Curve448.AArch64.normalize o)) s fun t =>
      (∀ i < 8, limbs t.mem base o i = folded (folded f) i) ∧
      FieldMem base o s.mem t.mem ∧ Keeps colRegs s t := by
  have htmp : TMP + 128 ≤ 8192 := by decide
  have hwork : ∀ {m m' : Mem}, Outside base TMP 128 m m' → FieldMem base o m m' :=
    fun h => FieldMem.work h (by decide) (by decide)
  have keep : ∀ {a b : State}, Keeps [.x4] a b → Keeps colRegs a b :=
    fun h => h.mono (by decide)
  rw [Impl.Curve448.AArch64.normalize, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (pass_ok hs htmp (by decide) (Or.inl rfl) false hf hb) fun s₁ ⟨f₁, c₁, m₁, k₁⟩ => ?_
  simp only [encoded, Bool.false_eq_true, ite_false] at f₁
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (fold_ok hs₁ f₁ c₁ (carry_bound hb)) fun s₂ ⟨f₂, m₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (tailPass_ok hs₂ htmp (by decide) (Or.inl rfl) false (fun _ => rfl) f₂ (folded_small hb)) fun s₃ ⟨f₃, c₃, m₃, k₃⟩ => ?_
  simp only [encoded, Bool.false_eq_true, ite_false] at f₃
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (fold_ok hs₃ f₃ c₃ (Nat.lt_trans (carry_small (folded_small hb)) (by decide))) fun s₄ ⟨f₄, m₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  refine WP.mono (collect_ok hs₄ ho ho8 f₄ (twice_weak hb)) fun s₅ ⟨f₅, m₅, k₅⟩ => ?_
  exact ⟨f₅, (hwork m₁).trans ((hwork m₂).trans ((hwork m₃).trans ((hwork m₄).trans (.output m₅)))),
    k₁.trans ((keep k₂).trans (k₃.trans ((keep k₄).trans (keep k₅))))⟩

end VG.Proof.Curve448.AArch64
