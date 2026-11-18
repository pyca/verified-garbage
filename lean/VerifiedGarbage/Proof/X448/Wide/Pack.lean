module

public import VerifiedGarbage.Impl.X448.AArch64.Wide
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.AArch64.Mem
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Impl.X448.AArch64.Tail
public import VerifiedGarbage.Proof.X448.Wide.Pass
public import VerifiedGarbage.Proof.X448.Wide.Column
import VerifiedGarbage.Proof.X448.Wide.Fold
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.X448.Wide.Limbs
public import VerifiedGarbage.Proof.X448.Limbs
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `X448.Wide.Bridge`, which only this module used -/

section

/-! Untrusted: the exact-value bridge between the old and wide limb layouts. -/

@[expose] public section

namespace VG.Proof.X448.Wide

/-- Combine two neighboring 28-bit limbs. -/
def paired (f : Nat → Nat) (i : Nat) : Nat :=
  f (2 * i) + VG.Proof.X448.radix * f (2 * i + 1)

theorem radix_pair : VG.Proof.X448.radix ^ 2 = radix := by decide

theorem paired_val (f : Nat → Nat) (n : Nat) :
    valN (paired f) n = VG.Proof.X448.valN f (2 * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega_using [],
      VG.Proof.X448.valN_succ, VG.Proof.X448.valN_succ, valN_succ, ih, paired,
      Nat.pow_succ, Nat.pow_mul, radix_pair, Nat.mul_add, Nat.add_assoc, Nat.mul_assoc]

theorem paired_bound {f : Nat → Nat} (h : ∀ i < 16, f i < VG.Proof.X448.radix) :
    ∀ i < 8, paired f i < radix := by
  intro i hi
  have h0 := h (2 * i) (by omega_using [hi])
  have h1 := h (2 * i + 1) (by omega_using [hi])
  simp only [paired, VG.Proof.X448.radix, radix] at *
  omega_using [h0, h1]

/-- Split a normalized wide limb back into the existing field-slot layout. -/
def unpacked (f : Nat → Nat) (i : Nat) : Nat :=
  if i % 2 = 0 then f (i / 2) % VG.Proof.X448.radix else f (i / 2) / VG.Proof.X448.radix

theorem paired_unpacked (f : Nat → Nat) (i : Nat) : paired (unpacked f) i = f i := by
  simp only [paired, unpacked, show (2 * i) % 2 = 0 by omega_using [],
    show (2 * i + 1) % 2 = 1 by omega_using [], show (2 * i) / 2 = i by omega_using [],
    show (2 * i + 1) / 2 = i by omega_using [], ite_true, ite_false, Nat.one_ne_zero]
  exact Nat.mod_add_div _ _

theorem unpacked_val (f : Nat → Nat) :
    VG.Proof.X448.valN (unpacked f) 16 = valN f 8 := by
  rw [← paired_val (unpacked f) 8]
  exact valN_congr (fun i _ => paired_unpacked f i)

theorem unpacked_bound {f : Nat → Nat} (h : ∀ i < 8, f i < radix) :
    ∀ i < 16, unpacked f i < VG.Proof.X448.radix := by
  intro i hi
  have hf := h (i / 2) (by omega_using [hi])
  simp only [unpacked]
  split
  · exact Nat.mod_lt _ (by decide)
  · simp only [radix] at hf
    simp only [VG.Proof.X448.radix]
    omega_using [hf]

end VG.Proof.X448.Wide

end

end

/-! ### `X448.Wide.TailNormalize`, which the modules that import this one used -/

section

/-! ### `X448.Wide.Encoded`, which the modules that import this one used -/

section

/-! Untrusted: interpreting the normalized wide output in the original slots. -/

@[expose] public section

namespace VG.Proof.X448.Wide

open VG VG.AArch64 VG.Proof.X448.AArch64

theorem decode_encoded (lo hi : BitVec 64) {v : Nat} (h : pair lo hi = encoded v true) :
    lo.toNat = v % VG.Proof.X448.radix ∧ hi.toNat = v / VG.Proof.X448.radix := by
  have hl := lo.isLt
  have hm := Nat.mod_lt v (show 0 < VG.Proof.X448.radix by decide)
  simp only [pair, encoded, ite_true, VG.Proof.X448.radix] at h hm ⊢
  omega_using [h]

theorem encoded_limbs {m : Mem} {base : Addr} {o : Nat} {f : Nat → Nat}
    (hf : ∀ i < 8, coeff m base o i = encoded (f i) true) :
    ∀ i < 16, limbs m base o i = unpacked f i := by
  intro i hi
  have hq : i / 2 < 8 := by omega_using [hi]
  have dec := decode_encoded _ _ (hf (i / 2) hq)
  have e0 : o + 16 * (i / 2) = o + 8 * (2 * (i / 2)) := by omega_using []
  simp only [e0] at dec
  change limbs m base o (2 * (i / 2)) = _ ∧ limbs m base o (2 * (i / 2) + 1) = _ at dec
  simp only [unpacked]
  split
  · rename_i h
    rw [show i = 2 * (i / 2) from by omega_using [h]]
    simpa only [show (2 * (i / 2)) / 2 = i / 2 by omega_using []] using dec.1
  · rename_i h
    rw [show i = 2 * (i / 2) + 1 from by omega_using [h]]
    simpa only [show (2 * (i / 2) + 1) / 2 = i / 2 by omega_using []] using dec.2

end VG.Proof.X448.Wide

end

end

/-! Untrusted: normalize wide coefficients and restore the field-slot interface. -/

@[expose] public section

namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ACC TMP)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem tailNormalize_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (ho : o + 128 ≤ ACC) (ho8 : o % 8 = 0) {f : Nat → Nat}
    (hf : ∀ i < 8, coeff s.mem base TMP i = f i) (hb : ∀ i < 8, f i < 2 ^ 118) :
    WP isa (.block (Impl.X448.AArch64.Tail.normalize o)) s fun t =>
      (∀ i < 8, coeff t.mem base o i = encoded (normalized f i) true) ∧
      FieldMem base o s.mem t.mem ∧ Keeps colRegs s t := by
  have htmp : TMP + 128 ≤ 8192 := by decide
  have hwork : ∀ {m m' : Mem}, Outside base TMP 128 m m' → FieldMem base o m m' :=
    fun h => FieldMem.work h (by decide) (by decide)
  have keep : ∀ {a b : State}, Keeps [.x4] a b → Keeps colRegs a b :=
    fun h => h.mono (by decide)
  rw [Impl.X448.AArch64.Tail.normalize, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
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
  refine WP.mono (tailPass_ok hs₄ (Nat.le_trans ho (by decide)) ho8
    (Or.inr (Or.inl (Nat.le_trans ho (by decide)))) true (by intro h; cases h) f₄
    (folded_small (folded_bound hb))) fun s₅ ⟨f₅, _, m₅, k₅⟩ => ?_
  exact ⟨f₅, (hwork m₁).trans ((hwork m₂).trans ((hwork m₃).trans ((hwork m₄).trans (.output m₅)))),
    k₁.trans ((keep k₂).trans (k₃.trans ((keep k₄).trans k₅)))⟩

end VG.Proof.X448.Wide

end

end

/-! Untrusted: staging normalized 28-bit field slots for the wide kernel. -/

@[expose] public section

namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem pack_word (lo hi : BitVec 64) (hl : lo.toNat < VG.Proof.X448.radix)
    (hh : hi.toNat < VG.Proof.X448.radix) :
    (lo + (hi <<< 28)).toNat = lo.toNat + VG.Proof.X448.radix * hi.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  simp only [VG.Proof.X448.radix] at hl hh ⊢
  have hb : hi.toNat * 2 ^ 28 < 2 ^ 64 := by omega_using [hh]
  rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (by omega_using [hl, hh])]
  omega_using []

theorem packStep_ok {s : State} {base : Addr} (hs : Scr s base) {o a i : Nat}
    (ho : o + 64 ≤ 8192) (ha : a + 128 ≤ 8192)
    (ho8 : o % 8 = 0) (ha8 : a % 8 = 0) (hi : i < 8)
    (hb : Bounded s.mem base a) :
    WP isa (.block (packStep o a i)) s fun t =>
      t.mem = s.mem.writeW (off base (o + 8 * i))
        (BitVec.ofNat 64 (paired (limbs s.mem base a) i)) ∧ Keeps [.x4, .x5] s t := by
  have al := hs.read (d := a + 16 * i) (n := 8) (by omega_using [ha, hi])
  have bl := hs.read (d := a + 16 * i + 8) (n := 8) (by omega_using [ha, hi])
  have ow := hs.write (d := o + 8 * i) (n := 8) (by omega_using [ho, hi])
  have ae : (a + 16 * i) % 8 = 0 ∧ a + 16 * i < 32768 := ⟨by omega_using [ha8], by omega_using [ha, hi]⟩
  have be : (a + 16 * i + 8) % 8 = 0 ∧ a + 16 * i + 8 < 32768 := ⟨by omega_using [ha8], by omega_using [ha, hi]⟩
  have oe : (o + 8 * i) % 8 = 0 ∧ o + 8 * i < 32768 := ⟨by omega_using [ho8], by omega_using [ho, hi]⟩
  have e0 : a + 8 * (2 * i) = a + 16 * i := by omega_using []
  have e1 : a + 8 * (2 * i + 1) = a + 16 * i + 8 := by omega_using []
  apply WP.of_runBlock
  simp only [packStep, ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
    Size.bytes, Size.bits, ae, be, oe, and_self, State.read, State.load, State.store,
    hs.x3, al, bl, ow, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, Nat.reduceLT,
    Option.map_some, Option.bind_some, read8_eq, write8_eq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, (fun r hr => ?_), rfl, rfl⟩
  · apply congrArg (s.mem.writeW (off base (o + 8 * i)))
    apply BitVec.eq_of_toNat_eq
    have h0 : (word s.mem base (a + 16 * i)).toNat < VG.Proof.X448.radix := by
      simpa only [limbs, e0] using hb (2 * i) (by omega_using [hi])
    have h1 : (word s.mem base (a + 16 * i + 8)).toNat < VG.Proof.X448.radix := by
      simpa only [limbs, e1] using hb (2 * i + 1) (by omega_using [hi])
    rw [pack_word _ _ h0 h1, BitVec.toNat_ofNat]
    have cap := paired_bound hb i hi
    rw [Nat.mod_eq_of_lt (Nat.lt_trans cap (show radix < 2 ^ 64 by decide))]
    simp only [paired, limbs, e0, e1]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]

theorem pack_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : o + 64 ≤ 8192) (ha : a + 128 ≤ 8192)
    (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (hsep : a + 128 ≤ o ∨ o + 64 ≤ a) (hb : Bounded s.mem base a) :
    WP isa (.block (pack o a)) s fun t =>
      (∀ i < 8, limbs t.mem base o i = paired (limbs s.mem base a) i) ∧
      Outside base o 64 s.mem t.mem ∧ Keeps [.x4, .x5] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base o i = paired (limbs s.mem base a) i) ∧
    Outside base o 64 s.mem t.mem ∧ Keeps [.x4, .x5] s t
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (packStep o a n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    have av : ∀ i < 16, limbs t.mem base a i = limbs s.mem base a i :=
      fun i hi => tm.limbs (by omega_using [hsep]) ha hi
    have tb : Bounded t.mem base a := by
      intro i hi
      rw [av i hi]
      exact hb i hi
    refine WP.mono (packStep_ok (hs.of_keeps tk (by decide)) ho ha ho8 ha8 hn tb)
      fun u ⟨um, uk⟩ => ?_
    have out : Outside base (o + 8 * n) 8 t.mem u.mem := by
      rw [um]
      exact writeW_outside _ _ _ (by omega_using [ho, hn])
    refine ⟨?_, tm.trans (out.mono (by omega_using []) (by omega_using [hn])), tk.trans uk⟩
    intro i hi
    change (word u.mem base (o + 8 * i)).toNat = _
    rw [um, word_write _ base (by omega_using [ho, hn]) (by omega_using [ho, hn, hi])]
    by_cases h : i = n
    · subst i
      rw [ite_eq_left rfl, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.lt_trans (paired_bound tb n hn) (show radix < 2 ^ 64 by decide))]
      simp only [paired]
      rw [av (2 * n) (by omega_using [hn]), av (2 * n + 1) (by omega_using [hn])]
    · rw [ite_eq_right h]
      exact tf i (by omega_using [hi, h])
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.Wide
