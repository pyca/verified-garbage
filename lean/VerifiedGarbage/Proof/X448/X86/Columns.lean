module

import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.X448.X86.Field
public import VerifiedGarbage.Proof.X448.X86.Args
import VerifiedGarbage.Proof.X448.X86.RowPass
import VerifiedGarbage.Proof.X448.X86.Carry
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `X448.X86.Normalize`, which this module and modules that import it used -/

section

/-!
# X448 on x86 (32-bit): modular reduction

The coefficients at `TMP` are carried, their carry folded with
`2^448 = 2^224 + 1`, twice (`norm4_ok`), and carried once more into the
element at `ebp` (`outPass_ok`), which the field functions point at their
result, the offset of their second argument (`normalize_ok`).
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

/-- The bytes from `ACC` that the field functions' arithmetic writes: the
product and the coefficients at `TMP`, not the registers they save after them. -/
abbrev WORK : Nat := TMP + 112 - ACC

/-- The two carries and folds, in place at `TMP`. -/
theorem norm4_ok {s : State} {base : Addr} (hs : Scr s base) {f : Nat → Nat}
    (hf : ∀ i < 28, limbs s.mem base TMP i = f i) (hb : ∀ i < 28, f i ≤ 2 ^ 32 - radix) :
    WP isa (.block (pass TMP TMP ++ fold ++ pass TMP TMP ++ fold)) s fun t =>
      (∀ i < 28, limbs t.mem base TMP i = folded (folded f) i) ∧
      Outside base TMP 112 s.mem t.mem ∧ Keeps [.eax, .ebx, .edx] s t := by
  have htmp : TMP + 112 ≤ 4096 := by decide
  have keep : ∀ {a b : State}, Keeps [.eax] a b → Keeps [.eax, .ebx, .edx] a b :=
    fun h => h.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; decide)
  rw [show pass TMP TMP ++ fold ++ pass TMP TMP ++ fold =
    pass TMP TMP ++ (fold ++ (pass TMP TMP ++ fold)) by simp only [List.append_assoc],
    WP.block_append_iff]
  refine WP.mono (pass_ok hs htmp htmp (Or.inl rfl) hf hb) fun s₁ ⟨f₁, c₁, m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (fold_ok hs₁ f₁ c₁ (carry_bound hb)) fun s₂ ⟨f₂, m₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pass_ok hs₂ htmp htmp (Or.inl rfl) f₂ (folded_bound hb)) fun s₃ ⟨f₃, c₃, m₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  refine WP.mono (fold_ok hs₃ f₃ c₃ (carry_bound (folded_bound hb))) fun s₄ ⟨f₄, m₄, k₄⟩ => ?_
  exact ⟨f₄, m₁.trans (m₂.trans (m₃.trans m₄)), k₁.trans ((keep k₂).trans (k₃.trans (keep k₄)))⟩

/-- The last carry pass, from `TMP` into the element at `o`, which `ebp` points at. -/
theorem outPass_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : o + 112 ≤ ACC)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 o) {g : Nat → Nat}
    (hg : ∀ i < 28, limbs s.mem base TMP i = g i) (hb : ∀ i < 28, g i ≤ 2 ^ 32 - radix) :
    WP isa (.block outPass) s fun t =>
      (∀ i < 28, limbs t.mem base o i = digit g i) ∧
      Outside base o 112 s.mem t.mem ∧ Keeps [.eax, .ebx, .edx] s t := by
  have ho' : o + 112 ≤ 3584 := ho
  unfold outPass
  rw [WP.block_append_iff]
  refine WP.mono (zeroCarry_ok s) fun t ⟨tc, tm, tk⟩ => ?_
  have ts := hs.of_keeps tk (by decide)
  have tp : t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 o := by
    rw [tk.1 _ (by decide), tk.1 _ (by decide)]; exact hp
  refine WP.mono (carryPass_ok (s0 := t) (base := base) (o := o) (d := 0) (c := g) (by decide)
    (by omega_using [ho']) (fun k hk => ?_) (fun k hk => ts.write (by omega_using [ho', hk])) (by rw [tc]; rfl) hb ?_)
    fun u hu => ⟨hu.outs, by rw [← tm]; exact hu.mem, tk.trans hu.regs⟩
  · change (t.gpr .ebp + BitVec.ofNat 32 (0 + 4 * k)).setWidth 64 = _
    rw [tp, Offset.add_add, Nat.zero_add]
    exact ts.ea (by omega_using [ho', hk])
  · intro k hk v hv
    refine load_ok (ts.of_keeps hv.regs (by decide)) (by simp only [TMP]; omega_using [hk]) fun w hw =>
      WP.block_nil ⟨?_, hw.rest (by decide), hw.mem⟩
    rw [hw.gpr]
    change limbs v.mem base TMP k = g k
    rw [hv.mem.limbs (Or.inr (by simp only [TMP]; omega_using [ho', hk])) (by decide) hk, tm, hg k hk]

/-- The coefficients at `TMP` normalized into the element at `o`, the second
argument of a field function. -/
theorem normalize_ok {s : State} {base : Addr} (hs : Scr s base) {n : Nat} (ha : ArgArea s base n)
    (hn : 1 < n) {o : Nat} (ho : o + 112 ≤ ACC) (harg : arg s 1 = BitVec.ofNat 32 o) {f : Nat → Nat}
    (hf : ∀ i < 28, limbs s.mem base TMP i = f i) (hb : ∀ i < 28, f i ≤ 2 ^ 32 - radix) :
    WP isa (.block normalize) s fun t =>
      (∀ i < 28, limbs t.mem base o i = normalized f i) ∧
      FieldMem base o s.mem t.mem WORK ∧ Keeps [.eax, .ebx, .edx, .ebp] s t := by
  have hwork : ∀ {m m' : Mem}, Outside base TMP 112 m m' → FieldMem base o m m' WORK :=
    fun h => FieldMem.work h (by decide) (by decide)
  unfold normalize
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (norm4_ok hs hf hb) fun t ⟨tf, tm, tk⟩ => ?_
  have ts := hs.of_keeps tk (by decide)
  obtain ⟨ta, targ⟩ := ha.keep (tk.1 _ (by decide)) tk.2.1 tk.2.2 (tm.mono (by decide) (by decide))
  unfold argPtr
  refine ta.load hn fun u hu => ?_
  refine wp_alu (Or.inl rfl) rfl fun v hv _ => ?_
  have uv : Keeps [.ebp] t v := (hu.rest (by decide)).trans (hv.rest (by decide))
  have vs := ts.of_keeps uv (by decide)
  have vp : v.gpr .ebp = v.gpr .edi + BitVec.ofNat 32 o := by
    rw [hv.gpr]
    change u.gpr .ebp + u.gpr .edi = _
    rw [hu.gpr, targ 1 hn, harg, hv.other .edi (by decide), hu.other .edi (by decide), BitVec.add_comm]
  have vm : v.mem = t.mem := hv.mem.trans hu.mem
  refine WP.mono (outPass_ok vs ho vp (fun i hi => by rw [vm]; exact tf i hi)
    (folded_bound (folded_bound hb))) fun w ⟨wf, wm, wk⟩ => ⟨wf, ?_, ?_⟩
  · exact (hwork tm).trans (by rw [← vm]; exact FieldMem.output wm)
  · exact (tk.mono (by decide)).trans ((uv.mono (by decide)).trans (wk.mono (by decide)))

end VG.Proof.X448.X86

end

end

/-! ### `X448.X86.FnCtx`, which this module and modules that import it used -/

section

/-!
# X448 on x86 (32-bit): the field functions' context

What the field functions (`vg_gf448_r16_*`) know once `edi` holds the
working space (`FnCtx`): their arguments (`ArgArea`) and the offsets of the
result and the first operand, which fit below their own working space.
`argPtr_ok` points a register at an element from its offset.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

/-- What the field functions know on entry, after `edi = ws`: the working
space, the arguments, and the offsets `o`, `a` (and `b`) that fit below the
functions' own working space. -/
structure FnCtx (s : State) (base : Addr) (n : Nat) (o a : Nat) : Prop where
  scr : Scr s base
  args : ArgArea s base n
  n3 : 3 ≤ n
  argO : arg s 1 = BitVec.ofNat 32 o
  argA : arg s 2 = BitVec.ofNat 32 a
  slotO : Slot o
  slotA : Slot a

theorem FnCtx.keep {s t : State} {base : Addr} {n o a : Nat} (h : FnCtx s base n o a) {rs : List Reg}
    (hk : Keeps rs s t) (hr : .esp ∉ rs) (he : .edi ∉ rs) (hm : Outside base 0 8192 s.mem t.mem) :
    FnCtx t base n o a := by
  obtain ⟨ta, targ⟩ := h.args.keep (hk.1 _ hr) hk.2.1 hk.2.2 hm
  exact ⟨h.scr.of_keeps hk he, ta, h.n3, by rw [targ 1 (by have := h.n3; omega_using [this])]; exact h.argO,
    by rw [targ 2 (by have := h.n3; omega_using [this])]; exact h.argA, h.slotO, h.slotA⟩

/-- `r = ws + ` argument `i`. -/
theorem argPtr_ok {s : State} {base : Addr} {n : Nat} (ha : ArgArea s base n)
    {i : Nat} (hi : i < n) {r : Reg} (hr : r ≠ .edi) {d : Nat} (hd : arg s i = BitVec.ofNat 32 d) :
    WP isa (.block (argPtr r i)) s fun t =>
      t.gpr r = t.gpr .edi + BitVec.ofNat 32 d ∧ t.mem = s.mem ∧ Keeps [r] s t := by
  unfold argPtr
  refine ha.load hi fun u hu => wp_alu (Or.inl rfl) rfl fun v hv _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [hv.gpr, hv.other .edi hr.symm]
    change u.gpr r + u.gpr .edi = _
    rw [hu.gpr, hd, BitVec.add_comm]
  · rw [hv.mem, hu.mem]
  · exact (hu.rest (by simp)).trans (hv.rest (by simp))

end VG.Proof.X448.X86

end

end

/-!
# X448 on x86 (32-bit): pointwise field operations

A pointwise operation fills `TMP` before the carry passes write the output,
permitting input/output aliasing.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem columns_ok {s : State} {base : Addr} (hs : Scr s base) {code : Nat → List Instr}
    {f : Nat → Nat} {rs : List Reg} (hr : .edi ∉ rs) (hb : ∀ i < 28, f i ≤ 2 ^ 32 - radix)
    (step : ∀ i < 28, ∀ t, Scr t base → Outside base TMP 112 s.mem t.mem → Keeps rs s t →
      WP isa (.block (code i)) t fun u =>
        u.mem = t.mem.writeW (off base (TMP + 4 * i)) (BitVec.ofNat 32 (f i)) ∧ Keeps rs t u) :
    WP isa (.block ((List.range 28).flatMap code)) s fun t =>
      (∀ i < 28, limbs t.mem base TMP i = f i) ∧ Outside base TMP 112 s.mem t.mem ∧ Keeps rs s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base TMP i = f i) ∧ Outside base TMP 112 s.mem t.mem ∧ Keeps rs s t
  have st : ∀ n t, n < 28 → inv n t → WP isa (.block (code n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (step n hn t (hs.of_keeps tk hr) tm tk) fun u ⟨um, uk⟩ => ?_
    have out : Outside base (TMP + 4 * n) 4 t.mem u.mem := by
      rw [um]; exact writeW_outside _ _ _ (by simp only [TMP]; omega_using [hn])
    refine ⟨?_, tm.trans (out.mono (by omega_using []) (by omega_using [hn])), tk.trans uk⟩
    intro i hi
    change (word u.mem base (TMP + 4 * i)).toNat = _
    rw [um, word_write t.mem base (by simp only [TMP]; omega_using [hn]) (by simp only [TMP]; omega_using [hn, hi])]
    by_cases h : i = n
    · rw [ite_eq_left h, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (hb n hn) (by decide))]
    · rw [ite_eq_right h]; exact tf i (by omega_using [hi, h])
  exact wp_range_flatMap (M := isa) (N := 28) inv st 28 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

/-- Reading an input during a pointwise operation. -/
theorem input_limb {s t : State} {base : Addr} {a i : Nat} (h : Outside base TMP 112 s.mem t.mem)
    (ha : Slot a) (hi : i < 28) : limbs t.mem base a i = limbs s.mem base a i :=
  h.limbs (Or.inl (Nat.le_trans ha (by decide))) (Nat.le_trans ha (by decide)) hi

/-- Carry propagation after a pointwise operation, into the element at `o`,
with the common frame. -/
theorem columns_normalize {s : State} {base : Addr} {n o a : Nat} (hc : FnCtx s base n o a)
    {code : List Instr} {f : Nat → Nat} (hb : ∀ i < 28, f i ≤ 2 ^ 32 - radix)
    (hcode : WP isa (.block code) s fun t =>
      (∀ i < 28, limbs t.mem base TMP i = f i) ∧ Outside base TMP 112 s.mem t.mem ∧ Keeps clob s t) :
    WP isa (.block (code ++ normalize)) s fun t =>
      (Keeps clob s t ∧ FieldMem base o s.mem t.mem WORK) ∧ Bounded t.mem base o ∧
        fe t.mem base o % Spec.X448.P = valN f 28 % Spec.X448.P := by
  rw [WP.block_append_iff]
  refine WP.mono hcode fun t ⟨tf, tm, tk⟩ => ?_
  have tc := hc.keep tk (by decide) (by decide) (tm.mono (by decide) (by decide))
  refine WP.mono (normalize_ok tc.scr tc.args (by have := tc.n3; omega_using [this]) tc.slotO tc.argO tf hb)
    fun u ⟨uf, um, uk⟩ => ?_
  refine ⟨⟨tk.trans (uk.mono (by decide)), (FieldMem.work tm (by decide) (by decide)).trans um⟩, ?_, ?_⟩
  · intro i hi; rw [uf i hi]; exact digit_lt _ _
  · rw [show fe u.mem base o = valN (normalized f) 28 from valN_congr uf, normalized_mod hb]

end VG.Proof.X448.X86
