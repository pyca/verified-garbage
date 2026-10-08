import VerifiedGarbage.Proof.X448.X86.RowPass
import VerifiedGarbage.Proof.X448.X86.Args

/-!
# X448 on x86 (32-bit): modular reduction

The coefficients at `TMP` are carried, their carry folded with
`2^448 = 2^224 + 1`, twice (`norm4_ok`), and carried once more into the
element at `ebp` (`outPass_ok`), which the field functions point at their
result, the offset of their second argument (`normalize_ok`).
-/

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
    (by omega) (fun k hk => ?_) (fun k hk => ts.write (by omega)) (by rw [tc]; rfl) hb ?_)
    fun u hu => ⟨hu.outs, by rw [← tm]; exact hu.mem, tk.trans hu.regs⟩
  · change (t.gpr .ebp + BitVec.ofNat 32 (0 + 4 * k)).setWidth 64 = _
    rw [tp, Offset.add_add, Nat.zero_add]
    exact ts.ea (by omega)
  · intro k hk v hv
    refine load_ok (ts.of_keeps hv.regs (by decide)) (by simp only [TMP]; omega) fun w hw =>
      WP.block_nil ⟨?_, hw.rest (by decide), hw.mem⟩
    rw [hw.gpr]
    change limbs v.mem base TMP k = g k
    rw [hv.mem.limbs (Or.inr (by simp only [TMP]; omega)) (by decide) hk, tm, hg k hk]

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
