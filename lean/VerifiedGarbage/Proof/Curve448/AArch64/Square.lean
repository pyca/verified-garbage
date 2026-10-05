import VerifiedGarbage.Proof.X448.Wide.TailMul
import VerifiedGarbage.Impl.X448.AArch64.Symmetric
import VerifiedGarbage.Impl.Curve448.AArch64
import VerifiedGarbage.Proof.Framework.Range

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Bounds`. -/
section

namespace VG.Proof.Curve448.AArch64
open VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation

theorem rows_bound {f g : Nat → Nat} (hf : Within weakBound f)
    (hg : Within weakBound g) {n : Nat} (hn : n ≤ 8) (k : Nat) :
    VG.Proof.X448.Wide.rows f g n k ≤ n * (weakBound - 1) ^ 2 := by
  induction n with
  | zero => simp only [VG.Proof.X448.Wide.rows, Nat.zero_mul, Nat.le_refl]
  | succ n ih =>
    rw [VG.Proof.X448.Wide.rows, VG.Proof.X448.Wide.addRow_at]
    have hp := ih (by omega)
    split
    · rename_i hk
      have h1 := hf n (by omega)
      have h2 := hg (k - n) (by omega)
      have hprod : f n * g (k - n) ≤ (weakBound - 1) ^ 2 := by
        rw [Nat.pow_two]
        exact Nat.mul_le_mul (by omega) (by omega)
      rw [Nat.succ_mul]; omega
    · rw [Nat.succ_mul]; omega

theorem sqrSum_bound {f : Nat → Nat} (hf : Within weakBound f)
    {n k : Nat} (hn : n ≤ 8) (hk : k < 16) : sqrSum f k n < 2 ^ 116 := by
  have h := sqrSum_le hn f k
  rw [sqrSum_eq f hk] at h
  exact Nat.lt_of_le_of_lt (Nat.le_trans h (VG.Proof.Curve448.AArch64.rows_bound hf hf (by decide) k)) (by decide)
end VG.Proof.Curve448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.AccumSquareBody`. -/
section

/-! Untrusted: accumulate a square diagonal into an existing coefficient. -/
namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64.Wide VG.Impl.X448.AArch64.Cached VG.Proof.X448.AArch64
theorem accumSquareBody_ok {s : State} {f : Nat → Nat} {k : Nat} (hk : k < 16)
    (fc : ∀ i < 8, (s.gpr (cacheReg i)).toNat = f i)
    (fb : ∀ i < 8, f i < weakBound) {c : Nat} (hc : c < 2 ^ 118)
    (hz : VG.Proof.X448.Wide.pair (s.gpr .x4) (s.gpr .x5) = c) :
    WP isa (.block (Impl.X448.AArch64.Symmetric.body k)) s fun t =>
      VG.Proof.X448.Wide.pair (t.gpr .x4) (t.gpr .x5) = c + VG.Proof.X448.Wide.rows f f 8 k ∧ t.mem = s.mem ∧ Keeps termRegs s t := by
  let inv := fun n (t : State) =>
    VG.Proof.X448.Wide.pair (t.gpr .x4) (t.gpr .x5) = c + sqrSum f k n ∧ t.mem = s.mem ∧ Keeps termRegs s t
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (if n ≤ k ∧ k < n + 8 ∧ n ≤ k - n then
      if n = k - n then termFrom (cacheReg n) (cacheReg (k - n))
      else termFromDouble (cacheReg n) (cacheReg (k - n)) else [])) t (inv (n + 1)) := by
    intro n t hn ⟨tv, tm, tk⟩
    by_cases h : n ≤ k ∧ k < n + 8 ∧ n ≤ k - n
    · rw [ite_eq_left h]
      have hj : k - n < 8 := by omega
      have av : (t.gpr (cacheReg n)).toNat = f n := by rw [tk.1 _ (cacheReg_kept hn), fc n hn]
      have bv : (t.gpr (cacheReg (k - n))).toNat = f (k - n) := by
        rw [tk.1 _ (cacheReg_kept hj), fc (k - n) hj]
      have next := VG.Proof.Curve448.AArch64.sqrSum_bound fb (n := n + 1) (by omega) hk
      by_cases diag : n = k - n
      · rw [ite_eq_left diag]
        have sum : (t.gpr (cacheReg n)).toNat * (t.gpr (cacheReg (k - n))).toNat +
            VG.Proof.X448.Wide.pair (t.gpr .x4) (t.gpr .x5) < 2 ^ 128 := by
          rw [av, bv, tv]
          simp only [sqrSum, ite_eq_left h, ite_eq_left diag] at next
          omega
        refine WP.mono (termFrom_ok t _ _ (cacheReg_ne10 hn) (cacheReg_ne10 hj) sum) fun u ⟨uv, um, uk⟩ => ?_
        refine ⟨?_, um.trans tm, tk.trans uk⟩
        rw [uv, av, bv, tv, sqrSum, ite_eq_left h, ite_eq_left diag]
        omega
      · rw [ite_eq_right diag]
        have sum : 2 * ((t.gpr (cacheReg n)).toNat * (t.gpr (cacheReg (k - n))).toNat) +
            VG.Proof.X448.Wide.pair (t.gpr .x4) (t.gpr .x5) < 2 ^ 128 := by
          rw [av, bv, tv]
          simp only [sqrSum, ite_eq_left h, ite_eq_right diag] at next
          omega
        refine WP.mono (termFromDouble_ok t _ _ (cacheReg_ne10 hj) (cacheReg_ne11 hj)
          (by rw [av]; exact Nat.lt_trans (fb n hn) (by decide : weakBound < 2 ^ 63)) sum) fun u ⟨uv, um, uk⟩ => ?_
        refine ⟨?_, um.trans tm, tk.trans uk⟩
        rw [uv, av, bv, tv, sqrSum, ite_eq_left h, ite_eq_right diag]
        omega
    · rw [ite_eq_right h]
      apply WP.block_nil
      exact ⟨by rw [sqrSum, ite_eq_right h, Nat.add_zero]; exact tv, tm, tk⟩
  rw [Impl.X448.AArch64.Symmetric.body]
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨by simpa only [sqrSum, Nat.add_zero] using hz, rfl, Keeps.refl _ _⟩) fun t ⟨tv, tm, tk⟩ => ?_
  rw [sqrSum_eq f hk] at tv
  exact ⟨tv, tm, tk⟩

end VG.Proof.Curve448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Memory`. -/
section

namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Proof.X448.AArch64

abbrev fe (m : Mem) (base : Addr) (o : Nat) : Nat := VG.Proof.X448.Wide.valN (limbs m base o) 8
abbrev F (m : Mem) (base : Addr) (o : Nat) : Spec.X448.Fe := VG.Proof.X448.toFe (VG.Proof.Curve448.AArch64.fe m base o)
def Bounded (m : Mem) (base : Addr) (o : Nat) : Prop := Within weakBound (limbs m base o)

theorem field_fe {base : Addr} {o : Nat} {m m' : Mem}
    (h : FieldMem base o m m') {d : Nat}
    (hd : d + 128 ≤ o ∨ o + 128 ≤ d) (hw : d + 128 ≤ Impl.X448.AArch64.ACC) :
    VG.Proof.Curve448.AArch64.fe m' base d = VG.Proof.Curve448.AArch64.fe m base d :=
  VG.Proof.X448.Wide.valN_congr (fun i hi => h.limbs hd hw (by omega : i < 16))

theorem outside_fe {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base o n m m') {d : Nat}
    (hd : d + 128 ≤ o ∨ o + n ≤ d) (hw : d + 128 ≤ 8192) :
    VG.Proof.Curve448.AArch64.fe m' base d = VG.Proof.Curve448.AArch64.fe m base d :=
  VG.Proof.X448.Wide.valN_congr (fun i hi => h.limbs hd hw (by omega : i < 16))
end VG.Proof.Curve448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Collect`. -/
section

namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ld st TMP ACC)
open VG.Proof.X448.AArch64

theorem coeff_low {m : Mem} {base : Addr} {i v : Nat}
    (h : coeff m base TMP i = v) (hv : v < 2 ^ 64) :
    (word m base (TMP + 16 * i)).toNat = v := by
  have low := (word m base (TMP + 16 * i)).isLt
  simp only [coeff, VG.Proof.X448.Wide.pair] at h
  omega

theorem collectStep_ok {s : State} {base : Addr} (hs : Scr s base) {o i : Nat}
    (ho : o + 128 ≤ ACC) (ho8 : o % 8 = 0) (hi : i < 8) :
    WP isa (.block [ld .x4 (TMP + 16 * i), st .x4 (o + 8 * i)]) s fun t =>
      t.mem = s.mem.writeW (off base (o + 8 * i)) (word s.mem base (TMP + 16 * i)) ∧
      Keeps [.x4] s t := by
  have l := hs.read (d := TMP + 16 * i) (n := 8) (by simp only [TMP]; omega)
  have w := hs.write (d := o + 8 * i) (n := 8) (by simp only [ACC] at ho; omega)
  have ae : (TMP + 16 * i) % 8 = 0 ∧ TMP + 16 * i < 32768 := by simp only [TMP]; omega
  have oe : (o + 8 * i) % 8 = 0 ∧ o + 8 * i < 32768 := by simp only [ACC] at ho; omega
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
    refine WP.mono (VG.Proof.Curve448.AArch64.collectStep_ok (hs.of_keeps tk (by decide)) ho ho8 hn) fun u ⟨um, uk⟩ => ?_
    have out : Outside base (o + 8 * n) 8 t.mem u.mem := by
      rw [um]; exact writeW_outside _ _ _ (by simp only [ACC] at ho; omega)
    refine ⟨?_, tm.trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    change (word u.mem base (o + 8 * i)).toNat = _
    rw [um, word_write t.mem base (by simp only [ACC] at ho; omega)
      (by simp only [ACC] at ho; omega)]
    by_cases h : i = n
    · subst i
      rw [ite_eq_left rfl, tm.word (Or.inr (by simp only [ACC, TMP] at ho ⊢; omega))
        (by simp only [TMP]; omega)]
      exact VG.Proof.Curve448.AArch64.coeff_low (hf n hn) (Nat.lt_trans (hb n hn) (by decide))
    · rw [ite_eq_right h]; exact tf i (by omega)
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩
end VG.Proof.Curve448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Normalize`. -/
section

/-! Untrusted: reduce wide coefficients to eight limbs with explicit headroom. -/
namespace VG.Proof.Curve448.AArch64

open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ACC TMP)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem normalize_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (ho : o + 128 ≤ ACC) (ho8 : o % 8 = 0) {f : Nat → Nat}
    (hf : ∀ i < 8, coeff s.mem base TMP i = f i) (hb : ∀ i < 8, f i < 2 ^ 118) :
    WP isa (.block (Impl.Curve448.AArch64.normalize o)) s fun t =>
      (∀ i < 8, limbs t.mem base o i = VG.Proof.X448.Wide.folded (VG.Proof.X448.Wide.folded f) i) ∧
      FieldMem base o s.mem t.mem ∧ Keeps VG.Proof.X448.Wide.colRegs s t := by
  have htmp : TMP + 128 ≤ 8192 := by decide
  have hwork : ∀ {m m' : Mem}, Outside base TMP 128 m m' → FieldMem base o m m' :=
    fun h => FieldMem.work h (by decide) (by decide)
  have keep : ∀ {a b : State}, Keeps [.x4] a b → Keeps VG.Proof.X448.Wide.colRegs a b :=
    fun h => h.mono (by decide)
  rw [Impl.Curve448.AArch64.normalize, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (pass_ok hs htmp (by decide) (Or.inl rfl) false hf hb) fun s₁ ⟨f₁, c₁, m₁, k₁⟩ => ?_
  simp only [encoded, Bool.false_eq_true, ite_false] at f₁
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.fold_ok hs₁ f₁ c₁ (VG.Proof.X448.Wide.carry_bound hb)) fun s₂ ⟨f₂, m₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (tailPass_ok hs₂ htmp (by decide) (Or.inl rfl) false (fun _ => rfl) f₂ (folded_small hb)) fun s₃ ⟨f₃, c₃, m₃, k₃⟩ => ?_
  simp only [encoded, Bool.false_eq_true, ite_false] at f₃
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.fold_ok hs₃ f₃ c₃ (Nat.lt_trans (carry_small (folded_small hb)) (by decide))) fun s₄ ⟨f₄, m₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  refine WP.mono (VG.Proof.Curve448.AArch64.collect_ok hs₄ ho ho8 f₄ (twice_weak hb)) fun s₅ ⟨f₅, m₅, k₅⟩ => ?_
  exact ⟨f₅, (hwork m₁).trans ((hwork m₂).trans ((hwork m₃).trans ((hwork m₄).trans (.output m₅)))),
    k₁.trans ((keep k₂).trans (k₃.trans ((keep k₄).trans (keep k₅))))⟩

end VG.Proof.Curve448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Stage`. -/
section

namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ld st TMP ACC)
open VG.Proof.X448.AArch64

/-- Stage all inputs before writing the output, including aliasing cases. -/
theorem stage_ok {s : State} {base : Addr} (hs : Scr s base)
    {code : Nat → List Instr} {f : Nat → Nat}
    (heval : ∀ i < 8, ∀ t, Scr t base → Outside base TMP 128 s.mem t.mem →
      WP isa (.block (code i)) t fun u =>
        VG.Proof.X448.Wide.pair (u.gpr .x4) (u.gpr .x5) = f i ∧ u.mem = t.mem ∧ Keeps VG.Proof.X448.AArch64.clob t u) :
    WP isa (.block ((List.range 8).flatMap (fun i => code i ++ Impl.Curve448.AArch64.storeCoeff i))) s fun t =>
      (∀ i < 8, coeff t.mem base TMP i = f i) ∧
      Outside base TMP 128 s.mem t.mem ∧ Keeps VG.Proof.X448.AArch64.clob s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, coeff t.mem base TMP i = f i) ∧
    Outside base TMP 128 s.mem t.mem ∧ Keeps VG.Proof.X448.AArch64.clob s t
  have step : ∀ n t, n < 8 → inv n t →
      WP isa (.block (code n ++ Impl.Curve448.AArch64.storeCoeff n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    rw [WP.block_append_iff]
    refine WP.mono (heval n hn t (hs.of_keeps tk (by decide)) tm) fun u ⟨uv, um, uk⟩ => ?_
    refine WP.mono (storeAt_ok ((hs.of_keeps tk (by decide)).of_keeps uk (by decide))
      (o := TMP) (k := n) (by simp only [TMP]; omega) (by decide)) fun v ⟨vm, vk⟩ => ?_
    have out : Outside base (TMP + 16 * n) 16 t.mem v.mem := by
      rw [vm, um]; exact putCoeff_outside _ _ _ _ (by simp only [TMP]; omega)
    refine ⟨?_, tm.trans (out.mono (by omega) (by omega)), tk.trans (uk.trans (vk.mono (by decide)))⟩
    intro i hi
    rw [vm, coeff_put _ base _ _ (by simp only [TMP]; omega) (by simp only [TMP]; omega)]
    by_cases h : i = n
    · subst i; rw [ite_eq_left rfl]; exact uv
    · rw [ite_eq_right h, um]; exact tf i (by omega)
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

theorem input_limb {base : Addr} {a : Nat} {m m' : Mem}
    (h : Outside base TMP 128 m m') (ha : VG.Proof.X448.AArch64.Slot a) {i : Nat} (hi : i < 8) :
    limbs m' base a i = limbs m base a i :=
  h.limbs (Or.inl (Nat.le_trans ha (by decide))) (Nat.le_trans ha (by decide)) (by omega)

theorem stage_normalize {s : State} {base : Addr} (hs : Scr s base)
    {code : Nat → List Instr} {o : Nat} (ho : VG.Proof.X448.AArch64.Slot o) (ho8 : o % 8 = 0)
    {f : Nat → Nat} (hb : Within (2 ^ 118) f)
    (heval : ∀ i < 8, ∀ t, Scr t base → Outside base TMP 128 s.mem t.mem →
      WP isa (.block (code i)) t fun u =>
        VG.Proof.X448.Wide.pair (u.gpr .x4) (u.gpr .x5) = f i ∧ u.mem = t.mem ∧ Keeps VG.Proof.X448.AArch64.clob t u) :
    WP isa (.block ((List.range 8).flatMap (fun i => code i ++ Impl.Curve448.AArch64.storeCoeff i) ++
      Impl.Curve448.AArch64.normalize o)) s fun t =>
      VG.Proof.X448.AArch64.Op base o s t ∧ VG.Proof.Curve448.AArch64.Bounded t.mem base o ∧ VG.Proof.Curve448.AArch64.fe t.mem base o % Spec.X448.P = VG.Proof.X448.Wide.valN f 8 % Spec.X448.P := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.stage_ok hs heval) fun u ⟨uf, um, uk⟩ => ?_
  refine WP.mono (VG.Proof.Curve448.AArch64.normalize_ok (hs.of_keeps uk (by decide)) ho ho8 uf hb) fun t ⟨tf, tm, tk⟩ => ?_
  refine ⟨⟨uk.trans (tk.mono (by decide)), (FieldMem.work um (by decide) (by decide)).trans tm⟩, ?_, ?_⟩
  · intro i hi; rw [tf i hi]; exact twice_weak hb i hi
  · rw [show VG.Proof.Curve448.AArch64.fe t.mem base o = VG.Proof.X448.Wide.valN (VG.Proof.X448.Wide.folded (VG.Proof.X448.Wide.folded f)) 8 from VG.Proof.X448.Wide.valN_congr tf, twice_mod]

theorem small_carry {f : Nat → Nat} {n : Nat} (h : ∀ i < n, f i < VG.Proof.X448.Wide.radix * 6) : VG.Proof.X448.Wide.carry f n < 7 := by
  induction n with
  | zero => simp only [VG.Proof.X448.Wide.carry]; decide
  | succ n ih =>
    have hi := ih (fun i hi => h i (by omega))
    have hn := h n (by omega)
    simp only [VG.Proof.X448.Wide.carry, VG.Proof.X448.Wide.radix] at *
    omega

theorem pointFinish_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (ho : VG.Proof.X448.AArch64.Slot o) (ho8 : o % 8 = 0) {f : Nat → Nat}
    (hf : ∀ i < 8, coeff s.mem base TMP i = f i) (hb : Within (VG.Proof.X448.Wide.radix * 6) f) :
    WP isa (.block (Impl.Curve448.AArch64.pointFinish o)) s fun t =>
      (∀ i < 8, limbs t.mem base o i = VG.Proof.X448.Wide.folded f i) ∧ FieldMem base o s.mem t.mem ∧ Keeps VG.Proof.X448.AArch64.clob s t := by
  have cap : ∀ i < 8, f i < 2 ^ 63 + VG.Proof.X448.Wide.radix := by
    intro i hi; exact Nat.lt_trans (hb i hi) (by decide)
  have out : Within weakBound (VG.Proof.X448.Wide.folded f) := by
    intro i _
    have hd := VG.Proof.X448.Wide.digit_lt f i
    have hc := VG.Proof.Curve448.AArch64.small_carry hb
    simp only [VG.Proof.X448.Wide.folded, weakBound]
    split <;> omega
  rw [Impl.Curve448.AArch64.pointFinish, List.append_assoc, WP.block_append_iff]
  refine WP.mono (tailPass_ok hs (o := TMP) (by decide) (by decide) (Or.inl rfl) false
    (fun _ => rfl) hf cap) fun u ⟨uf, uc, um, uk⟩ => ?_
  simp only [encoded, Bool.false_eq_true, ite_false] at uf
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.fold_ok (hs.of_keeps uk (by decide)) uf uc
    (Nat.lt_trans (VG.Proof.Curve448.AArch64.small_carry hb) (by decide))) fun v ⟨vf, vm, vk⟩ => ?_
  refine WP.mono (VG.Proof.Curve448.AArch64.collect_ok ((hs.of_keeps uk (by decide)).of_keeps vk (by decide)) ho ho8 vf out)
    fun t ⟨tf, tm, tk⟩ => ?_
  exact ⟨tf, (FieldMem.work um (by decide) (by decide)).trans
    ((FieldMem.work vm (by decide) (by decide)).trans (.output tm)),
    (uk.mono (by decide)).trans ((vk.mono (by decide)).trans (tk.mono (by decide)))⟩
theorem stage_point {s : State} {base : Addr} (hs : Scr s base)
    {code : Nat → List Instr} {o : Nat} (ho : VG.Proof.X448.AArch64.Slot o) (ho8 : o % 8 = 0)
    {f : Nat → Nat} (hb : Within (VG.Proof.X448.Wide.radix * 6) f)
    (heval : ∀ i < 8, ∀ t, Scr t base → Outside base TMP 128 s.mem t.mem →
      WP isa (.block (code i)) t fun u =>
        VG.Proof.X448.Wide.pair (u.gpr .x4) (u.gpr .x5) = f i ∧ u.mem = t.mem ∧ Keeps VG.Proof.X448.AArch64.clob t u) :
    WP isa (.block ((List.range 8).flatMap (fun i => code i ++ Impl.Curve448.AArch64.storeCoeff i) ++
      Impl.Curve448.AArch64.pointFinish o)) s fun t =>
      VG.Proof.X448.AArch64.Op base o s t ∧ VG.Proof.Curve448.AArch64.Bounded t.mem base o ∧ VG.Proof.Curve448.AArch64.fe t.mem base o % Spec.X448.P = VG.Proof.X448.Wide.valN f 8 % Spec.X448.P := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.stage_ok hs heval) fun u ⟨uf, um, uk⟩ => ?_
  refine WP.mono (VG.Proof.Curve448.AArch64.pointFinish_ok (hs.of_keeps uk (by decide)) ho ho8 uf hb) fun t ⟨tf, tm, tk⟩ => ?_
  refine ⟨⟨uk.trans tk, (FieldMem.work um (by decide) (by decide)).trans tm⟩, ?_, ?_⟩
  · intro i hi
    rw [tf i hi]
    have hd := VG.Proof.X448.Wide.digit_lt f i
    have hc := VG.Proof.Curve448.AArch64.small_carry hb
    simp only [VG.Proof.X448.Wide.folded, weakBound]
    split <;> omega
  · rw [show VG.Proof.Curve448.AArch64.fe t.mem base o = VG.Proof.X448.Wide.valN (VG.Proof.X448.Wide.folded f) 8 from VG.Proof.X448.Wide.valN_congr tf, VG.Proof.X448.Wide.folded_mod]

end VG.Proof.Curve448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.AddEval`. -/
section

/-! Untrusted: pointwise coefficient in registers, without an intermediate store. -/
namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ld st)
open VG.Proof.X448.AArch64
open VG.Impl.Curve448.AArch64

theorem addEval_ok {s : State} {base : Addr} (hs : Scr s base) {a b i : Nat}
    (ha : VG.Proof.X448.AArch64.Slot a) (ha8 : a % 8 = 0) (hb : VG.Proof.X448.AArch64.Slot b) (hb8 : b % 8 = 0) (hi : i < 8)
    (ab : limbs s.mem base a i < weakBound) (bb : limbs s.mem base b i < weakBound) :
    WP isa (.block (Impl.Curve448.AArch64.addEval a b i)) s fun t =>
      VG.Proof.X448.Wide.pair (t.gpr .x4) (t.gpr .x5) = limbs s.mem base a i + limbs s.mem base b i ∧ t.mem = s.mem ∧ Keeps [.x4, .x5] s t := by
  have la := hs.read (d := a + 8 * i) (n := 8) (by change a + 128 ≤ 3584 at ha; omega)
  have lb := hs.read (d := b + 8 * i) (n := 8) (by change b + 128 ≤ 3584 at hb; omega)
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := by
    change a + 128 ≤ 3584 at ha; omega
  have be : (b + 8 * i) % 8 = 0 ∧ b + 8 * i < 32768 := by
    change b + 128 ≤ 3584 at hb; omega
  apply WP.of_runBlock
  simp only [Impl.Curve448.AArch64.addEval, ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    State.read, State.load, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq, ae, be, and_self,
    hs.x3, la, lb, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, read8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · simp only [VG.Proof.X448.Wide.pair, show (BitVec.setWidth 64 (0 : BitVec 16)).toNat = 0 from rfl,
      Nat.mul_zero, Nat.add_zero, BitVec.toNat_add]
    change (limbs s.mem base a i + limbs s.mem base b i) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt (by simp only [weakBound, VG.Proof.X448.Wide.radix] at ab bb; omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

end VG.Proof.Curve448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Column`. -/
section

/-! Untrusted: a diagonal of an eight-by-eight product, accumulated in registers. -/
namespace VG.Proof.Curve448.AArch64

open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ld st ACC)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

/-- Load one pair of operands without changing the coefficient registers. -/
theorem loadTerm_ok {s : State} {base : Addr} (hs : Scr s base) {a b i j : Nat}
    (ha : a + 64 ≤ 8192) (hb : b + 64 ≤ 8192)
    (ha8 : a % 8 = 0) (hb8 : b % 8 = 0) (hi : i < 8) (hj : j < 8) :
    WP isa (.block [ld .x6 (a + 8 * i), ld .x9 (b + 8 * j)]) s fun t =>
      t.gpr .x6 = word s.mem base (a + 8 * i) ∧
      t.gpr .x9 = word s.mem base (b + 8 * j) ∧
      t.mem = s.mem ∧ Keeps [.x6, .x9] s t := by
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := ⟨by omega, by omega⟩
  have be : (b + 8 * j) % 8 = 0 ∧ b + 8 * j < 32768 := ⟨by omega, by omega⟩
  have al := hs.read (d := a + 8 * i) (n := 8) (by omega)
  have bl := hs.read (d := b + 8 * j) (n := 8) (by omega)
  apply WP.of_runBlock
  simp only [ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    ae, be, and_self, State.load, hs.x3, al, bl, ite_true, Option.map_some,
    Option.bind_some, BitVec.setWidth_eq, read8_eq, RegUpd.gpr_write,
    ite_false, reduceCtorEq, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-- Initialize a register coefficient to zero. -/
theorem zero_ok (s : State) :
    WP isa (.block [.movz .x .x4 0 0, .movz .x .x5 0 0]) s fun t =>
      VG.Proof.X448.Wide.pair (t.gpr .x4) (t.gpr .x5) = 0 ∧ t.mem = s.mem ∧ Keeps [.x4, .x5] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits from by decide, ite_true, RegUpd.gpr_write, BitVec.setWidth_eq, ite_false,
    reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-- Write the two coefficient words. -/
theorem store_ok {s : State} {base : Addr} (hs : Scr s base) {k : Nat} (hk : k < 16) :
    WP isa (.block [st .x4 (ACC + 16 * k), st .x5 (ACC + 16 * k + 8)]) s fun t =>
      t.mem = putCoeff s.mem base ACC k (s.gpr .x4) (s.gpr .x5) ∧ Keeps [] s t := by
  have ae : (ACC + 16 * k) % 8 = 0 ∧ ACC + 16 * k < 32768 := by simp only [ACC]; omega
  have be : (ACC + 16 * k + 8) % 8 = 0 ∧ ACC + 16 * k + 8 < 32768 := by simp only [ACC]; omega
  have aw := hs.write (d := ACC + 16 * k) (n := 8) (by simp only [ACC]; omega)
  have bw := hs.write (d := ACC + 16 * k + 8) (n := 8) (by simp only [ACC]; omega)
  apply WP.of_runBlock
  simp only [st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    ae, be, and_self, State.read, State.store, hs.x3, aw, bw, ite_true,
    Option.bind_some, BitVec.setWidth_eq, write8_eq,
    Option.some.injEq, exists_eq_left']
  exact ⟨rfl, (fun _ _ => rfl), rfl, rfl⟩

def colRegs : List Reg := [.x4, .x5, .x6, .x9, .x10, .x11]

theorem columnBody_ok {s : State} {base : Addr} (hs : Scr s base) {a b k : Nat}
    (ha : a + 64 ≤ 8192) (hb : b + 64 ≤ 8192)
    (ha8 : a % 8 = 0) (hb8 : b % 8 = 0)
    (fa : ∀ i < 8, limbs s.mem base a i < weakBound)
    (fb : ∀ i < 8, limbs s.mem base b i < weakBound)
    (hz : VG.Proof.X448.Wide.pair (s.gpr .x4) (s.gpr .x5) = 0) :
    WP isa (.block ((List.range 8).flatMap (fun i => if i ≤ k ∧ k < i + 8 then
      [ld .x6 (a + 8 * i), ld .x9 (b + 8 * (k - i))] ++ term else []))) s fun t =>
      VG.Proof.X448.Wide.pair (t.gpr .x4) (t.gpr .x5) = VG.Proof.X448.Wide.rows (limbs s.mem base a) (limbs s.mem base b) 8 k ∧
      t.mem = s.mem ∧ Keeps VG.Proof.Curve448.AArch64.colRegs s t := by
  let f := limbs s.mem base a
  let g := limbs s.mem base b
  let inv := fun n (t : State) =>
    VG.Proof.X448.Wide.pair (t.gpr .x4) (t.gpr .x5) = colSum f g k n ∧
    t.mem = s.mem ∧ Keeps VG.Proof.Curve448.AArch64.colRegs s t
  have step : ∀ n t, n < 8 → inv n t →
      WP isa (.block (if n ≤ k ∧ k < n + 8 then
        [ld .x6 (a + 8 * n), ld .x9 (b + 8 * (k - n))] ++ term else [])) t (inv (n + 1)) := by
    intro n t hn ⟨tv, tm, tk⟩
    by_cases h : n ≤ k ∧ k < n + 8
    · rw [ite_eq_left h, WP.block_append_iff]
      have ts := hs.of_keeps tk (by decide)
      refine WP.mono (VG.Proof.Curve448.AArch64.loadTerm_ok ts ha hb ha8 hb8 hn (by omega)) fun u ⟨u6, u9, um, uk⟩ => ?_
      have uv : VG.Proof.X448.Wide.pair (u.gpr .x4) (u.gpr .x5) = colSum f g k n := by
        rw [uk.1 .x4 (by decide), uk.1 .x5 (by decide), tv]
      have av : (u.gpr .x6).toNat = f n := by rw [u6, tm]
      have bv : (u.gpr .x9).toNat = g (k - n) := by rw [u9, tm]
      have prod : f n * g (k - n) ≤ (weakBound - 1) ^ 2 := by
        rw [Nat.pow_two]
        exact Nat.mul_le_mul (by have fh : f n < weakBound := fa n hn; omega) (by have gh : g (k - n) < weakBound := fb (k - n) (by omega); omega)
      have cb := VG.Proof.Curve448.AArch64.rows_bound fa fb (n := n) (by omega) k
      rw [← colSum_eq] at cb
      change colSum f g k n ≤ n * (weakBound - 1) ^ 2 at cb
      have sum : (u.gpr .x6).toNat * (u.gpr .x9).toNat + VG.Proof.X448.Wide.pair (u.gpr .x4) (u.gpr .x5) < 2 ^ 128 := by
        rw [av, bv, uv]
        have bd : (n + 1) * (weakBound - 1) ^ 2 ≤ 8 * (weakBound - 1) ^ 2 :=
          Nat.mul_le_mul_right _ (by omega)
        have cap : 8 * (weakBound - 1) ^ 2 < 2 ^ 128 := by decide +kernel
        rw [Nat.add_mul, Nat.one_mul] at bd
        omega
      refine WP.mono (term_ok u sum) fun v ⟨vv, vm, vk⟩ => ?_
      refine ⟨?_, vm.trans (um.trans tm), ?_⟩
      · rw [vv, av, bv, uv, colSum, ite_eq_left h]
        omega
      · exact tk.trans ((uk.mono (by decide)).trans (vk.mono (by decide)))
    · rw [ite_eq_right h]
      apply WP.block_nil
      exact ⟨by rw [colSum, ite_eq_right h, Nat.add_zero]; exact tv, tm, tk⟩
  have init : inv 0 s := ⟨hz, rfl, Keeps.refl _ _⟩
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s init)
    fun t ⟨tv, tm, tk⟩ => ?_
  exact ⟨tv.trans (colSum_eq f g k 8), tm, tk⟩

theorem column_ok {s : State} {base : Addr} (hs : Scr s base) {a b k : Nat}
    (ha : a + 64 ≤ 8192) (hb : b + 64 ≤ 8192)
    (ha8 : a % 8 = 0) (hb8 : b % 8 = 0) (hk : k < 16)
    (fa : ∀ i < 8, limbs s.mem base a i < weakBound)
    (fb : ∀ i < 8, limbs s.mem base b i < weakBound) :
    WP isa (.block (column a b k)) s fun t =>
      coeff t.mem base ACC k = VG.Proof.X448.Wide.rows (limbs s.mem base a) (limbs s.mem base b) 8 k ∧
      Outside base (ACC + 16 * k) 16 s.mem t.mem ∧ Keeps VG.Proof.Curve448.AArch64.colRegs s t := by
  rw [column, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.zero_ok s) fun u ⟨uz, um, uk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.columnBody_ok (hs.of_keeps uk (by decide)) ha hb ha8 hb8
    (by rw [um]; exact fa) (by rw [um]; exact fb) uz) fun v ⟨vv, vm, vk⟩ => ?_
  have vs := (hs.of_keeps uk (by decide)).of_keeps vk (by decide)
  refine WP.mono (VG.Proof.Curve448.AArch64.store_ok vs hk) fun t ⟨tm, tk⟩ => ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [tm, coeff_put _ base _ _ (by simp only [ACC]; omega)
      (by simp only [ACC]; omega), ite_eq_left rfl, vv, um]
  · rw [tm, vm, um]
    exact putCoeff_outside _ _ _ _ (by simp only [ACC]; omega)
  · exact (uk.mono (by decide)).trans (vk.trans (tk.mono (by decide)))

end VG.Proof.Curve448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Columns`. -/
section

/-! Untrusted: the complete two-word coefficient array of a wide product. -/
namespace VG.Proof.Curve448.AArch64

open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ACC)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem columns_ok {s : State} {base : Addr} (hs : Scr s base) {a b : Nat}
    (ha : a + 64 ≤ ACC ∨ ACC + 256 ≤ a) (hb : b + 64 ≤ ACC ∨ ACC + 256 ≤ b)
    (ha' : a + 64 ≤ 8192) (hb' : b + 64 ≤ 8192) (ha8 : a % 8 = 0) (hb8 : b % 8 = 0)
    (fa : ∀ i < 8, limbs s.mem base a i < weakBound)
    (fb : ∀ i < 8, limbs s.mem base b i < weakBound) :
    WP isa (.block ((List.range 16).flatMap (column a b))) s fun t =>
      (∀ k < 16, coeff t.mem base ACC k = VG.Proof.X448.Wide.rows (limbs s.mem base a) (limbs s.mem base b) 8 k) ∧
      Outside base ACC 256 s.mem t.mem ∧ Keeps VG.Proof.Curve448.AArch64.colRegs s t := by
  let f := limbs s.mem base a
  let g := limbs s.mem base b
  let inv := fun n (t : State) =>
    (∀ k < 16, coeff t.mem base ACC k = if k < n then VG.Proof.X448.Wide.rows f g 8 k else coeff s.mem base ACC k) ∧
    Outside base ACC 256 s.mem t.mem ∧ Keeps VG.Proof.Curve448.AArch64.colRegs s t
  have step : ∀ n t, n < 16 → inv n t → WP isa (.block (column a b n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    have av : ∀ i < 8, limbs t.mem base a i = f i := by
      intro i hi
      exact congrArg BitVec.toNat (tm.word (by omega) (by omega))
    have bv : ∀ i < 8, limbs t.mem base b i = g i := by
      intro i hi
      exact congrArg BitVec.toNat (tm.word (by omega) (by omega))
    refine WP.mono (VG.Proof.Curve448.AArch64.column_ok (hs.of_keeps tk (by decide)) ha' hb' ha8 hb8 hn
      (by intro i hi; rw [av i hi]; exact fa i hi)
      (by intro i hi; rw [bv i hi]; exact fb i hi)) fun u ⟨uv, um, uk⟩ => ?_
    refine ⟨?_, tm.trans (um.mono (by omega) (by omega)), tk.trans uk⟩
    intro k hk
    by_cases h : k = n
    · subst k
      rw [ite_eq_left (by omega), uv]
      exact rows_congr av bv (by decide) n
    · have hsep : ACC + 16 * k + 16 ≤ ACC + 16 * n ∨
          ACC + 16 * n + 16 ≤ ACC + 16 * k := by omega
      change VG.Proof.X448.Wide.pair (word u.mem base (ACC + 16 * k)) (word u.mem base (ACC + 16 * k + 8)) = _
      rw [outside_coeff um hsep (by simp only [ACC]; omega)]
      change coeff t.mem base ACC k = _
      rw [tf k hk]
      have e : (k < n) = (k < n + 1) := propext (by omega)
      simp only [e]
  have init : inv 0 s := ⟨by intro k _; rw [ite_eq_right (by omega)], Outside.refl _ _ _ _, Keeps.refl _ _⟩
  refine WP.mono (wp_range_flatMap (M := isa) (N := 16) inv step 16 (by decide) s init)
    fun t ⟨tf, tm, tk⟩ => ?_
  exact ⟨fun k hk => (tf k hk).trans (ite_eq_left hk), tm, tk⟩

end VG.Proof.Curve448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Copy`. -/
section

/-!
# X448 on AArch64: copying field elements

Untrusted: everything here is checked by Lean. Eight persistent limbs are copied. Source and destination are
equal or disjoint; every limb is copied without changing its representation.
-/

namespace VG.Proof.Curve448.AArch64

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st)
open VG.Proof.X448.AArch64
open VG.Impl.Curve448.AArch64

theorem copyStep_ok {s : State} {base : Addr} (hs : Scr s base) {o a i : Nat}
    (ho : o + 128 ≤ 8192) (ha : a + 128 ≤ 8192) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0) (hi : i < 8) :
    WP isa (.block [ld .x4 (a + 8 * i), st .x4 (o + 8 * i)]) s fun t =>
      t.mem = s.mem.writeW (off base (o + 8 * i)) (word s.mem base (a + 8 * i)) ∧ Keeps VG.Proof.X448.AArch64.clob s t := by
  have l := hs.read (d := a + 8 * i) (n := 8) (by omega)
  have w := hs.write (d := o + 8 * i) (n := 8) (by omega)
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := ⟨by omega, by omega⟩
  have oe : (o + 8 * i) % 8 = 0 ∧ o + 8 * i < 32768 := ⟨by omega, by omega⟩
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
      Outside base o 128 s.mem t.mem ∧ Keeps VG.Proof.X448.AArch64.clob s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base o i = limbs s.mem base a i) ∧
    (∀ i, n ≤ i → i < 8 → limbs t.mem base a i = limbs s.mem base a i) ∧
    Outside base o 128 s.mem t.mem ∧ Keeps VG.Proof.X448.AArch64.clob s t
  have st : ∀ n t, n < 8 → inv n t →
      WP isa (.block [ld .x4 (a + 8 * n), st .x4 (o + 8 * n)]) t (inv (n + 1)) := by
    intro n t hn ⟨tf, ta, tm, tk⟩
    refine WP.mono (VG.Proof.Curve448.AArch64.copyStep_ok (hs.of_keeps tk (by decide)) ho ha ho8 ha8 hn) fun u ⟨um, uk⟩ => ?_
    have out : Outside base (o + 8 * n) 8 t.mem u.mem := by
      rw [um]; exact writeW_outside _ _ _ (by omega)
    refine ⟨?_, ?_, tm.trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    · intro i hi
      change (word u.mem base (o + 8 * i)).toNat = _
      rw [um, word_write t.mem base (by omega) (by omega)]
      by_cases h : i = n
      · rw [ite_eq_left h, h]; exact ta n (by omega) hn
      · rw [ite_eq_right h]; exact tf i (by omega)
    · intro i hi hi'
      change (word u.mem base (a + 8 * i)).toNat = _
      rw [out.word (by rcases hsep with h | h | h <;> omega) (by omega)]
      exact ta i (by omega) hi'
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv st 8 (by decide) s ?_)
    fun t ⟨tf, _, tm, tk⟩ => ⟨tf, tm, tk⟩
  exact ⟨fun _ hi => by omega, fun _ _ _ => rfl, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.Curve448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Legacy`. -/
section

namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ld st TMP ACC)
open VG.Impl.X448.AArch64.Wide (PACKA)
open VG.Proof.X448.AArch64

theorem fromLegacy_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (ho : VG.Proof.X448.AArch64.Slot o) (ho8 : o % 8 = 0) (hb : VG.Proof.X448.AArch64.Bounded s.mem base o) :
    WP isa (.block (Impl.Curve448.AArch64.fromLegacy o)) s fun t =>
      VG.Proof.X448.AArch64.Op base o s t ∧ VG.Proof.Curve448.AArch64.Bounded t.mem base o ∧ VG.Proof.Curve448.AArch64.F t.mem base o = VG.Proof.X448.AArch64.F s.mem base o := by
  rw [Impl.Curve448.AArch64.fromLegacy, WP.block_append_iff]
  refine WP.mono (pack_ok hs (o := PACKA) (by decide) (Nat.le_trans ho (by decide))
    (by decide) ho8 (Or.inl (Nat.le_trans ho (by decide))) hb) fun u ⟨uf, um, uk⟩ => ?_
  refine WP.mono (VG.Proof.Curve448.AArch64.copy_ok (o := o) (a := PACKA) (hs.of_keeps uk (by decide)) (Nat.le_trans ho (by decide))
    (by decide) ho8 (by decide) (Or.inr (Or.inl (Nat.le_trans ho (by decide))))) fun t ⟨tf, tm, tk⟩ => ?_
  have out : ∀ i < 8, limbs t.mem base o i = paired (limbs s.mem base o) i :=
    fun i hi => (tf i hi).trans (uf i hi)
  refine ⟨⟨(uk.mono (by decide)).trans tk,
    (FieldMem.work um (by decide) (by decide)).trans (.output tm)⟩, ?_, ?_⟩
  · intro i hi; rw [out i hi]
    exact Nat.lt_trans (paired_bound hb i hi) (by simp only [weakBound]; omega)
  · apply congrArg VG.Proof.X448.toFe
    rw [show VG.Proof.Curve448.AArch64.fe t.mem base o = VG.Proof.X448.Wide.valN (paired (limbs s.mem base o)) 8 from
      VG.Proof.X448.Wide.valN_congr out, paired_val]

theorem legacyEval_ok {s : State} {base : Addr} (hs : Scr s base) {o i : Nat}
    (ho : VG.Proof.X448.AArch64.Slot o) (ho8 : o % 8 = 0) (hi : i < 8) :
    WP isa (.block (Impl.Curve448.AArch64.legacyEval o i)) s fun t =>
      VG.Proof.X448.Wide.pair (t.gpr .x4) (t.gpr .x5) = limbs s.mem base o i ∧ t.mem = s.mem ∧ Keeps VG.Proof.X448.AArch64.clob s t := by
  have l := hs.read (d := o + 8 * i) (n := 8) (by change o + 128 ≤ 3584 at ho; omega)
  have oe : (o + 8 * i) % 8 = 0 ∧ o + 8 * i < 32768 := by change o + 128 ≤ 3584 at ho; omega
  apply WP.of_runBlock
  simp only [Impl.Curve448.AArch64.legacyEval, ld, runBlock_cons, runStep_some, runBlock_nil, exec,
    addr, Size.bytes, Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    State.load, RegUpd.gpr_write, RegUpd.mem_write, BitVec.setWidth_eq,
    oe, and_self, hs.x3, l, ite_true, ite_false, reduceCtorEq, Option.map_some,
    Option.bind_some, read8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · simp only [VG.Proof.X448.Wide.pair, show (BitVec.setWidth 64 (0 : BitVec 16)).toNat = 0 from rfl,
      Nat.mul_zero, Nat.add_zero]
  · simp only [RegUpd.gpr_write, show r ≠ .x4 from fun h => hr (by subst r; decide),
      show r ≠ .x5 from fun h => hr (by subst r; decide), ite_false]

theorem toLegacy_ok' {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (ho : VG.Proof.X448.AArch64.Slot o) (ho8 : o % 8 = 0) (cap : ∀ i < 8, limbs s.mem base o i < 2 ^ 118) :
    WP isa (.block (Impl.Curve448.AArch64.toLegacy o)) s fun t =>
      VG.Proof.X448.AArch64.Op base o s t ∧ VG.Proof.X448.AArch64.Bounded t.mem base o ∧
      VG.Proof.X448.AArch64.F t.mem base o = VG.Proof.Curve448.AArch64.F s.mem base o := by
  rw [Impl.Curve448.AArch64.toLegacy, WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.stage_ok hs (code := Impl.Curve448.AArch64.legacyEval o)
    (f := limbs s.mem base o) ?_) fun u ⟨uf, um, uk⟩ => ?_
  · intro i hi t ts tm
    refine WP.mono (VG.Proof.Curve448.AArch64.legacyEval_ok ts ho ho8 hi) fun v ⟨vf, vm, vk⟩ => ⟨?_, vm, vk⟩
    rw [VG.Proof.Curve448.AArch64.input_limb tm ho hi] at vf; exact vf
  · refine WP.mono (tailNormalize_ok (hs.of_keeps uk (by decide)) ho ho8 uf cap) fun t ⟨tf, tm, tk⟩ => ?_
    have out := encoded_limbs tf
    refine ⟨⟨uk.trans (tk.mono (by decide)), (FieldMem.work um (by decide) (by decide)).trans tm⟩, ?_, ?_⟩
    · intro i hi; rw [out i hi]
      exact unpacked_bound (fun j _ => VG.Proof.X448.Wide.digit_lt _ j) i hi
    · apply VG.Proof.X448.toFe_congr
      rw [show VG.Proof.X448.AArch64.fe t.mem base o = VG.Proof.X448.valN
        (unpacked (VG.Proof.X448.Wide.normalized (limbs s.mem base o))) 16 from VG.Proof.X448.valN_congr out,
        unpacked_val, VG.Proof.X448.Wide.normalized_mod cap]

theorem toLegacy_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (ho : VG.Proof.X448.AArch64.Slot o) (ho8 : o % 8 = 0) (hb : VG.Proof.Curve448.AArch64.Bounded s.mem base o) :
    WP isa (.block (Impl.Curve448.AArch64.toLegacy o)) s fun t =>
      VG.Proof.X448.AArch64.Op base o s t ∧ VG.Proof.X448.AArch64.Bounded t.mem base o ∧
      VG.Proof.X448.AArch64.F t.mem base o = VG.Proof.Curve448.AArch64.F s.mem base o :=
  VG.Proof.Curve448.AArch64.toLegacy_ok' hs ho ho8 fun i hi => Nat.lt_trans (hb i hi) (by decide)
end VG.Proof.Curve448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.SubEval`. -/
section

/-! Untrusted: pointwise coefficient in registers, without an intermediate store. -/
namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ld st)
open VG.Proof.X448.AArch64
open VG.Impl.Curve448.AArch64

theorem subEval_ok {s : State} {base : Addr} (hs : Scr s base) {a b i : Nat}
    (ha : VG.Proof.X448.AArch64.Slot a) (ha8 : a % 8 = 0) (hb : VG.Proof.X448.AArch64.Slot b) (hb8 : b % 8 = 0) (hi : i < 8)
    (ab : limbs s.mem base a i < weakBound) (bb : limbs s.mem base b i < weakBound) :
    WP isa (.block (Impl.Curve448.AArch64.subEval a b i)) s fun t =>
      VG.Proof.X448.Wide.pair (t.gpr .x4) (t.gpr .x5) = VG.Proof.X448.Wide.Representation.difference (limbs s.mem base a) (limbs s.mem base b) i ∧ t.mem = s.mem ∧ Keeps [.x4, .x5] s t := by
  have la := hs.read (d := a + 8 * i) (n := 8) (by change a + 128 ≤ 3584 at ha; omega)
  have lb := hs.read (d := b + 8 * i) (n := 8) (by change b + 128 ≤ 3584 at hb; omega)
  have biasb := bias_ge i
  have biashi : VG.Proof.X448.Wide.Representation.bias i < 2 ^ 59 := by unfold VG.Proof.X448.Wide.Representation.bias; split <;> decide +kernel
  have biasword : (((((BitVec.setWidth 64 (if i = 4 then (0xfff8 : BitVec 16) else 0xfffc)) &&& ~~~((0xffff : BitVec 64) <<< 16)) ||| ((BitVec.setWidth 64 (0xffff : BitVec 16)) <<< 16)) &&& ~~~((0xffff : BitVec 64) <<< 32) ||| ((BitVec.setWidth 64 (0xffff : BitVec 16)) <<< 32)) &&& ~~~((0xffff : BitVec 64) <<< 48) ||| ((BitVec.setWidth 64 (0x03ff : BitVec 16)) <<< 48)).toNat = VG.Proof.X448.Wide.Representation.bias i := by
    by_cases h : i = 4 <;> simp only [h, ite_true, ite_false, VG.Proof.X448.Wide.Representation.bias] <;> decide +kernel
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := by
    change a + 128 ≤ 3584 at ha; omega
  have be : (b + 8 * i) % 8 = 0 ∧ b + 8 * i < 32768 := by
    change b + 128 ≤ 3584 at hb; omega
  apply WP.of_runBlock
  simp only [Impl.Curve448.AArch64.subEval, ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    Size.bits, Nat.reduceLT, Nat.reduceMul, BitVec.shiftLeft_zero, State.read, State.load, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq, ae, be, and_self,
    hs.x3, la, lb, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, read8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · simp only [VG.Proof.X448.Wide.pair, show (BitVec.setWidth 64 (0 : BitVec 16)).toNat = 0 from rfl,
      Nat.mul_zero, Nat.add_zero, BitVec.toNat_sub, BitVec.toNat_add, biasword]
    change (2 ^ 64 - limbs s.mem base b i +
      (limbs s.mem base a i + VG.Proof.X448.Wide.Representation.bias i) % 2 ^ 64) % 2 ^ 64 =
      limbs s.mem base a i + VG.Proof.X448.Wide.Representation.bias i - limbs s.mem base b i
    simp only [weakBound, VG.Proof.X448.Wide.radix] at ab bb biasb
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

end VG.Proof.Curve448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.SmallEval`. -/
section

namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide
open VG.Impl.X448.AArch64 (ld st)
open VG.Proof.X448.AArch64
open VG.Proof.Ed25519.AArch64 (mulHi read_x mul_lo_hi)

theorem smallEval_ok {s : State} {base : Addr} (hs : Scr s base) {a i : Nat}
    (ha : VG.Proof.X448.AArch64.Slot a) (ha8 : a % 8 = 0) (hi : i < 8) :
    WP isa (.block (Impl.Curve448.AArch64.smallEval a i)) s fun t =>
      VG.Proof.X448.Wide.pair (t.gpr .x4) (t.gpr .x5) = 39081 * limbs s.mem base a i ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5, .x6] s t := by
  have la := hs.read (d := a + 8 * i) (n := 8) (by change a + 128 ≤ 3584 at ha; omega)
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := by
    change a + 128 ≤ 3584 at ha; omega
  apply WP.of_runBlock
  simp only [Impl.Curve448.AArch64.smallEval, ld, runBlock_cons, runStep_some, runBlock_nil, exec,
    addr, Size.bytes, Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    State.read, State.load, RegUpd.gpr_write, RegUpd.mem_write,
    BitVec.setWidth_eq, ae, and_self, hs.x3, la, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, read8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · have h := mul_lo_hi (word s.mem base (a + 8 * i)) (BitVec.setWidth 64 (39081 : BitVec 16))
    rw [show (BitVec.setWidth 64 (39081 : BitVec 16)).toNat = 39081 by decide, Nat.mul_comm _ 39081] at h
    dsimp only [VG.Proof.X448.Wide.pair, mulHi, Size.bits] at h ⊢
    exact h
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]
end VG.Proof.Curve448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Pointwise`. -/
section

namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Proof.X448.AArch64

theorem add_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : VG.Proof.X448.AArch64.Slot o) (ho8 : o % 8 = 0) (ha : VG.Proof.X448.AArch64.Slot a) (ha8 : a % 8 = 0)
    (hb : VG.Proof.X448.AArch64.Slot b) (hb8 : b % 8 = 0) (ab : VG.Proof.Curve448.AArch64.Bounded s.mem base a) (bb : VG.Proof.Curve448.AArch64.Bounded s.mem base b) :
    WP isa (.block (Impl.Curve448.AArch64.add o a b)) s fun t =>
      VG.Proof.X448.AArch64.Op base o s t ∧ VG.Proof.Curve448.AArch64.Bounded t.mem base o ∧ VG.Proof.Curve448.AArch64.F t.mem base o = VG.Proof.Curve448.AArch64.F s.mem base a + VG.Proof.Curve448.AArch64.F s.mem base b := by
  let f := fun i => limbs s.mem base a i + limbs s.mem base b i
  have fb : Within (VG.Proof.X448.Wide.radix * 6) f := by
    intro i hi; have h1 := ab i hi; have h2 := bb i hi
    change limbs s.mem base a i + limbs s.mem base b i < _
    simp only [weakBound, VG.Proof.X448.Wide.radix] at h1 h2 ⊢; omega
  refine WP.mono (VG.Proof.Curve448.AArch64.stage_point hs ho ho8 fb ?_) fun t ⟨op, tb, tv⟩ => ⟨op, tb, VG.Proof.X448.toFe_add ?_⟩
  · intro i hi t ts tm
    have ea := VG.Proof.Curve448.AArch64.input_limb tm ha hi
    have eb := VG.Proof.Curve448.AArch64.input_limb tm hb hi
    refine WP.mono (VG.Proof.Curve448.AArch64.addEval_ok ts ha ha8 hb hb8 hi (ea ▸ ab i hi) (eb ▸ bb i hi))
      fun u ⟨uv, um, uk⟩ => ⟨?_, um, uk.mono (by decide)⟩
    rw [ea, eb] at uv; exact uv
  · rw [tv, VG.Proof.X448.Wide.valN_add]

theorem sub_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : VG.Proof.X448.AArch64.Slot o) (ho8 : o % 8 = 0) (ha : VG.Proof.X448.AArch64.Slot a) (ha8 : a % 8 = 0)
    (hb : VG.Proof.X448.AArch64.Slot b) (hb8 : b % 8 = 0) (ab : VG.Proof.Curve448.AArch64.Bounded s.mem base a) (bb : VG.Proof.Curve448.AArch64.Bounded s.mem base b) :
    WP isa (.block (Impl.Curve448.AArch64.sub o a b)) s fun t =>
      VG.Proof.X448.AArch64.Op base o s t ∧ VG.Proof.Curve448.AArch64.Bounded t.mem base o ∧ VG.Proof.Curve448.AArch64.F t.mem base o = VG.Proof.Curve448.AArch64.F s.mem base a - VG.Proof.Curve448.AArch64.F s.mem base b := by
  let f := VG.Proof.X448.Wide.Representation.difference (limbs s.mem base a) (limbs s.mem base b)
  have fb : Within (VG.Proof.X448.Wide.radix * 6) f := by
    intro i hi; have h := ab i hi
    change VG.Proof.X448.Wide.Representation.difference (limbs s.mem base a) (limbs s.mem base b) i < _
    simp only [VG.Proof.X448.Wide.Representation.difference, VG.Proof.X448.Wide.Representation.bias, weakBound, VG.Proof.X448.Wide.radix] at h ⊢
    split <;> omega
  refine WP.mono (VG.Proof.Curve448.AArch64.stage_point hs ho ho8 fb ?_) fun t ⟨op, tb, tv⟩ => ⟨op, tb, VG.Proof.X448.toFe_sub ?_⟩
  · intro i hi t ts tm
    have ea := VG.Proof.Curve448.AArch64.input_limb tm ha hi
    have eb := VG.Proof.Curve448.AArch64.input_limb tm hb hi
    refine WP.mono (VG.Proof.Curve448.AArch64.subEval_ok ts ha ha8 hb hb8 hi (ea ▸ ab i hi) (eb ▸ bb i hi))
      fun u ⟨uv, um, uk⟩ => ⟨?_, um, uk.mono (by decide)⟩
    simp only [VG.Proof.X448.Wide.Representation.difference, ea, eb] at uv; exact uv
  · rw [Nat.add_mod, tv, ← Nat.add_mod, VG.Proof.X448.Wide.Representation.difference_val bb,
      Nat.mul_comm 4 Spec.X448.P, Nat.add_mul_mod_self_left]

theorem small_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : VG.Proof.X448.AArch64.Slot o) (ho8 : o % 8 = 0) (ha : VG.Proof.X448.AArch64.Slot a) (ha8 : a % 8 = 0)
    (ab : VG.Proof.Curve448.AArch64.Bounded s.mem base a) :
    WP isa (.block (Impl.Curve448.AArch64.small o a)) s fun t =>
      VG.Proof.X448.AArch64.Op base o s t ∧ VG.Proof.Curve448.AArch64.Bounded t.mem base o ∧ VG.Proof.Curve448.AArch64.F t.mem base o = Spec.X448.a24 * VG.Proof.Curve448.AArch64.F s.mem base a := by
  let f := fun i => 39081 * limbs s.mem base a i
  have fb : Within (2 ^ 118) f := by
    intro i hi
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 39081 (Nat.le_of_lt (ab i hi))) (by decide)
  refine WP.mono (VG.Proof.Curve448.AArch64.stage_normalize hs ho ho8 fb ?_) fun t ⟨op, tb, tv⟩ => ⟨op, tb, VG.Proof.X448.toFe_a24 ?_⟩
  · intro i hi t ts tm
    refine WP.mono (VG.Proof.Curve448.AArch64.smallEval_ok ts ha ha8 hi) fun u ⟨uv, um, uk⟩ => ⟨?_, um, uk.mono (by decide)⟩
    rw [VG.Proof.Curve448.AArch64.input_limb tm ha hi] at uv; exact uv
  · rw [tv, VG.Proof.X448.Wide.valN_scale]
end VG.Proof.Curve448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Product`. -/
section

namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ACC TMP)
open VG.Proof.X448.AArch64

theorem product_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : VG.Proof.X448.AArch64.Slot o) (ho8 : o % 8 = 0) (ha : VG.Proof.X448.AArch64.Slot a) (ha8 : a % 8 = 0)
    (hb : VG.Proof.X448.AArch64.Slot b) (hb8 : b % 8 = 0) (ab : VG.Proof.Curve448.AArch64.Bounded s.mem base a) (bb : VG.Proof.Curve448.AArch64.Bounded s.mem base b) :
    WP isa (Impl.Curve448.AArch64.product o a b) s fun t =>
      VG.Proof.X448.AArch64.Op base o s t ∧ VG.Proof.Curve448.AArch64.Bounded t.mem base o ∧ VG.Proof.Curve448.AArch64.F t.mem base o = VG.Proof.Curve448.AArch64.F s.mem base a * VG.Proof.Curve448.AArch64.F s.mem base b := by
  let f := limbs s.mem base a
  let g := limbs s.mem base b
  rw [Impl.Curve448.AArch64.product, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.columns_ok hs (Or.inl (by omega)) (Or.inl (by omega))
    (by have := ha; change a + 128 ≤ 3584 at this; omega)
    (by have := hb; change b + 128 ≤ 3584 at this; omega) ha8 hb8 ab bb) fun s₁ ⟨c₁, m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have raw : ∀ i < 16, coeff s₁.mem base ACC i < 2 ^ 116 := by
    intro i hi
    rw [c₁ i hi]
    exact Nat.lt_of_le_of_lt (VG.Proof.Curve448.AArch64.rows_bound ab bb (by decide) i) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.reduce_ok hs₁ raw) fun s₂ ⟨r₂, m₂, k₂⟩ => ?_
  have red := VG.Proof.X448.Wide.reduced_bound raw
  refine WP.mono (VG.Proof.Curve448.AArch64.normalize_ok (hs₁.of_keeps k₂ (by decide)) ho ho8 r₂ red) fun t ⟨tf, tm, tk⟩ => ?_
  have val : VG.Proof.Curve448.AArch64.fe t.mem base o % Spec.X448.P = (VG.Proof.Curve448.AArch64.fe s.mem base a * VG.Proof.Curve448.AArch64.fe s.mem base b) % Spec.X448.P := by
    rw [show VG.Proof.Curve448.AArch64.fe t.mem base o = VG.Proof.X448.Wide.valN
        (VG.Proof.X448.Wide.folded (VG.Proof.X448.Wide.folded (VG.Proof.X448.Wide.reduced (coeff s₁.mem base ACC)))) 8 from
        VG.Proof.X448.Wide.valN_congr tf, twice_mod, VG.Proof.X448.Wide.reduced_mod,
      VG.Proof.X448.Wide.valN_congr c₁, rows_val f g (by decide)]
  refine ⟨⟨?_, ?_⟩, ?_, VG.Proof.X448.toFe_mul val⟩
  · exact (k₁.mono (by decide)).trans ((k₂.mono (by decide)).trans (tk.mono (by decide)))
  · exact (FieldMem.work m₁ (by decide) (by decide)).trans
      ((FieldMem.work m₂ (by decide) (by decide)).trans tm)
  · intro i hi; rw [tf i hi]; exact twice_weak red i hi
end VG.Proof.Curve448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.SymmetricColumn`. -/
section

/-! Untrusted: store a symmetric square diagonal. -/
namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ACC)
open VG.Impl.X448.AArch64.Wide VG.Impl.X448.AArch64.Cached VG.Proof.X448.AArch64

theorem symmetricColumn_ok {s : State} {base : Addr} (hs : Scr s base) {f : Nat → Nat} {k : Nat}
    (hk : k < 16) (fc : ∀ i < 8, (s.gpr (cacheReg i)).toNat = f i)
    (fb : ∀ i < 8, f i < weakBound) :
    WP isa (.block (Impl.X448.AArch64.Symmetric.column k)) s fun t =>
      coeff t.mem base ACC k = VG.Proof.X448.Wide.rows f f 8 k ∧
      Outside base (ACC + 16 * k) 16 s.mem t.mem ∧ Keeps termRegs s t := by
  rw [Impl.X448.AArch64.Symmetric.column, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.zero_ok s) fun u ⟨uz, um, uk⟩ => ?_
  rw [WP.block_append_iff]
  have uk' : Keeps termRegs s u := uk.mono (by decide)
  refine WP.mono (VG.Proof.Curve448.AArch64.accumSquareBody_ok hk (by
    intro i hi; rw [uk'.1 _ (cacheReg_kept hi)]; exact fc i hi) fb (by decide) uz)
    fun v ⟨vv, vm, vk⟩ => ?_
  have vs := (hs.of_keeps uk (by decide)).of_keeps vk (by decide)
  refine WP.mono (VG.Proof.X448.Wide.store_ok vs hk) fun t ⟨tm, tk⟩ => ?_
  refine ⟨?_, ?_, uk'.trans (vk.trans (tk.mono (by decide)))⟩
  · rw [tm, coeff_put _ base _ _ (by simp only [ACC]; omega)
      (by simp only [ACC]; omega), ite_eq_left rfl, vv, Nat.zero_add]
  · rw [tm, vm, um]
    exact putCoeff_outside _ _ _ _ (by simp only [ACC]; omega)
end VG.Proof.Curve448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.SymmetricColumns`. -/
section

/-! Untrusted: the complete two-word coefficient array of a wide product. -/
namespace VG.Proof.Curve448.AArch64

open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ACC)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem symmetricColumns_ok {s : State} {base : Addr} (hs : Scr s base) {f : Nat → Nat}
    (fc : ∀ i < 8, (s.gpr (Impl.X448.AArch64.Cached.cacheReg i)).toNat = f i)
    (fb : ∀ i < 8, f i < weakBound) :
    WP isa (.block ((List.range 16).flatMap (Impl.X448.AArch64.Symmetric.column))) s fun t =>
      (∀ k < 16, coeff t.mem base ACC k = VG.Proof.X448.Wide.rows f f 8 k) ∧
      Outside base ACC 256 s.mem t.mem ∧ Keeps termRegs s t := by
  let inv := fun n (t : State) =>
    (∀ k < 16, coeff t.mem base ACC k = if k < n then VG.Proof.X448.Wide.rows f f 8 k else coeff s.mem base ACC k) ∧
    Outside base ACC 256 s.mem t.mem ∧ Keeps termRegs s t
  have step : ∀ n t, n < 16 → inv n t → WP isa (.block (Impl.X448.AArch64.Symmetric.column n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (VG.Proof.Curve448.AArch64.symmetricColumn_ok (hs.of_keeps tk (by decide)) hn (by
      intro i hi; rw [tk.1 _ (cacheReg_kept hi)]; exact fc i hi) fb) fun u ⟨uv, um, uk⟩ => ?_
    refine ⟨?_, tm.trans (um.mono (by omega) (by omega)), tk.trans uk⟩
    intro k hk
    by_cases h : k = n
    · subst k
      rw [ite_eq_left (by omega), uv]

    · have hsep : ACC + 16 * k + 16 ≤ ACC + 16 * n ∨
          ACC + 16 * n + 16 ≤ ACC + 16 * k := by omega
      change VG.Proof.X448.Wide.pair (word u.mem base (ACC + 16 * k)) (word u.mem base (ACC + 16 * k + 8)) = _
      rw [outside_coeff um hsep (by simp only [ACC]; omega)]
      change coeff t.mem base ACC k = _
      rw [tf k hk]
      have e : (k < n) = (k < n + 1) := propext (by omega)
      simp only [e]
  have init : inv 0 s := ⟨by intro k _; rw [ite_eq_right (by omega)], Outside.refl _ _ _ _, Keeps.refl _ _⟩
  refine WP.mono (wp_range_flatMap (M := isa) (N := 16) inv step 16 (by decide) s init)
    fun t ⟨tf, tm, tk⟩ => ?_
  exact ⟨fun k hk => (tf k hk).trans (ite_eq_left hk), tm, tk⟩

end VG.Proof.Curve448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Square`. -/
section

namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ACC TMP)
open VG.Impl.X448.AArch64.Cached VG.Proof.X448.AArch64

theorem square_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : VG.Proof.X448.AArch64.Slot o) (ho8 : o % 8 = 0) (ha : VG.Proof.X448.AArch64.Slot a) (ha8 : a % 8 = 0)
    (ab : VG.Proof.Curve448.AArch64.Bounded s.mem base a) :
    WP isa (Impl.Curve448.AArch64.sqr o a) s fun t =>
      VG.Proof.X448.AArch64.Op base o s t ∧ VG.Proof.Curve448.AArch64.Bounded t.mem base o ∧ VG.Proof.Curve448.AArch64.F t.mem base o = VG.Proof.Curve448.AArch64.F s.mem base a * VG.Proof.Curve448.AArch64.F s.mem base a := by
  let f := limbs s.mem base a
  rw [Impl.Curve448.AArch64.sqr, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadCached_ok hs (by have := ha; change a + 128 ≤ 3584 at this; omega) ha8)
    fun s₁ ⟨c₁, m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have fc : ∀ i < 8, (s₁.gpr (cacheReg i)).toNat = f i := by intro i hi; rw [c₁ i hi]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.symmetricColumns_ok hs₁ fc ab) fun s₂ ⟨c₂, m₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have raw : ∀ i < 16, coeff s₂.mem base ACC i < 2 ^ 116 := by
    intro i hi; rw [c₂ i hi]
    exact Nat.lt_of_le_of_lt (VG.Proof.Curve448.AArch64.rows_bound ab ab (by decide) i) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.reduce_ok hs₂ raw) fun s₃ ⟨r₃, m₃, k₃⟩ => ?_
  have red := VG.Proof.X448.Wide.reduced_bound raw
  refine WP.mono (VG.Proof.Curve448.AArch64.normalize_ok (hs₂.of_keeps k₃ (by decide)) ho ho8 r₃ red) fun t ⟨tf, tm, tk⟩ => ?_
  have val : VG.Proof.Curve448.AArch64.fe t.mem base o % Spec.X448.P = (VG.Proof.Curve448.AArch64.fe s.mem base a * VG.Proof.Curve448.AArch64.fe s.mem base a) % Spec.X448.P := by
    rw [show VG.Proof.Curve448.AArch64.fe t.mem base o = VG.Proof.X448.Wide.valN
        (VG.Proof.X448.Wide.folded (VG.Proof.X448.Wide.folded (VG.Proof.X448.Wide.reduced (coeff s₂.mem base ACC)))) 8 from
        VG.Proof.X448.Wide.valN_congr tf, twice_mod, VG.Proof.X448.Wide.reduced_mod,
      VG.Proof.X448.Wide.valN_congr c₂, rows_val f f (by decide)]
  refine ⟨⟨?_, ?_⟩, ?_, VG.Proof.X448.toFe_mul val⟩
  · exact (k₁.mono (by decide)).trans ((k₂.mono (by decide)).trans
      ((k₃.mono (by decide)).trans (tk.mono (by decide))))
  · rw [m₁] at m₂
    exact (FieldMem.work m₂ (by decide) (by decide)).trans
      ((FieldMem.work m₃ (by decide) (by decide)).trans tm)
  · intro i hi; rw [tf i hi]; exact twice_weak red i hi

theorem mul_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : VG.Proof.X448.AArch64.Slot o) (ho8 : o % 8 = 0) (ha : VG.Proof.X448.AArch64.Slot a) (ha8 : a % 8 = 0)
    (hb : VG.Proof.X448.AArch64.Slot b) (hb8 : b % 8 = 0) (ab : VG.Proof.Curve448.AArch64.Bounded s.mem base a) (bb : VG.Proof.Curve448.AArch64.Bounded s.mem base b) :
    WP isa (Impl.Curve448.AArch64.mul o a b) s fun t =>
      VG.Proof.X448.AArch64.Op base o s t ∧ VG.Proof.Curve448.AArch64.Bounded t.mem base o ∧ VG.Proof.Curve448.AArch64.F t.mem base o = VG.Proof.Curve448.AArch64.F s.mem base a * VG.Proof.Curve448.AArch64.F s.mem base b := by
  rw [Impl.Curve448.AArch64.mul]
  by_cases h : a = b
  · rw [ite_eq_left h, ← h]; exact VG.Proof.Curve448.AArch64.square_ok hs ho ho8 ha ha8 ab
  · rw [ite_eq_right h]; exact VG.Proof.Curve448.AArch64.product_ok hs ho ho8 ha ha8 hb hb8 ab bb
end VG.Proof.Curve448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Swap`. -/
section

/-!
# X448 on AArch64: constant-time conditional swaps

Untrusted: everything here is checked by Lean. An XOR mask exchanges the
limbs without a branch or an address depending on the swap bit.
-/

namespace VG.Proof.Curve448.AArch64

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st)
open VG.Proof.X448.AArch64
open VG.Impl.Curve448.AArch64

def mask (sw : Bool) : BitVec 64 := if sw then BitVec.allOnes 64 else 0

theorem xor_sel (sw : Bool) (a b : BitVec 64) :
    a ^^^ ((a ^^^ b) &&& VG.Proof.Curve448.AArch64.mask sw) = (if sw then b else a) ∧
      b ^^^ ((a ^^^ b) &&& VG.Proof.Curve448.AArch64.mask sw) = (if sw then a else b) := by
  cases sw
  · simp only [VG.Proof.Curve448.AArch64.mask, Bool.false_eq_true, ite_false]
    constructor <;> (apply BitVec.eq_of_toNat_eq; simp)
  · simp only [VG.Proof.Curve448.AArch64.mask, ite_true, BitVec.and_allOnes]
    constructor
    · rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    · rw [BitVec.xor_comm a b, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem swapStep_ok {s : State} {base : Addr} (hs : Scr s base) {x y i : Nat}
    (hx : VG.Proof.X448.AArch64.Slot x) (hy : VG.Proof.X448.AArch64.Slot y) (hx8 : x % 8 = 0) (hy8 : y % 8 = 0) (hi : i < 8) {sw : Bool} (hc : s.gpr .x6 = VG.Proof.Curve448.AArch64.mask sw) :
    WP isa (.block
      [ld .x4 (x + 8 * i), ld .x5 (y + 8 * i), .logic .eor .x .x7 .x4 .x5,
        .logic .and .x .x7 .x7 .x6, .logic .eor .x .x4 .x4 .x7,
        .logic .eor .x .x5 .x5 .x7, st .x4 (x + 8 * i), st .x5 (y + 8 * i)]) s fun t =>
      t.mem = (s.mem.writeW (off base (x + 8 * i))
        (if sw then word s.mem base (y + 8 * i) else word s.mem base (x + 8 * i))).writeW
        (off base (y + 8 * i)) (if sw then word s.mem base (x + 8 * i) else word s.mem base (y + 8 * i)) ∧
      Keeps [.x4, .x5, .x7] s t := by
  have lx := hs.read (d := x + 8 * i) (n := 8) (by change x + 128 ≤ 3584 at hx; omega)
  have ly := hs.read (d := y + 8 * i) (n := 8) (by change y + 128 ≤ 3584 at hy; omega)
  have wx := hs.write (d := x + 8 * i) (n := 8) (by change x + 128 ≤ 3584 at hx; omega)
  have wy := hs.write (d := y + 8 * i) (n := 8) (by change y + 128 ≤ 3584 at hy; omega)
  have xe : (x + 8 * i) % 8 = 0 ∧ x + 8 * i < 32768 := by
    change x + 128 ≤ 3584 at hx; omega
  have ye : (y + 8 * i) % 8 = 0 ∧ y + 8 * i < 32768 := by
    change y + 128 ≤ 3584 at hy; omega
  apply WP.of_runBlock
  simp only [ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    State.read, State.load, State.store, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq, xe, ye, and_self,
    hs.x3, hc, lx, ly, wx, wy, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, read8_eq, write8_eq, Option.some.injEq, exists_eq_left']
  simp only [(VG.Proof.Curve448.AArch64.xor_sel sw _ _).1, (VG.Proof.Curve448.AArch64.xor_sel sw _ _).2]
  refine ⟨trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

/-- Reading two disjoint words after writing a limb pair. -/
theorem pair_write {m : Mem} {base : Addr} {x y n j : Nat} (hx : VG.Proof.X448.AArch64.Slot x) (hy : VG.Proof.X448.AArch64.Slot y)
    (hxy : x + 128 ≤ y ∨ y + 128 ≤ x) (hn : n < 8) (hj : j < 8) (vx vy : BitVec 64) :
    let m' := (m.writeW (off base (x + 8 * n)) vx).writeW (off base (y + 8 * n)) vy
    limbs m' base x j = (if j = n then vx.toNat else limbs m base x j) ∧
    limbs m' base y j = (if j = n then vy.toNat else limbs m base y j) := by
  have xb : x + 128 ≤ 8192 := Nat.le_trans hx (by decide)
  have yb : y + 128 ≤ 8192 := Nat.le_trans hy (by decide)
  dsimp only
  constructor
  · simp only [limbs, word]
    rw [Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide)]
    rw [show m.readW (off base (x + 8 * j)) 64 = word m base (x + 8 * j) from rfl]
    change (word (m.writeW (off base (x + 8 * n)) vx) base (x + 8 * j)).toNat = _
    rw [word_write m base (by omega) (by omega)]
    split <;> rfl
  · change (word ((m.writeW (off base (x + 8 * n)) vx).writeW (off base (y + 8 * n)) vy)
      base (y + 8 * j)).toNat = _
    rw [word_write (m.writeW (off base (x + 8 * n)) vx) base (by omega) (by omega)]
    by_cases h : j = n
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h]
      apply congrArg BitVec.toNat
      exact Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide)

/-- Swap all eight limbs under the mask, preserving all other bytes. -/
theorem cswap_ok {s : State} {base : Addr} (hs : Scr s base) {x y : Nat} (hx : VG.Proof.X448.AArch64.Slot x) (hy : VG.Proof.X448.AArch64.Slot y)
    (hx8 : x % 8 = 0) (hy8 : y % 8 = 0)
    (hxy : x + 128 ≤ y ∨ y + 128 ≤ x) {sw : Bool} (hc : s.gpr .x6 = VG.Proof.Curve448.AArch64.mask sw) :
    WP isa (.block (VG.Impl.Curve448.AArch64.cswap x y)) s fun t =>
      (∀ i < 8, limbs t.mem base x i = if sw then limbs s.mem base y i else limbs s.mem base x i) ∧
      (∀ i < 8, limbs t.mem base y i = if sw then limbs s.mem base x i else limbs s.mem base y i) ∧
      Outside2 base x 128 y 128 s.mem t.mem ∧ Keeps [.x4, .x5, .x7] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base x i = if sw then limbs s.mem base y i else limbs s.mem base x i) ∧
    (∀ i < n, limbs t.mem base y i = if sw then limbs s.mem base x i else limbs s.mem base y i) ∧
    Outside2 base x (8 * n) y (8 * n) s.mem t.mem ∧ Keeps [.x4, .x5, .x7] s t
  have xb : x + 128 ≤ 8192 := Nat.le_trans hx (by decide)
  have yb : y + 128 ≤ 8192 := Nat.le_trans hy (by decide)
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block
      [ld .x4 (x + 8 * n), ld .x5 (y + 8 * n), .logic .eor .x .x7 .x4 .x5,
        .logic .and .x .x7 .x7 .x6, .logic .eor .x .x4 .x4 .x7,
        .logic .eor .x .x5 .x5 .x7, st .x4 (x + 8 * n), st .x5 (y + 8 * n)]) t (inv (n + 1)) := by
    intro n t hn ⟨tx, ty, tm, tk⟩
    have tc := (tk.1 .x6 (by decide)).trans hc
    refine WP.mono (VG.Proof.Curve448.AArch64.swapStep_ok (hs.of_keeps tk (by decide)) hx hy hx8 hy8 hn tc) fun u ⟨um, uk⟩ => ?_
    have ex : limbs t.mem base x n = limbs s.mem base x n :=
      congrArg BitVec.toNat (tm.word (by omega) (by omega) (by omega))
    have ey : limbs t.mem base y n = limbs s.mem base y n :=
      congrArg BitVec.toNat (tm.word (by omega) (by omega) (by omega))
    have pair := fun (j : Nat) (hj : j < 8) => VG.Proof.Curve448.AArch64.pair_write (m := t.mem) (base := base) hx hy hxy hn hj
      (if sw then word t.mem base (y + 8 * n) else word t.mem base (x + 8 * n))
      (if sw then word t.mem base (x + 8 * n) else word t.mem base (y + 8 * n))
    refine ⟨?_, ?_, ?_, tk.trans uk⟩
    · intro j hj
      rw [um, (pair j (by omega)).1]
      by_cases h : j = n
      · rw [ite_eq_left h, h]
        cases sw <;> simp only [ite_true, Bool.false_eq_true, ite_false] <;> with_reducible assumption
      · rw [ite_eq_right h]; exact tx j (by omega)
    · intro j hj
      rw [um, (pair j (by omega)).2]
      by_cases h : j = n
      · rw [ite_eq_left h, h]
        cases sw <;> simp only [ite_true, Bool.false_eq_true, ite_false] <;> with_reducible assumption
      · rw [ite_eq_right h]; exact ty j (by omega)
    · refine (tm.mono (by omega) (by omega)).trans ?_
      intro p hp hq
      rw [um, writeW_outside _ _ _ (by omega : y + 8 * n + 8 ≤ 8192) p (by omega),
        writeW_outside _ _ _ (by omega : x + 8 * n + 8 ≤ 8192) p (by omega)]
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hi => by omega, fun _ hi => by omega, Outside2.refl _ _ _ _ _ _, Keeps.refl _ _⟩) fun t ⟨tx, ty, tm, tk⟩ => ?_
  exact ⟨tx, ty, tm.mono (by decide) (by decide), tk⟩

end VG.Proof.Curve448.AArch64

end
