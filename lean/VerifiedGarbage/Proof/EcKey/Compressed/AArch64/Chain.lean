module

public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64.Chain
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Chain
public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFnG
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy

/-! # Refinement of field-call chains to the existing exponent-chain semantics -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.AArch64.Chain
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

structure Backend (P : ChainCfg) : Prop where
  sound : ∀ f m, Mont.callOf P.M = some (f, m) → VG.Proof.Weierstrass.AArch64.Mont.ModOk P.M.n m
  low : Mont.callOf P.M = none ∨
    P.acc + 8 * P.M.n ≤ Mont.own P.M.n ∧ P.base + 8 * P.M.n ≤ Mont.own P.M.n ∧
      P.tbl + 9 * (8 * P.M.n) ≤ Mont.own P.M.n

 theorem mul_ok {P : ChainCfg} (B : Backend P) {base : Addr} {size m : Nat} {s : State}
    (hs : Scr s base size) (hM : ModOkA P.M size m s.mem base) (hA : ModA P.M)
    {o a b : Nat} (ho : o + 8 * P.M.n ≤ size) (ha : a + 8 * P.M.n ≤ size)
    (hb : b + 8 * P.M.n ≤ size) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0) (hb8 : b % 8 = 0)
    (hB : wordsVal s.mem base b P.M.n < m)
    (hslots : ∀ x ∈ [o, a, b], x = P.acc ∨ x = P.base ∨
      (P.tbl ≤ x ∧ x + 8 * P.M.n ≤ P.tbl + 9 * (8 * P.M.n))) :
    WP isa (VG.Impl.EcKey.Compressed.AArch64.Chain.mul P o a b) s fun t => OpKeep P.M base o s t ∧
      wordsVal t.mem base o P.M.n < m ∧
      wordsVal t.mem base o P.M.n * 2 ^ (64 * P.M.n) % m =
        wordsVal s.mem base a P.M.n * wordsVal s.mem base b P.M.n % m := by
  unfold VG.Impl.EcKey.Compressed.AArch64.Chain.mul
  cases hc : Mont.callOf P.M with
  | none => exact VG.Proof.Mont.AArch64.mul_ok hs hM hA ho ha hb ho8 ha8 hb8 hB
  | some fm =>
    obtain ⟨f, m'⟩ := fm
    obtain rfl := hM.call f m' hc
    have ht : P.M.tmp = Mont.moAt P.M.n := by
      unfold Mont.callOf at hc
      split at hc
      · assumption
      · cases hc
    have hl := B.low.resolve_left (by rw [hc]; simp)
    have hx : ∀ x ∈ [o, a, b], x + 8 * P.M.n ≤ Mont.own P.M.n := by
      intro x h
      rcases hslots x h with rfl | rfl | h
      · exact hl.1
      · exact hl.2.1
      · omega
    exact Mont.mulCall_ok hs hM (B.sound _ _ hc) ht (hx _ (by simp))
      (hx _ (by simp)) (hx _ (by simp)) hB

 theorem oddPowers_ok {P : ChainCfg} {N : Nat} (Inv : Nat → State → Prop)
    (hstep : ∀ k s, k < N → Inv k s →
      WP isa (VG.Impl.EcKey.Compressed.AArch64.Chain.mul P (P.slot (k + 1)) (P.slot k) (P.slot 8)) s (Inv (k + 1))) :
    ∀ n ≤ N, ∀ s, Inv 0 s → WP isa (VG.Impl.EcKey.Compressed.AArch64.Chain.oddPowers P n) s (Inv n) := by
  intro n hn
  induction n with
  | zero => exact fun _ h => WP.block_nil h
  | succ n ih =>
    intro s hs
    exact WP.seq (WP.mono (ih (by omega) s hs) fun t ht => hstep n t (by omega) ht)

theorem table_ok {P : ChainCfg} {base : Addr} {size m : Nat} [NeZero m] (hL : ChainLay P size) (B : Backend P)
    (hm : UnitMod m (2 ^ (64 * P.M.n))) {s₀ s : State} (h : ChainSt P base size m s₀ s)
    (hB : wordsVal s₀.mem base P.base P.M.n < m) :
    WP isa (VG.Impl.EcKey.Compressed.AArch64.Chain.table P) s fun s' =>
      ChainSt P base size m s₀ s' ∧ TblC P base m (bv P base m s₀) 8 s' := by
  have hn := h.scr.nowrap
  have h8 := slot_mod8 P hL.tbl8
  have hle : ∀ i ≤ 8, P.slot i + 8 * P.M.n ≤ size := fun i hi => by
    have := slot_le P hi; have := hL.tbl; omega_arith
  have hin : ∀ i ≤ 8, P.tbl ≤ P.slot i ∧ P.slot i + 8 * P.M.n ≤ P.tbl + 9 * (8 * P.M.n) :=
    fun i hi => slot_le P hi
  have hb := h.base hL
  rw [VG.Impl.EcKey.Compressed.AArch64.Chain.table]
  refine WP.seq (WP.mono (copy_ok P.M.n h.scr (hle 0 (by decide)) hL.base (h8 0) hL.base8
    ((slot_base hL (i := 0) (by decide)).symm.imp (fun h => by omega_arith) id)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
  have S₁ := h.copy (Or.inr (hin 0 (by decide))) k₁ O₁ hL
  have b₁ := S₁.base hL
  refine WP.seq (WP.mono (mul_ok B S₁.scr S₁.mod hL.mod (hle 8 (Nat.le_refl _)) hL.base hL.base (h8 8) hL.base8
    hL.base8 (by rw [b₁]; exact hB) (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact .inr (.inr (hin 8 (by decide)))
      · exact .inr (.inl rfl)
      · exact .inr (.inl rfl))) fun s₂ ⟨k₂, lt₂, e₂⟩ => ?_)
  have S₂ := S₁.op hL (Or.inr (hin 8 (Nat.le_refl _))) k₂
  have v0 : ∀ {t : State}, Unch base [(P.slot 8, 8 * P.M.n), (P.M.tmp, 8 * P.M.n)] s₁.mem t.mem →
      wordsVal t.mem base (P.slot 0) P.M.n = wordsVal s.mem base P.base P.M.n := fun U => by
    rw [U.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact slot_apart P (by decide)
      · exact slot_tmp hL (by decide)) (by have := hle 0 (by decide); omega_arith), e₁]
  have T₂ : TblC P base m (bv P base m s₀) 1 s₂ := by
    refine ⟨fun i hi => ?_, lt₂, ?_⟩
    · obtain rfl : i = 0 := by omega_arith
      rw [v0 k₂.unch, hb]
      exact ⟨hB, by rw [Nat.mul_zero, Nat.zero_add, Lean.Grind.Semiring.pow_one]⟩
    · rw [toM_mul hm (e₂.trans (by rw [b₁])), Lean.Grind.Semiring.pow_two]
  refine WP.mono (oddPowers_ok (P := P) (N := 7)
    (fun k t => ChainSt P base size m s₀ t ∧ TblC P base m (bv P base m s₀) (k + 1) t)
    (fun k t hk ⟨St, Tt⟩ => ?_) 7 (Nat.le_refl _) s₂ ⟨S₂, T₂⟩) fun t h => h
  have Ti := Tt.1 k (by omega_arith)
  refine WP.mono (mul_ok B St.scr St.mod hL.mod (hle (k + 1) (by omega_arith)) (hle k (by omega_arith))
    (hle 8 (Nat.le_refl _)) (h8 _) (h8 _) (h8 _) Tt.2.1 (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> exact .inr (.inr (hin _ (by omega))))) fun u ⟨ku, ltu, eu⟩ => ?_
  refine ⟨St.op hL (Or.inr (hin (k + 1) (by omega_arith))) ku, ?_⟩
  have e : ∀ j ≤ 8, j ≠ k + 1 →
      wordsVal u.mem base (P.slot j) P.M.n = wordsVal t.mem base (P.slot j) P.M.n := fun j hj hne =>
    ku.unch.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact slot_apart P hne
      · exact slot_tmp hL hj) (by have := hle j hj; omega_arith)
  refine ⟨fun i hi => ?_, by rw [e 8 (Nat.le_refl _) (by omega_arith)]; exact Tt.2.1,
    by rw [e 8 (Nat.le_refl _) (by omega_arith)]; exact Tt.2.2⟩
  rcases Nat.lt_or_ge i (k + 1) with h' | h'
  · rw [e i (by omega_arith) (by omega_arith)]; exact Tt.1 i h'
  · obtain rfl : i = k + 1 := by omega_arith
    refine ⟨ltu, ?_⟩
    rw [toM_mul hm eu, Ti.2, Tt.2.2, ← Lean.Grind.Semiring.pow_add]
    congr 1

/-- `acc = acc^(2^s)`, from `B^v`. -/
theorem squares_ok {P : ChainCfg} {base : Addr} {size m : Nat} [NeZero m] (hL : ChainLay P size) (B : Backend P)
    (hm : UnitMod m (2 ^ (64 * P.M.n))) {s₀ s : State} {v k : Nat} (hs1 : 1 ≤ k) (hs : k < 2 ^ 16)
    (h : ChainSt P base size m s₀ s) (hT : TblC P base m (bv P base m s₀) 8 s)
    (hlt : wordsVal s.mem base P.acc P.M.n < m)
    (hv : toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.acc P.M.n) = bv P base m s₀ ^ v) :
    WP isa (VG.Impl.EcKey.Compressed.AArch64.Chain.squares P k) s fun s' => ChainSt P base size m s₀ s' ∧
      TblC P base m (bv P base m s₀) 8 s' ∧ wordsVal s'.mem base P.acc P.M.n < m ∧
      toM m (2 ^ (64 * P.M.n)) (wordsVal s'.mem base P.acc P.M.n) = bv P base m s₀ ^ (v * 2 ^ k) := by
  have hn := h.scr.nowrap
  rw [VG.Impl.EcKey.Compressed.AArch64.Chain.squares]
  refine WP.seq (WP.mono (setCounter_ok s hs) fun s₁ ⟨c₁, k₁⟩ => ?_)
  have keep₁ : KeepRegs (powClob P.M.n) s s₁ := (Keeps.regs k₁).mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [powClob]
  have S₁ : ChainSt P base size m s₀ s₁ :=
    ⟨h.scr.of_keeps k₁ (by decide), h.keep.trans keep₁, by rw [k₁.mem]; exact h.unch,
      by rw [k₁.mem]; exact h.mod⟩
  refine countLoop_ok (n := k) (by omega_arith) (Inv := fun j t => ChainSt P base size m s₀ t ∧
      TblC P base m (bv P base m s₀) 8 t ∧ t.gpr .x19 = BitVec.ofNat 64 j ∧
      wordsVal t.mem base P.acc P.M.n < m ∧
      toM m (2 ^ (64 * P.M.n)) (wordsVal t.mem base P.acc P.M.n) = bv P base m s₀ ^ (v * 2 ^ (k - j)))
    (fun j t h1 h2 ⟨St, Tt, xt, lt, vt⟩ => ?_) (fun t ⟨St, Tt, _, lt, vt⟩ => ⟨St, Tt, lt, by
      rw [vt, Nat.sub_zero]⟩) hs1
    ⟨S₁, by unfold TblC; rw [k₁.mem]; exact hT, c₁, by rw [k₁.mem]; exact hlt,
      by rw [k₁.mem, hv, Nat.sub_self, Nat.pow_zero, Nat.mul_one]⟩
  refine WP.seq (WP.mono (decCounter_ok t h1 (by omega_arith) xt) fun u ⟨xu, ku⟩ => ?_)
  have Su : ChainSt P base size m s₀ u :=
    ⟨St.scr.of_keeps ku (by decide), St.keep.trans ((Keeps.regs ku).mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp [powClob]), by rw [ku.mem]; exact St.unch,
      by rw [ku.mem]; exact St.mod⟩
  have mu : u.mem = t.mem := ku.mem
  refine WP.mono (mul_ok B Su.scr Su.mod hL.mod hL.acc hL.acc hL.acc hL.acc8 hL.acc8 hL.acc8
    (by rw [mu]; exact lt) (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> exact .inl rfl)) fun w ⟨kw, ltw, ew⟩ => ?_
  have hx : w.gpr .x19 = BitVec.ofNat 64 (j - 1) := by rw [kw.gpr _ (x19_not_clob _), xu]
  have Uw := kw.unch
  rw [mu] at Uw
  refine ⟨⟨Su.op hL (Or.inl rfl) kw, Tt.acc hL hn (Nat.le_refl _) Uw,
    hx, ltw, ?_⟩, hx⟩
  rw [toM_mul hm (ew.trans (by rw [mu])), vt, ← Lean.Grind.Semiring.pow_add]
  congr 1
  rw [← Nat.mul_add, ← Nat.two_mul, show k - (j - 1) = k - j + 1 by omega_arith, Nat.pow_succ]
  grind

/-- A step: `B^v` to `B^(v 2^s + d)`. -/
theorem step_ok {P : ChainCfg} {base : Addr} {size m : Nat} [NeZero m] (hL : ChainLay P size) (B : Backend P)
    (hm : UnitMod m (2 ^ (64 * P.M.n))) {s₀ s : State} {v k d : Nat} (hs : k < 2 ^ 16)
    (hd : d = 0 ∨ (d % 2 = 1 ∧ d ≤ 15))
    (h : ChainSt P base size m s₀ s) (hT : TblC P base m (bv P base m s₀) 8 s)
    (hlt : wordsVal s.mem base P.acc P.M.n < m)
    (hv : toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.acc P.M.n) = bv P base m s₀ ^ v) :
    WP isa (VG.Impl.EcKey.Compressed.AArch64.Chain.step P (k, d)) s fun s' => ChainSt P base size m s₀ s' ∧
      TblC P base m (bv P base m s₀) 8 s' ∧ wordsVal s'.mem base P.acc P.M.n < m ∧
      toM m (2 ^ (64 * P.M.n)) (wordsVal s'.mem base P.acc P.M.n) = bv P base m s₀ ^ (v * 2 ^ k + d) := by
  have hn := h.scr.nowrap
  rw [VG.Impl.EcKey.Compressed.AArch64.Chain.step]
  have hsq : WP isa (if k = 0 then .block [] else VG.Impl.EcKey.Compressed.AArch64.Chain.squares P k) s fun s' =>
      ChainSt P base size m s₀ s' ∧ TblC P base m (bv P base m s₀) 8 s' ∧
      wordsVal s'.mem base P.acc P.M.n < m ∧
      toM m (2 ^ (64 * P.M.n)) (wordsVal s'.mem base P.acc P.M.n) = bv P base m s₀ ^ (v * 2 ^ k) := by
    split
    · rename_i h0; subst h0
      exact WP.block_nil ⟨h, hT, hlt, by rw [hv, Nat.pow_zero, Nat.mul_one]⟩
    · exact squares_ok hL B hm (by omega_arith) hs h hT hlt hv
  refine WP.seq (WP.mono hsq fun s₁ ⟨S₁, T₁, lt₁, v₁⟩ => ?_)
  split
  · rename_i h0; subst h0
    exact WP.block_nil ⟨S₁, T₁, lt₁, by rw [v₁, Nat.add_zero]⟩
  · rename_i h0
    have hd' : d % 2 = 1 ∧ d ≤ 15 := hd.resolve_left h0
    have hi : (d - 1) / 2 < 8 := by omega_arith
    have Ti := T₁.1 _ hi
    refine WP.mono (mul_ok B S₁.scr S₁.mod hL.mod hL.acc hL.acc
      (by have := slot_le P (i := (d - 1) / 2) (by omega_arith); have := hL.tbl; omega_arith) hL.acc8 hL.acc8
      (slot_mod8 P hL.tbl8 _) Ti.1 (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact .inl rfl
        · exact .inl rfl
        · exact .inr (.inr (slot_le P (by omega))))) fun s₂ ⟨k₂, lt₂, e₂⟩ => ?_
    refine ⟨S₁.op hL (Or.inl rfl) k₂, T₁.acc hL hn (Nat.le_refl _) k₂.unch, lt₂, ?_⟩
    rw [toM_mul hm e₂, v₁, Ti.2, ← Lean.Grind.Semiring.pow_add]
    congr 1
    omega_arith

theorem steps_ok {P : ChainCfg} {base : Addr} {size m : Nat} [NeZero m] (hL : ChainLay P size) (B : Backend P)
    (hm : UnitMod m (2 ^ (64 * P.M.n))) {s₀ : State} :
    ∀ (sts : List (Nat × Nat)) {s : State} {v : Nat},
      (∀ st ∈ sts, st.1 < 2 ^ 16 ∧ (st.2 = 0 ∨ (st.2 % 2 = 1 ∧ st.2 ≤ 15))) →
      ChainSt P base size m s₀ s → TblC P base m (bv P base m s₀) 8 s →
      wordsVal s.mem base P.acc P.M.n < m →
      toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.acc P.M.n) = bv P base m s₀ ^ v →
      WP isa (VG.Impl.EcKey.Compressed.AArch64.Chain.steps P sts) s fun s' => ChainSt P base size m s₀ s' ∧
        wordsVal s'.mem base P.acc P.M.n < m ∧
        toM m (2 ^ (64 * P.M.n)) (wordsVal s'.mem base P.acc P.M.n) = bv P base m s₀ ^ chainVal v sts
  | [], _, _, _, h, _, hlt, hv => WP.block_nil ⟨h, hlt, hv⟩
  | (k, d) :: rest, s, v, hst, h, hT, hlt, hv => by
    rw [VG.Impl.EcKey.Compressed.AArch64.Chain.steps]
    have h1 := hst (k, d) (List.mem_cons_self ..)
    exact WP.seq (WP.mono (step_ok hL B hm h1.1 h1.2 h hT hlt hv) fun s₁ ⟨S₁, T₁, lt₁, v₁⟩ =>
      steps_ok hL B hm rest (fun st hs => hst st (List.mem_cons_of_mem _ hs)) S₁ T₁ lt₁ v₁)

/-- `[acc] = [base]^e` in Montgomery form, for the exponent `e` of the chain;
only `powClob` and `chainW` change. -/
theorem chainPow_ok {P : ChainCfg} {base : Addr} {size m e : Nat} [NeZero m] (hL : ChainLay P size) (B : Backend P)
    (hm : UnitMod m (2 ^ (64 * P.M.n))) {s : State} (hs : Scr s base size)
    (hM : ModOkA P.M size m s.mem base) (hB : wordsVal s.mem base P.base P.M.n < m) (hC : ChainOk P e) :
    WP isa (VG.Impl.EcKey.Compressed.AArch64.Chain.pow P) s fun s' => KeepRegs (powClob P.M.n) s s' ∧ Unch base (chainW P) s.mem s'.mem ∧
      wordsVal s'.mem base P.acc P.M.n < m ∧
      toM m (2 ^ (64 * P.M.n)) (wordsVal s'.mem base P.acc P.M.n) =
        toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.base P.M.n) ^ e := by
  have hn := hs.nowrap
  have S₀ : ChainSt P base size m s s := ⟨hs, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Unch.refl _ _ _, hM⟩
  rw [VG.Impl.EcKey.Compressed.AArch64.Chain.pow]
  refine WP.seq (WP.mono (table_ok hL B hm S₀ hB) fun s₁ ⟨S₁, T₁⟩ => ?_)
  have hi : (P.first - 1) / 2 < 8 := by have := hC.first; omega_arith
  have hle := slot_le P (i := (P.first - 1) / 2) (by omega_arith)
  refine WP.seq (WP.mono (copy_ok P.M.n S₁.scr hL.acc (by have := hL.tbl; omega_arith) hL.acc8
    (slot_mod8 P hL.tbl8 _) ((slot_acc hL (i := (P.first - 1) / 2) (by omega_arith)).symm.imp
      (fun h => by omega_arith) id)) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  have S₂ := S₁.copy (Or.inl rfl) k₂ O₂ hL
  have T₂ : TblC P base m (bv P base m s) 8 s₂ :=
    T₁.acc hL hn (Nat.le_refl _) (O₂.unch.mono fun w hw => by simp at hw; simp [hw])
  have Ti := T₁.1 _ hi
  refine WP.mono (steps_ok hL B hm P.steps hC.steps S₂ T₂ (by rw [e₂]; exact Ti.1)
    (v := P.first) (by rw [e₂, Ti.2]; congr 1; have := hC.first; omega_arith)) fun s₃ ⟨S₃, lt₃, v₃⟩ =>
    ⟨S₃.keep, S₃.unch, lt₃, by rw [v₃, hC.val]⟩


end VG.Proof.EcKey.Compressed.AArch64.Chain
