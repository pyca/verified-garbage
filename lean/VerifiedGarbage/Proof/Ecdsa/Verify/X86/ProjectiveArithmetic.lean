import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Final
import VerifiedGarbage.Proof.Ecdsa.Projective

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86 VG.Impl.Ecdsa.Verify.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86 VG.Proof.Ecdh.X86
open VG.Impl.Ecdsa.Verify.X86.Cfg (projectiveOps)
variable {c : VG.Impl.Ecdsa.X86.Cfg}

abbrev projectiveSlots : List Nat := [X, XM, RZ, W, RX, ACC, XN]
abbrev projectiveReads : List Nat := [XM, RZ, RX, ACC]
abbrev projectiveWrites : List Nat := [X, W, XM, X, XN, TMP]

theorem projectiveOps_rename (sl : Nat → Nat) :
    projectiveOps sl = (projectiveOps id).map (FOp.rename sl) := rfl

theorem projectiveOps_run (hc : CfgOk c) (e : Nat → Fe c.C) :
    runOps (projectiveOps c.sl) e (c.sl W) = e (c.sl RX) - e (c.sl XM) * e (c.sl RZ) ∧
    runOps (projectiveOps c.sl) e (c.sl XN) =
      e (c.sl RX) - (e (c.sl XM) + e (c.sl ACC)) * e (c.sl RZ) := by
  have H := runOps_rename c.sl (projectiveOps id) e (fun _ _ _ h => sl_inj c hc.n0 h)
  rw [← projectiveOps_rename] at H
  exact ⟨congrFun H W, congrFun H XN⟩

/-- The five field operations compute both projective differences. -/
theorem projectiveOps_ok (hc : CfgOk c) {s : State} {base : Addr}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hlt : ∀ i ∈ projectiveReads, sv c base s i < c.C.p) :
    WP isa (fprog c.MP' c.wk (projectiveOps c.sl)) s fun t =>
      Scr t base size ∧ t.gpr .esp = s.gpr .esp ∧ Unch base (slWk c projectiveWrites) s.mem t.mem ∧
      sv c base t W < c.C.p ∧ sv c base t XN < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t W) =
        tmv c.C c.n base s (c.sl RX) - tmv c.C c.n base s (c.sl XM) * tmv c.C c.n base s (c.sl RZ) ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t XN) =
        tmv c.C c.n base s (c.sl RX) -
          (tmv c.C c.n base s (c.sl XM) + tmv c.C c.n base s (c.sl ACC)) * tmv c.C c.n base s (c.sl RZ) := by
  have hL : Lay c.MP' size (· ∈ projectiveSlots.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  have hW : WkOk c.MP' size c.wk (· ∈ projectiveSlots.map c.sl) := ⟨wk_le c hc.n10 rfl, fun x hx => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have : ∀ i ∈ projectiveSlots, i < 45 := by decide
      exact sl_below_wk c (this i hi),
    sl_below_wk c (i := MP) (by decide), sl_below_wk c (i := TMP) (by decide)⟩
  have I : Inv c.MP' base size c.C.p (· ∈ projectiveSlots.map c.sl) (projectiveReads.map c.sl)
      (tmv c.C c.n base s) s := by
    refine ⟨hs, hM, ?_, ?_, fun _ _ => rfl⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have sub : ∀ i ∈ projectiveReads, i ∈ projectiveSlots := by decide
      exact List.mem_map_of_mem (sub i hi)
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact hlt i hi
  have reads : readsOk (projectiveOps c.sl) (projectiveReads.map c.sl) = true := by
    rw [projectiveOps_rename]
    exact readsOk_rename c.sl (by decide)
  refine WP.mono (fprog_ok hL hW (unitMod_pow_two hc.p_odd _) _ I ?_ reads)
    fun t ⟨keep, It⟩ => ?_
  · intro op hop x hx
    simp only [projectiveOps, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> exact List.mem_map_of_mem (by decide)
  have w : c.sl W ∈ validAfter (projectiveOps c.sl) (projectiveReads.map c.sl) := by
    simp [mem_validAfter, projectiveOps, FOp.out]
  have xn : c.sl XN ∈ validAfter (projectiveOps c.sl) (projectiveReads.map c.sl) := by
    simp [mem_validAfter, projectiveOps, FOp.out]
  have run := projectiveOps_run hc (tmv c.C c.n base s)
  exact ⟨It.scr, keep.gpr _ (by decide), (by simpa only [progW, projectiveOps, List.map_cons, List.map_nil, FOp.out, List.append_assoc, slWk, slW, projectiveWrites, accLen_MP', MP'_n, show c.MP'.tmp = c.sl TMP from rfl, List.cons_append, List.nil_append] using keep.unch), It.lt _ w, It.lt _ xn, (It.val _ w).trans run.1, (It.val _ xn).trans run.2⟩


abbrev projectivePrepareW : List Nat := [XM, ACC, MN]
abbrev projectiveAllW : List Nat := [XM, ACC, MN, X, W, XN, TMP]

theorem projectivePrepare_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size) :
    WP isa (.block (Impl.Ecdsa.Verify.X86.Cfg.projectivePrepare c)) s fun t =>
      Scr t base size ∧ t.gpr .esp = s.gpr .esp ∧ Unch base (slW c projectivePrepareW) s.mem t.mem ∧
      sv c base t XM = c.R * c.R % c.C.p ∧ sv c base t ACC = c.mont c.C.n ∧
      sv c base t MN = c.C.p - c.C.n := by
  have hp := hc.p_ge
  have hpR := hc.p_lt
  have r2 : c.R * c.R % c.C.p < 2 ^ (64 * c.n) :=
    Nat.lt_trans (Nat.mod_lt _ (by omega)) hpR
  have mont : c.mont c.C.n < 2 ^ (64 * c.n) :=
    Nat.lt_trans (Nat.mod_lt _ (by omega)) hpR
  have sub : c.C.p - c.C.n < 2 ^ (64 * c.n) := by omega
  rw [Impl.Ecdsa.Verify.X86.Cfg.projectivePrepare, List.append_assoc, WP.block_append_iff]
  refine WP.mono (setConst_ok hs (sl_le c hc.n10 (i := XM) (by decide)) r2) fun s₁ ⟨e₁,k₁,O₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (setConst_ok hs₁ (sl_le c hc.n10 (i := ACC) (by decide)) mont) fun s₂ ⟨e₂,k₂,O₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  refine WP.mono (setConst_ok hs₂ (sl_le c hc.n10 (i := MN) (by decide)) sub) fun s₃ ⟨e₃,k₃,O₃⟩ => ?_
  have o : ∀ {s t : State} {j i : Nat}, Outside base (c.sl j) (8 * c.n) s.mem t.mem → i < 45 → i ≠ j →
      sv c base t i = sv c base s i := fun O hi hij => sv_out O hc.n10 hs.nowrap hi hij
  exact ⟨hs₂.of_keeps k₃ (by decide), by rw [k₃.1 _ (by decide), k₂.1 _ (by decide), k₁.1 _ (by decide)], O₁.unch.trans (O₂.unch.trans O₃.unch),
    by rw [o O₃ (by decide) (by decide), o O₂ (by decide) (by decide)]; exact e₁,
    by rw [o O₃ (by decide) (by decide)]; exact e₂, e₃⟩

/-- Prepare constants, convert `r`, and compute both differences. -/
theorem projectiveArithmetic_ok (hc : CfgOk c) {s : State} {base : Addr}
    (hs : Scr s base size) (hmp : sv c base s MP = c.C.p)
    (hrx : sv c base s RX < c.C.p) (hrz : sv c base s RZ < c.C.p) :
    WP isa (.seq (.block (Impl.Ecdsa.Verify.X86.Cfg.projectivePrepare c))
      (.seq (mul c.MP' c.wk (c.sl XM) (c.sl K) (c.sl XM))
        (fprog c.MP' c.wk (projectiveOps c.sl)))) s fun t =>
      Scr t base size ∧ t.gpr .esp = s.gpr .esp ∧ Unch base (slWk c projectiveAllW) s.mem t.mem ∧
      sv c base t MN = c.C.p - c.C.n ∧ sv c base t W < c.C.p ∧ sv c base t XN < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t W) =
        tmv c.C c.n base s (c.sl RX) - Fin.ofNat c.C.p (sv c base s K) * tmv c.C c.n base s (c.sl RZ) ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t XN) =
        tmv c.C c.n base s (c.sl RX) -
          (Fin.ofNat c.C.p (sv c base s K) + Fin.ofNat c.C.p c.C.n) * tmv c.C c.n base s (c.sl RZ) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hp := hc.p_ge
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  refine WP.seq (WP.mono (projectivePrepare_ok hc hs) fun s₁ ⟨hs₁,esp₁,U₁,xm₁,acc₁,mn₁⟩ => ?_)
  have v₁ : ∀ {i}, i < 45 → i ∉ projectivePrepareW → sv c base s₁ i = sv c base s i :=
    fun hi hl => sv_unch U₁ h7 hn hi (apart_slW hl)
  have M₁ : ModOkW c.MP' size c.C.p s₁.mem base := modP_of hc
    ((v₁ (i := MP) (by decide) (by decide)).trans hmp)
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) (.inl rfl) rfl h7 hs₁ M₁ (o := XM) (a := K) (b := XM)
    (by decide) (by decide) (by decide) (by decide) (by rw [xm₁]; exact Nat.mod_lt _ (by omega)))
    fun s₂ ⟨k₂,lt₂,e₂⟩ => ?_)
  have hs₂ := k₂.scr hs₁
  have v₂ : ∀ {i}, i < 45 → i ≠ XM → i ≠ TMP → sv c base s₂ i = sv c base s₁ i :=
    fun hi hio hit => sv_keep (MP'_n c) rfl h7 hn k₂ hi hio hit
  have M₂ := M₁.keepX86 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  have xm₂ : tmv c.C c.n base s₂ (c.sl XM) = Fin.ofNat c.C.p (sv c base s K) := by
    show toM _ _ (sv c base s₂ XM) = _
    rw [toM_r2 (A := sv c base s₁ K) hpR (by rw [e₂, xm₁]; rfl), v₁ (by decide) (by decide)]
  have acc₂ : tmv c.C c.n base s₂ (c.sl ACC) = Fin.ofNat c.C.p c.C.n := by
    show toM _ _ (sv c base s₂ ACC) = _
    rw [v₂ (by decide) (by decide) (by decide), acc₁]
    exact toM_cmont hc _
  have tv₂ : ∀ {i}, i < 45 → i ∉ projectivePrepareW → i ≠ TMP →
      tmv c.C c.n base s₂ (c.sl i) = tmv c.C c.n base s (c.sl i) := fun {i} hi hl ht => by
    show toM _ _ (sv c base s₂ i) = toM _ _ (sv c base s i)
    rw [v₂ hi (fun he => hl (by rw [he]; decide)) ht, v₁ hi hl]
  refine WP.mono (projectiveOps_ok hc hs₂ M₂ (fun i hi => ?_)) fun s₃ ⟨hs₃,esp₃,U₃,wlt,xnlt,wval,xnval⟩ => ?_
  · simp only [projectiveReads, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact lt₂
    · rw [v₂ (by decide) (by decide) (by decide), v₁ (by decide) (by decide)]; exact hrz
    · rw [v₂ (by decide) (by decide) (by decide), v₁ (by decide) (by decide)]; exact hrx
    · rw [v₂ (by decide) (by decide) (by decide), acc₁]; exact Nat.mod_lt _ (by omega)
  have U₂ : Unch base (slWk c [XM, TMP]) s₁.mem s₂.mem := by simpa only [accLen_MP', MP'_n, show c.MP'.tmp = c.sl TMP from rfl, slWk, slW, List.map_cons, List.map_nil, List.cons_append, List.nil_append] using k₂.unch
  have U : Unch base (slWk c projectiveAllW) s.mem s₃.mem :=
    ((U₁.trans U₂).trans U₃).mono (by
      intro w hw
      simp only [slWk, slW, projectivePrepareW, projectiveWrites, projectiveAllW, List.map_cons, List.map_nil,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      rcases hw with ((h | h | h) | ((h | h) | h)) | ((h | h | h | h | h | h) | h) <;> simp [h])
  have mn₃ : sv c base s₃ MN = c.C.p - c.C.n := by
    have kept : sv c base s₃ MN = sv c base s₂ MN :=
      sv_unch U₃ h7 hn (i := MN) (by decide) (apart_slWk (by decide) (by decide))
    rw [kept, v₂ (by decide) (by decide) (by decide), mn₁]
  refine ⟨hs₃, by rw [esp₃, k₂.gpr _ (by decide), esp₁], U,mn₃,wlt,xnlt,?_,?_⟩
  · rw [wval, xm₂, tv₂ (by decide) (by decide) (by decide), tv₂ (by decide) (by decide) (by decide)]
  · rw [xnval, xm₂, acc₂, tv₂ (by decide) (by decide) (by decide), tv₂ (by decide) (by decide) (by decide)]

end VG.Proof.Ecdsa.Verify.X86
