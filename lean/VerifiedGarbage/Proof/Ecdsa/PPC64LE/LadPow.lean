module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
import VerifiedGarbage.Proof.Weierstrass.BytesLen
import VerifiedGarbage.Proof.Weierstrass.Pow
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Copy
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call

/-! ### `Ecdsa.PPC64LE.MulFn`, which this module and modules that import it used -/

section

/-!
# `vg_<curve>_mul` on PPC64LE: correctness

`mulBody` (`Impl/Ecdsa/PPC64LE.lean`) makes the table of the bits of the
number at `K`'s slot, copies `Q` from `R`'s first two slots to `ACC` and
`PT`, sets `R = O` from zero and one, and runs the ladder of `ladderP` from
the point at `ACC`, `PT`, `ONEP` (`ladderAt c ACC PT`). For any invariant `Q`
of the ladder from the point at `RX`, `RY`, `ONEP` (`Step` of `ladderAt c RX
RY`, which the copies carry to the ladder's point) that accepts `O`, `Q 0`
accepts what `R` holds at the end, and the body writes only what the ladder
writes, `ACC`, `PT` and the table of bits (`mulBody_ok`). `mulFn` keeps
`r31` and `lr` past the numbered slots around it (`mulFn_ok`). As on 32-bit
ARM (`Proof/Ecdsa/Arm/Main.lean`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Weierstrass.PPC64LE.Point VG.Spec.Weierstrass

variable {c : Cfg}

/-- What `mulBody` writes besides the ladder: `ACC`, `PT` and the table of
the bits of `k`. -/
abbrev mulBX (c : Cfg) : List (Nat × Nat) := slW c [ACC, PT] ++ [(bitsAt c.n 0, 64 * c.n)]

/-- What `mulBody` writes: the ladder's slots (for any point; `ladWp` does
not depend on it) and `mulBX`. -/
abbrev mulBW (c : Cfg) : List (Nat × Nat) := ladWp (ladderAt c RX RY) ++ mulBX c

/-- `Step` depends only on what the slots of `a`, `3b` and the point hold. -/
theorem step_congr {L L' : LadderCfg} {C : Curve} {base : Addr} {s s' : State} {k : Nat}
    {Q : Nat → Fe C → Fe C → Fe C → Prop} (hb : L'.nbits = L.nbits)
    (ha : tmv C L'.M.n base s' L'.S.a = tmv C L.M.n base s L.S.a)
    (h3 : tmv C L'.M.n base s' L'.S.b3 = tmv C L.M.n base s L.S.b3)
    (hx : tmv C L'.M.n base s' L'.G.x = tmv C L.M.n base s L.G.x)
    (hy : tmv C L'.M.n base s' L'.G.y = tmv C L.M.n base s L.G.y)
    (hz : tmv C L'.M.n base s' L'.G.z = tmv C L.M.n base s L.G.z)
    (h : Step L C base s k Q) : Step L' C base s' k Q := by
  intro j hj X Y Z X2 Y2 Z2 X3 Y3 Z3 hq h2 h3'
  rw [ha, h3] at h2 h3'
  rw [hx, hy, hz] at h3'
  exact h j (hb ▸ hj) X Y Z X2 Y2 Z2 X3 Y3 Z3 hq h2 h3'

/-- A slot's number apart from a slot written at another. -/
theorem sv_outside {base : Addr} {m m' : Mem} {j i : Nat} (h7 : c.n < 10)
    (O : Outside base (c.sl j) (8 * c.n) m m') (hi : i < 45) (hij : i ≠ j) :
    wordsVal m' base (c.sl i) c.n = wordsVal m base (c.sl i) c.n :=
  O.wordsVal (sl_apart c hij) (by have := sl_le c h7 hi; omega_arith)

/-- `[o] = [a]` for numbered slots. -/
theorem copySl_ok (hc : CfgOk c) {s : State} {base : Addr} (hw : WsReg s base) {o a : Nat}
    (ho : o < 45) (ha : a < 45) (hoa : o ≠ a) :
    WP isa (.block (copy c.n (c.sl o) (c.sl a))) s fun s' =>
      sv c base s' o = sv c base s a ∧ Kp [.r4] s s' ∧ Outside base (c.sl o) (8 * c.n) s.mem s'.mem := by
  have := sl_le c hc.n10 ho
  have := sl_le c hc.n10 ha
  exact copy_ok c.n hw.ws hw.at3 (sl_al c o) (sl_al c a) (by omega_arith) (by omega_arith)
    ((sl_apart c hoa).elim (fun h => Or.inl (by omega_arith)) Or.inr)

/-- `mulBody`: for any invariant `Q` of the ladder from the point at `RX`,
`RY`, `ONEP` that accepts `O` (as zero and one hold it), for the scalar at
`K`'s slot, `Q 0` accepts what `R` holds at the end; only `powClob` and
`mulBW` change. -/
theorem mulBody_ok (hc : CfgOk c) (h3 : 3 ≤ c.n) {base : Addr} {s : State} (hw : WsReg s base)
    (hap : sv c base s AP < c.C.p) (hb3 : sv c base s B3P < c.C.p) (hone : sv c base s ONEP < c.C.p)
    (hzero : sv c base s ZERO < c.C.p) (hqx : sv c base s RX < c.C.p) (hqy : sv c base s RY < c.C.p)
    {Q : Nat → Fe c.C → Fe c.C → Fe c.C → Prop}
    (hstep : Step (ladderAt c RX RY) c.C base s (sv c base s K) Q)
    (hO : Q c.ladderCfg.nbits (tmv c.C c.n base s (c.sl ZERO)) (tmv c.C c.n base s (c.sl ONEP))
      (tmv c.C c.n base s (c.sl ZERO))) :
    WP isa c.mulBody s fun s' => Rk powClob s s' ∧ Unch base (mulBW c) s.mem s'.mem ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Q 0 (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY)) (tmv c.C c.n base s' (c.sl RZ)) := by
  have h7 := hc.n10
  have hn := hw.nowrap
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  -- The table of `k`'s bits.
  refine WP.seq (WP.mono (tbl_bits_ok hc hw (i := K) (j := 0) (by decide) (by decide))
    fun s₁ ⟨T₁, K₁, O₁⟩ => ?_)
  obtain hw₁ := hw.of_kp K₁
  obtain e₁ : ∀ {i}, i < 45 → sv c base s₁ i = sv c base s i := fun hi =>
    O₁.wordsVal (Or.inl (sl_below_bits c h7 hi 0 0)) (by have := sl_le c h7 hi; omega_arith)
  -- The copies.
  refine WP.seq ?_
  simp only [List.append_assoc]
  refine wp_append (WP.mono (copySl_ok hc hw₁ (o := ACC) (a := RX) (by decide) (by decide) (by decide))
    fun s₂ ⟨x₂, k₂, O₂⟩ => ?_)
  obtain hw₂ := hw₁.of_kp k₂
  refine wp_append (WP.mono (copySl_ok hc hw₂ (o := PT) (a := RY) (by decide) (by decide) (by decide))
    fun s₃ ⟨x₃, k₃, O₃⟩ => ?_)
  obtain hw₃ := hw₂.of_kp k₃
  refine wp_append (WP.mono (copySl_ok hc hw₃ (o := RX) (a := ZERO) (by decide) (by decide) (by decide))
    fun s₄ ⟨x₄, k₄, O₄⟩ => ?_)
  obtain hw₄ := hw₃.of_kp k₄
  refine wp_append (WP.mono (copySl_ok hc hw₄ (o := RY) (a := ONEP) (by decide) (by decide) (by decide))
    fun s₅ ⟨x₅, k₅, O₅⟩ => ?_)
  obtain hw₅ := hw₄.of_kp k₅
  refine WP.mono (copySl_ok hc hw₅ (o := RZ) (a := ZERO) (by decide) (by decide) (by decide))
    fun s₆ ⟨x₆, k₆, O₆⟩ => ?_
  obtain hw₆ := hw₅.of_kp k₆
  obtain K₁₆ : Rk powClob s s₆ :=
    K₁.rk.trans ((k₂.trans (k₃.trans (k₄.trans (k₅.trans k₆)))).rk)
  obtain o : ∀ {s s' : State} {j i : Nat}, Outside base (c.sl j) (8 * c.n) s.mem s'.mem → i < 45 → i ≠ j →
      sv c base s' i = sv c base s i := fun O hi hij => sv_outside h7 O hi hij
  -- What the copies leave, in terms of `s`.
  obtain e₆ : ∀ {i}, i < 45 → i ∉ [ACC, PT, RX, RY, RZ] → sv c base s₆ i = sv c base s i := fun hi hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hl
    rw [o O₆ hi hl.2.2.2.2, o O₅ hi hl.2.2.2.1, o O₄ hi hl.2.2.1, o O₃ hi hl.2.1, o O₂ hi hl.1, e₁ hi]
  obtain acc₆ : sv c base s₆ ACC = sv c base s RX := by
    rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), o O₄ (by decide) (by decide),
      o O₃ (by decide) (by decide), x₂, e₁ (by decide)]
  obtain pt₆ : sv c base s₆ PT = sv c base s RY := by
    rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), o O₄ (by decide) (by decide), x₃,
      o O₂ (by decide) (by decide), e₁ (by decide)]
  obtain rx₆ : sv c base s₆ RX = sv c base s ZERO := by
    rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), x₄, o O₃ (by decide) (by decide),
      o O₂ (by decide) (by decide), e₁ (by decide)]
  obtain ry₆ : sv c base s₆ RY = sv c base s ONEP := by
    rw [o O₆ (by decide) (by decide), x₅, o O₄ (by decide) (by decide), o O₃ (by decide) (by decide),
      o O₂ (by decide) (by decide), e₁ (by decide)]
  obtain rz₆ : sv c base s₆ RZ = sv c base s ZERO := by
    rw [x₆, o O₅ (by decide) (by decide), o O₄ (by decide) (by decide), o O₃ (by decide) (by decide),
      o O₂ (by decide) (by decide), e₁ (by decide)]
  obtain U₁₆ : Unch base (mulBX c ++ slW c [RX, RY, RZ]) s.mem s₆.mem := by
    have := O₁.unch.trans (O₂.unch.trans (O₃.unch.trans (O₄.unch.trans (O₅.unch.trans O₆.unch))))
    refine this.mono fun w hw => ?_
    simp only [slW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.map_cons,
      List.map_nil] at hw ⊢
    rcases hw with h | h | h | h | h | h <;> simp only [h, true_or, or_true]
  obtain T₆ : ∀ t < 64 * c.n, s₆.mem (off base (bitsAt c.n 0 + t)) =
      if (sv c base s K).testBit t then 1 else 0 := fun t ht => by
    obtain U : Unch base (slW c [ACC, PT, RX, RY, RZ]) s₁.mem s₆.mem := by
      have := O₂.unch.trans (O₃.unch.trans (O₄.unch.trans (O₅.unch.trans O₆.unch)))
      exact this.mono fun w hw => by simpa using hw
    rw [tbl_unch U h7 (j := 0) (by decide) ht (tbl_apart_slW h7 (by decide) 0 t), T₁ t ht]
  obtain tv : ∀ {i j : Nat}, sv c base s₆ i = sv c base s j →
      tmv c.C c.n base s₆ (c.sl i) = tmv c.C c.n base s (c.sl j) := fun h => by
    show toM _ _ (sv c base s₆ _) = toM _ _ (sv c base s _); rw [h]
  obtain hstep₆ : Step (ladderAt c ACC PT) c.C base s₆ (sv c base s K) Q :=
    step_congr (L := ladderAt c RX RY) rfl (tv (e₆ (by decide) (by decide))) (tv (e₆ (by decide) (by decide)))
      (tv acc₆) (tv pt₆) (tv (e₆ (by decide) (by decide))) hstep
  obtain hlt : ∀ x ∈ [(ladderAt c ACC PT).S.a, (ladderAt c ACC PT).S.b3, (ladderAt c ACC PT).G.x,
      (ladderAt c ACC PT).G.y, (ladderAt c ACC PT).G.z, (ladderAt c ACC PT).R.x, (ladderAt c ACC PT).R.y,
      (ladderAt c ACC PT).R.z], wordsVal s₆.mem base x (ladderAt c ACC PT).M.n < c.C.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show sv c base s₆ AP < _; rw [e₆ (by decide) (by decide)]; exact hap
    · show sv c base s₆ B3P < _; rw [e₆ (by decide) (by decide)]; exact hb3
    · show sv c base s₆ ACC < _; rw [acc₆]; exact hqx
    · show sv c base s₆ PT < _; rw [pt₆]; exact hqy
    · show sv c base s₆ ONEP < _; rw [e₆ (by decide) (by decide)]; exact hone
    · show sv c base s₆ RX < _; rw [rx₆]; exact hzero
    · show sv c base s₆ RY < _; rw [ry₆]; exact hone
    · show sv c base s₆ RZ < _; rw [rz₆]; exact hzero
  obtain hR : Q (ladderAt c ACC PT).nbits (tmv c.C c.n base s₆ (ladderAt c ACC PT).R.x)
      (tmv c.C c.n base s₆ (ladderAt c ACC PT).R.y) (tmv c.C c.n base s₆ (ladderAt c ACC PT).R.z) := by
    show Q _ (tmv c.C c.n base s₆ (c.sl RX)) (tmv c.C c.n base s₆ (c.sl RY)) (tmv c.C c.n base s₆ (c.sl RZ))
    rw [tv rx₆, tv ry₆, tv rz₆]; exact hO
  refine WP.mono (ladderP_ok (L := ladderAt c ACC PT) (S := c.SP) hc.fpk hc.fpm (modP hc) hc.p_odd hpR
    (fun h6 => ladPtLay hc h3 h6 (by decide) (by decide))
    (fun _ => ladLayI hc (by decide) (by decide) (by decide) (by decide)) hw₆ hlt nofun hstep₆ hR
    (fun t ht => T₆ t (by have := hc.len_hi; show t < 64 * c.n; change t < 8 * c.C.len at ht; omega_arith)))
    fun s₇ ⟨K₇, U₇, L₇, R₇⟩ => ⟨K₁₆.trans K₇, ?_, L₇, R₇⟩
  refine (U₁₆.trans U₇).mono fun w hw => ?_
  simp only [mulBW, List.mem_append] at hw ⊢
  rcases hw with (hw | hw) | hw
  · exact .inr hw
  · refine .inl ?_
    rw [ladWp_eq]
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨i, (by decide : ∀ i ∈ [RX, RY, RZ], i ∈ ladIx) i hi, rfl⟩))
  · exact .inl hw

/-! ## The function -/

/-- What `vg_<curve>_mul` writes: `mulBW` and where it keeps `r31` and `lr`. -/
abbrev mulFW (c : Cfg) : List (Nat × Nat) := mulBW c ++ [(c.sl nslots, 16)]

/-- The words of `r31` and `lr` lie past the numbered slots, below the field
arithmetic's own working space and the point functions' slots. -/
theorem save_le_own (h7 : c.n < 10) : c.sl 45 + 16 ≤ own c.n := by
  rw [sl_eq, own_eq]; omega_arith

theorem save_le_oAt (h3 : 3 ≤ c.n) (h6 : c.n ≤ 6) : c.sl 45 + 16 ≤ Impl.Weierstrass.Point.oAt c.n := by
  obtain ⟨h1, h2, he, hb3, ha, hq, hp, hoo, -, -⟩ := VG.Proof.Weierstrass.PPC64LE.Point.lay_nums h3 h6
  rw [sl_eq]; omega_arith

/-- The words of `r31` and `lr` are apart from what the body writes. -/
theorem save_apart (h3 : 3 ≤ c.n) (h7 : c.n < 10) {d : Nat} (hd : c.sl 45 ≤ d) (hd' : d + 8 ≤ c.sl 45 + 16) :
    ∀ w ∈ mulBW c, d + 8 ≤ w.1 ∨ w.1 + w.2 ≤ d := by
  intro w hw
  obtain hown := save_le_own (c := c) h7
  simp only [mulBW, mulBX, List.mem_append, ladWp_eq] at hw
  rcases hw with ((hw | hw) | hw) | (hw | hw)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    have := sl_lt c (j := 45) ((by decide : ∀ i ∈ ladIx, i < 45) i hi)
    exact .inr (by dsimp only; omega_arith)
  · rw [List.mem_singleton.mp hw]; exact .inl (by dsimp only; omega_arith)
  · simp only [ptW] at hw
    split at hw
    · rw [List.mem_singleton.mp hw]; exact .inl (by have := save_le_oAt h3 ‹_›; dsimp only; omega_arith)
    · simp at hw
  · simp only [slW, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact .inr (by have := sl_lt c (i := ACC) (j := 45) (by decide); dsimp only; omega_arith)
    · exact .inr (by have := sl_lt c (i := PT) (j := 45) (by decide); dsimp only; omega_arith)
  · rw [List.mem_singleton.mp hw, bitsAt_eq]
    exact .inl (by have := own_eq c.n; dsimp only; omega_arith)

/-- `r31` and `lr` stored past the numbered slots, through `r0`. -/
theorem saves_ok (h7 : c.n < 10) {s : State} {base : Addr} (hw : WsReg s base) :
    WP isa (.block [.store .d .r31 wb c.mulAt31, .mflr .r0, .store .d .r0 wb c.mulAtLr]) s fun s' =>
      Kp [.r0] s s' ∧
        s'.mem = (s.mem.writeW (off base (c.sl 45)) (s.gpr .r31)).writeW (off base (c.sl 45 + 8)) s.lr := by
  obtain hown := save_le_own (c := c) h7
  obtain h45 := sl_eq c 45
  obtain hal : c.sl 45 % 4 = 0 := sl_al c 45
  have hs := hw.ws
  have ha := hw.at3
  refine wp_step (std0_ok hs ha (d := c.sl 45) (by decide) hal (by have := own_eq c.n; omega_arith)) ?_
  refine wp_step exec_mflr ?_
  refine wp_step (std0_ok (d := c.sl 45 + 8) ((hs.store _).write _ _) ((show At { s with mem := _ } base .r3 0 from ha).write _)
    (by decide) (by omega_arith) (by have := own_eq c.n; omega_arith)) (WP.block_nil ⟨?_, ?_⟩)
  · exact ((Kp.store s _ _).trans (Kp.write _ _ (by decide))).trans (Kp.store _ _ _)
  · simp only [write_mem, write_gpr, ite_true]

/-- `lr` and `r31` reloaded from past the numbered slots, through `r0`. -/
theorem loads_ok (h7 : c.n < 10) {s : State} {base : Addr} (hw : WsReg s base) :
    WP isa (.block [.load .d .r0 wb c.mulAtLr, .mtlr .r0, .load .d .r31 wb c.mulAt31]) s fun s' =>
      s'.mem = s.mem ∧ s'.lr = word s.mem base (c.sl 45 + 8) ∧ s'.gpr .r31 = word s.mem base (c.sl 45) ∧
      Rk [.r0, .r31] s s' := by
  obtain hown := save_le_own (c := c) h7
  obtain h45 := sl_eq c 45
  obtain hal : c.sl 45 % 4 = 0 := sl_al c 45
  have hs := hw.ws
  have ha := hw.at3
  refine wp_step (ld0_ok hs ha (d := c.sl 45 + 8) (by decide) (by omega_arith) (by have := own_eq c.n; omega_arith)) ?_
  refine wp_step exec_mtlr ?_
  simp only [write_gpr, ite_true]
  obtain hs₂ : Ws { s.write .r0 (word s.mem base (c.sl 45 + 8)) with lr := word s.mem base (c.sl 45 + 8) } base 8192 :=
    hs.of_wr rfl
  obtain h3₂ : At { s.write .r0 (word s.mem base (c.sl 45 + 8)) with lr := word s.mem base (c.sl 45 + 8) } base .r3 0 :=
    ha.write (d := .r0) (word s.mem base (c.sl 45 + 8))
  refine wp_step (ld0_ok (t := .r31) (d := c.sl 45) hs₂ h3₂ (by decide) hal (by have := own_eq c.n; omega_arith))
    (WP.block_nil ⟨rfl, ?_, ?_, ?_⟩)
  · simp only [write_lr, write_mem]
  · simp only [write_gpr, write_mem, ite_true]
  · refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, hr.1, hr.2, ite_false]

/-- `vg_<curve>_mul`, from the working space at `r3` (`base`), its `8192`
bytes the only memory it may access, and what `mulBody_ok` needs of them:
it returns with the callee-saved registers, `sp` and `lr` kept, `r3` and
every register but `powClob`, having changed only `mulFW`, with `Q 0`
accepting what `R` holds. -/
theorem mulFn_ok (hc : CfgOk c) (h3 : 3 ≤ c.n) {s : State} {base : Addr} (hb : s.gpr .r3 = base)
    (hwr : s.wr = [⟨base, 8192⟩]) (hfit : base.toNat + 8192 ≤ 2 ^ 64)
    (hap : sv c base s AP < c.C.p) (hb3 : sv c base s B3P < c.C.p) (hone : sv c base s ONEP < c.C.p)
    (hzero : sv c base s ZERO < c.C.p) (hqx : sv c base s RX < c.C.p) (hqy : sv c base s RY < c.C.p)
    {Q : Nat → Fe c.C → Fe c.C → Fe c.C → Prop}
    (hstep : Step (ladderAt c RX RY) c.C base s (sv c base s K) Q)
    (hO : Q c.ladderCfg.nbits (tmv c.C c.n base s (c.sl ZERO)) (tmv c.C c.n base s (c.sl ONEP))
      (tmv c.C c.n base s (c.sl ZERO))) :
    WP isa c.mulFn s fun s' => abiPreserved s s' ∧ (∀ r, r ∉ powClob → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Unch base (mulFW c) s.mem s'.mem ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Q 0 (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY)) (tmv c.C c.n base s' (c.sl RZ)) := by
  have h7 := hc.n10
  obtain hown := save_le_own (c := c) h7
  obtain h45 := sl_eq c 45
  obtain hO8 := own_eq c.n
  obtain hw : WsReg s base := ⟨hb, by rw [hwr]; simp, hfit⟩
  have hn := hw.nowrap
  rw [Cfg.mulFn]
  -- `r31` and `lr` saved.
  refine WP.seq (WP.mono (saves_ok h7 hw) fun s₂ ⟨K₂, m₂⟩ => ?_)
  obtain hw₂ := hw.of_kp K₂
  obtain O₂ : Unch base [(c.sl 45, 16)] s.mem s₂.mem := by
    rw [m₂]
    refine ((writeW_outside s.mem base (s.gpr .r31) (d := c.sl 45) (by omega_arith)).unch.trans
      (writeW_outside _ base s.lr (d := c.sl 45 + 8) (by omega_arith)).unch).cover fun w hw => ?_
    refine ⟨(c.sl 45, 16), List.mem_singleton_self _, ?_⟩
    simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with rfl | rfl <;> exact ⟨by dsimp only; omega_arith, by dsimp only; omega_arith⟩
  obtain e₂ : ∀ {i}, i < 45 → sv c base s₂ i = sv c base s i := fun hi =>
    O₂.wordsVal (fun w hw => by
      rw [List.mem_singleton.mp hw]; exact .inl (sl_lt c hi)) (by have := sl_le c h7 hi; omega_arith)
  obtain tv : ∀ {i}, i < 45 → tmv c.C c.n base s₂ (c.sl i) = tmv c.C c.n base s (c.sl i) := fun hi => by
    show toM _ _ (sv c base s₂ _) = toM _ _ (sv c base s _); rw [e₂ hi]
  obtain hstep₂ : Step (ladderAt c RX RY) c.C base s₂ (sv c base s₂ K) Q := by
    rw [e₂ (by decide)]
    exact step_congr rfl (tv (by decide)) (tv (by decide)) (tv (by decide)) (tv (by decide)) (tv (by decide)) hstep
  obtain hO₂ : Q c.ladderCfg.nbits (tmv c.C c.n base s₂ (c.sl ZERO)) (tmv c.C c.n base s₂ (c.sl ONEP))
      (tmv c.C c.n base s₂ (c.sl ZERO)) := by
    rw [tv (by decide), tv (by decide)]; exact hO
  -- The body.
  refine WP.seq (WP.mono (mulBody_ok hc h3 hw₂ (by rw [e₂ (by decide)]; exact hap)
    (by rw [e₂ (by decide)]; exact hb3) (by rw [e₂ (by decide)]; exact hone)
    (by rw [e₂ (by decide)]; exact hzero) (by rw [e₂ (by decide)]; exact hqx)
    (by rw [e₂ (by decide)]; exact hqy) hstep₂ hO₂) fun s₃ ⟨K₃, U₃, L₃, R₃⟩ => ?_)
  obtain hw₃ := hw₂.of_rk K₃
  obtain w31 : word s₃.mem base (c.sl 45) = s.gpr .r31 := by
    rw [U₃.word (save_apart h3 h7 (Nat.le_refl _) (by omega_arith)) (by omega_arith), m₂,
      word_writeW_ne _ (by omega_arith) (by omega_arith) (by omega_arith), word_writeW_self]
  obtain wlr : word s₃.mem base (c.sl 45 + 8) = s.lr := by
    rw [U₃.word (save_apart h3 h7 (by omega_arith) (by omega_arith)) (by omega_arith), m₂, word_writeW_self]
  -- `lr` and `r31` restored.
  refine WP.mono (loads_ok h7 hw₃) fun s₄ ⟨m₄, lr₄, r31₄, K₄⟩ => ?_
  obtain sub₄ : ∀ r ∈ [Reg.r0, .r31], r ∈ powClob := by decide
  obtain sub₂ : ∀ r ∈ [Reg.r0], r ∈ powClob := by decide
  obtain g : ∀ r, r ∉ powClob → s₄.gpr r = s.gpr r := fun r hr => by
    rw [K₄.gpr r (fun h => hr (sub₄ r h)), K₃.gpr r hr, K₂.gpr r (fun h => hr (sub₂ r h))]
  refine ⟨⟨fun r hr => ?_, by rw [K₄.sp, K₃.sp, K₂.sp], by rw [lr₄, wlr]⟩, g,
    by rw [K₄.rd, K₃.rd, K₂.rd], by rw [K₄.wr, K₃.wr, K₂.wr], ?_, by rw [m₄]; exact L₃, ?_⟩
  · by_cases h31 : r = .r31
    · subst h31; rw [r31₄, w31]
    · refine g r fun h => ?_
      simp only [powClob, fnClob, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact h31 rfl | simp [preserved] at hr
  · rw [m₄]
    exact (O₂.trans U₃).mono fun w hw => by
      simp only [List.mem_append, List.mem_singleton] at hw ⊢
      rcases hw with hw | hw
      · exact .inr hw
      · exact .inl hw
  · show Q 0 (toM _ _ (wordsVal s₄.mem _ _ _)) (toM _ _ (wordsVal s₄.mem _ _ _)) (toM _ _ (wordsVal s₄.mem _ _ _))
    rw [m₄]; exact R₃

/-! ## `[k]P`: the call, or the ladder inline -/

/-- What `qMul` writes besides the ladder: `ACC`, `PT` (`vg_<curve>_mul`'s
copy of `Q`), the table of `k`'s bits and where it keeps `r31` and `lr`. -/
abbrev genX (c : Cfg) : List (Nat × Nat) :=
  slW c [ACC, PT] ++ [(bitsAt c.n 0, 64 * c.n), (c.sl nslots, 16)]

theorem apart_genX (h7 : c.n < 10) {i : Nat} (hi : i < 45) (hr : i ∉ [ACC, PT]) :
    ∀ w ∈ genX c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  refine apart_append (apart_slW hr) ?_
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact Or.inl (by have := sl_below_bits c h7 hi 0 0; omega_arith)
  · exact Or.inl (sl_lt c hi)

theorem fixedOk_genX (h7 : c.n < 10) : FixedOk c (genX c) := by
  refine (fixedOk_slW (l := [ACC, PT]) (by decide)).append ?_
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_below_bits c h7 (i := 12) (by decide) 0 0))
  · exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_lt c (i := 12) (j := nslots) (by decide)))

theorem genX_le (h7 : c.n < 10) : ∀ w ∈ genX c, w.1 + w.2 ≤ size := by
  have := sl_le c h7 (i := ACC) (by decide)
  have := sl_le c h7 (i := PT) (by decide)
  have := bitsAt_le c h7 (j := 0) (by decide)
  have := save_le_own (c := c) h7
  have := own_eq c.n
  have hsz : size = 8192 := rfl
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false, List.mem_append, slW, List.map_cons, List.map_nil] at hw
  rcases hw with (rfl | rfl) | rfl | rfl <;> (dsimp only [nslots]; omega_arith)

theorem tbl_apart_genX (h7 : c.n < 10) {j t : Nat} (hj : j ≠ 0) (ht : t < 64 * c.n) :
    ∀ w ∈ genX c, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  have := sl_below_bits c h7 (i := ACC) (by decide) j t
  have := sl_below_bits c h7 (i := PT) (by decide) j t
  have := save_le_own (c := c) h7
  have := own_below_bits c h7 j
  have := bitsAt_eq c j
  have := bitsAt_eq c 0
  obtain hj1 : 1 ≤ j := Nat.pos_of_ne_zero hj
  have : 64 * c.n * 1 ≤ 64 * c.n * j := Nat.mul_le_mul_left _ hj1
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false, List.mem_append, slW, List.map_cons, List.map_nil] at hw
  rcases hw with (rfl | rfl) | rfl | rfl <;> (dsimp only [nslots]; omega_arith)

/-- `R = [k]P` for the point at `gx`, `gy`, `ONEP` (`qMul`): by a call of
`vg_<curve>_mul` if the curve has it, from `k` at `K`'s slot, else by the
ladder inline, from the table of `k`'s bits. For any invariant `Q` of the
ladder from that point that accepts both `R` and `O` (as zero and one hold
it), `Q 0` accepts what `R` holds at the end; only `powClob`, what the
ladder writes and `genX` change. -/
theorem qMul_ok (hc : CfgOk c) (h3 : 3 ≤ c.n) (hnf : ∀ C, c.mul = some C → c.mulFn.noFrames = true)
    {gx gy : Nat} (hgx : gx < 45) (hgy : gy < 45) (hgw : gx ∉ MP :: ladIx) (hgw' : gy ∉ MP :: ladIx)
    {s : State} {base : Addr} (hw : WsReg s base)
    (hap : sv c base s AP < c.C.p) (hb3 : sv c base s B3P < c.C.p) (hone : sv c base s ONEP < c.C.p)
    (hzero : sv c base s ZERO < c.C.p) (hqx : sv c base s gx < c.C.p) (hqy : sv c base s gy < c.C.p)
    (hrx : sv c base s RX < c.C.p) (hry : sv c base s RY < c.C.p) (hrz : sv c base s RZ < c.C.p)
    {k : Nat} {Q : Nat → Fe c.C → Fe c.C → Fe c.C → Prop}
    (hstep : Step (ladderAt c gx gy) c.C base s k Q c.qA0)
    (hR : Q c.ladderCfg.nbits (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))
      (tmv c.C c.n base s (c.sl RZ)))
    (hO : Q c.ladderCfg.nbits (tmv c.C c.n base s (c.sl ZERO)) (tmv c.C c.n base s (c.sl ONEP))
      (tmv c.C c.n base s (c.sl ZERO)))
    (hk : c.mul.isSome → sv c base s K = k)
    (ht : c.mul = none → ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0) :
    WP isa (c.qMul gx gy) s fun s' => Rk powClob s s' ∧
      Unch base (ladWp (ladderAt c gx gy) ++ genX c) s.mem s'.mem ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Q 0 (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY)) (tmv c.C c.n base s' (c.sl RZ)) := by
  have h7 := hc.n10
  have hn := hw.nowrap
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  obtain hgr : gx ≠ RX ∧ gx ≠ RY ∧ gy ≠ RX ∧ gy ≠ RY := by
    refine ⟨fun h => hgw ?_, fun h => hgw ?_, fun h => hgw' ?_, fun h => hgw' ?_⟩ <;> rw [h] <;> decide
  unfold Cfg.qMul
  split
  · -- The call: `Q` copied to `R`'s first two slots.
    next C hC =>
    obtain hq : c.qA0 = false := by simp only [Cfg.qA0, hC, Option.isNone_some, Bool.false_and]
    rw [hq] at hstep
    refine WP.seq ?_
    refine wp_append (WP.mono (copySl_ok hc hw (o := RX) (a := gx) (by decide) hgx (Ne.symm hgr.1))
      fun s₁ ⟨x₁, k₁, O₁⟩ => ?_)
    obtain hw₁ := hw.of_kp k₁
    refine WP.mono (copySl_ok hc hw₁ (o := RY) (a := gy) (by decide) hgy (Ne.symm hgr.2.2.2))
      fun s₂ ⟨x₂, k₂, O₂⟩ => ?_
    obtain hw₂ := hw₁.of_kp k₂
    obtain o : ∀ {s s' : State} {j i : Nat}, Outside base (c.sl j) (8 * c.n) s.mem s'.mem → i < 45 → i ≠ j →
        sv c base s' i = sv c base s i := fun O hi hij => sv_outside h7 O hi hij
    obtain e₂ : ∀ {i}, i < 45 → i ≠ RX → i ≠ RY → sv c base s₂ i = sv c base s i := fun hi h1 h2 =>
      (o O₂ hi h2).trans (o O₁ hi h1)
    obtain rx₂ : sv c base s₂ RX = sv c base s gx := (o O₂ (by decide) (by decide)).trans x₁
    obtain ry₂ : sv c base s₂ RY = sv c base s gy := x₂.trans (o O₁ hgy hgr.2.2.1)
    obtain tv : ∀ {i j}, sv c base s₂ i = sv c base s j →
        tmv c.C c.n base s₂ (c.sl i) = tmv c.C c.n base s (c.sl j) :=
      fun h => by show toM _ _ (sv c base s₂ _) = toM _ _ (sv c base s _); rw [h]
    obtain hstep₂ : Step (ladderAt c RX RY) c.C base s₂ (sv c base s₂ K) Q := by
      rw [e₂ (by decide) (by decide) (by decide), hk (by rw [hC]; rfl)]
      exact step_congr (L := ladderAt c gx gy) rfl (tv (e₂ (by decide) (by decide) (by decide)))
        (tv (e₂ (by decide) (by decide) (by decide))) (tv rx₂) (tv ry₂)
        (tv (e₂ (by decide) (by decide) (by decide))) hstep
    obtain hO₂ : Q c.ladderCfg.nbits (tmv c.C c.n base s₂ (c.sl ZERO)) (tmv c.C c.n base s₂ (c.sl ONEP))
        (tmv c.C c.n base s₂ (c.sl ZERO)) := by
      rw [tv (e₂ (i := ZERO) (by decide) (by decide) (by decide)),
        tv (e₂ (i := ONEP) (by decide) (by decide) (by decide))]
      exact hO
    obtain hcov : Covers [⟨base, 8192⟩] s₂.wr := Covers.of_mem fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hw₂.wr
    obtain g3 : ∀ t : State, (t.callEntry.withRegions [] [⟨base, 8192⟩]).gpr .r3 = t.gpr .r3 := fun t => by
      rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide)]
    refine WP.call (k := ⟨fun t => t.wr = [⟨base, 8192⟩] ∧ t.gpr .r3 = base ∧ t.mem = s₂.mem,
        fun t t' => (∀ r, r ∉ powClob → t'.gpr r = t.gpr r) ∧ Unch base (mulFW c) t.mem t'.mem ∧
          (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal t'.mem base x c.n < c.C.p) ∧
          Q 0 (tmv c.C c.n base t' (c.sl RX)) (tmv c.C c.n base t' (c.sl RY)) (tmv c.C c.n base t' (c.sl RZ)),
        fun _ _ => True⟩)
      (fun t ⟨hwr, h3t, hm⟩ => by
        obtain sv_t : ∀ i, sv c base t i = sv c base s₂ i := fun i => by
          show wordsVal t.mem _ _ _ = wordsVal s₂.mem _ _ _; rw [hm]
        obtain tm_t : ∀ i, tmv c.C c.n base t (c.sl i) = tmv c.C c.n base s₂ (c.sl i) := fun i => by
          show toM _ _ (sv c base t i) = toM _ _ (sv c base s₂ i); rw [sv_t]
        obtain ⟨tr, t', he, A, G, -, -, U, L, R⟩ := mulFn_ok hc h3 h3t hwr hn
          (by rw [sv_t, e₂ (by decide) (by decide) (by decide)]; exact hap)
          (by rw [sv_t, e₂ (by decide) (by decide) (by decide)]; exact hb3)
          (by rw [sv_t, e₂ (by decide) (by decide) (by decide)]; exact hone)
          (by rw [sv_t, e₂ (by decide) (by decide) (by decide)]; exact hzero)
          (by rw [sv_t, rx₂]; exact hqx) (by rw [sv_t, ry₂]; exact hqy)
          (by rw [sv_t]; exact step_congr rfl (tm_t _) (tm_t _) (tm_t _) (tm_t _) (tm_t _) hstep₂)
          (by rw [tm_t, tm_t]; exact hO₂)
        exact ⟨tr, t', he, A, G, U, L, R⟩)
      (rd := []) (wr := [⟨base, 8192⟩])
      ⟨by rw [State.withRegions_wr], by rw [g3, hw₂.r3],
        by rw [State.withRegions_mem, State.callEntry_mem]⟩
      (Covers.right hcov) hcov ?_ (hnf C hC)
    intro s₃ r₃ w₃ p₃ _ _ _ ⟨G, U, L, E⟩
    simp only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr] at G U L E
    obtain K₃ : Rk powClob s s₃ := by
      refine ((k₁.trans k₂).rk).trans ⟨fun r hr => ?_, r₃, w₃, p₃⟩
      obtain sub : ∀ r ∈ linkRegs, r ∈ powClob := by decide
      obtain hl : r ∉ linkRegs := fun h => hr (sub r h)
      rw [G r hr, State.callEntry_gpr _ hl]
    refine ⟨K₃, ?_, L, E⟩
    obtain U₂ : Unch base (slW c [RX, RY]) s.mem s₂.mem := by
      have := O₁.unch.trans O₂.unch
      exact this.mono fun w hw => by simpa using hw
    refine (U₂.trans U).mono fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      refine List.mem_append_left _ ?_
      rw [ladWp_eq]
      exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.mpr ⟨i, (by decide : ∀ i ∈ [RX, RY], i ∈ ladIx) i hi, rfl⟩))
    · rcases List.mem_append.mp hw with hw | hw
      · rcases List.mem_append.mp hw with hw | hw
        · refine List.mem_append_left _ ?_
          rw [ladWp_eq] at hw; rw [ladWp_eq]; exact hw
        · rcases List.mem_append.mp hw with hw | hw
          · exact List.mem_append_right _ (List.mem_append_left _ hw)
          · exact List.mem_append_right _ (List.mem_append_right _ (by rw [List.mem_singleton.mp hw]; simp))
      · exact List.mem_append_right _ (List.mem_append_right _ (by rw [List.mem_singleton.mp hw]; simp [nslots]))
  · -- The ladder inline.
    next hN =>
    obtain hlt : ∀ x ∈ [(ladderAt c gx gy).S.a, (ladderAt c gx gy).S.b3, (ladderAt c gx gy).G.x,
        (ladderAt c gx gy).G.y, (ladderAt c gx gy).G.z, (ladderAt c gx gy).R.x, (ladderAt c gx gy).R.y,
        (ladderAt c gx gy).R.z], wordsVal s.mem base x (ladderAt c gx gy).M.n < c.C.p := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hap
      · exact hb3
      · exact hqx
      · exact hqy
      · exact hone
      · exact hrx
      · exact hry
      · exact hrz
    refine WP.mono (ladderP_ok (L := ladderAt c gx gy) (S := c.SP) hc.fpk hc.fpm (modP hc) hc.p_odd hpR
      (fun h6 => ladPtLay hc h3 h6 hgx hgy) (fun _ => ladLayI hc hgx hgy hgw hgw') hw hlt (fun h => by
        simp only [Cfg.qA0, Bool.and_eq_true, decide_eq_true_eq] at h
        exact h.2.2) hstep hR
      (fun t ht' => ht hN t (by have := hc.len_hi; show t < 64 * c.n; change t < 8 * c.C.len at ht'; omega_arith)))
      fun s' ⟨K, U, L, R⟩ => ⟨K, U.mono fun w hw => List.mem_append_left _ hw, L, R⟩

end VG.Proof.Ecdsa.PPC64LE

end

end

/-!
# ECDSA on PPC64LE: `[k]P` and `Z^(p-2)`

`ladPow_ok`: `[k]P` for the point at two numbered slots (`qMul`: a call of
`vg_<curve>_mul`, or the ladder inline), then `Z^(p-2)` by its addition chain, and
what they keep; `stage₂`: the same after the setup and the tables.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Weierstrass.PPC64LE.Point VG.Spec.Weierstrass

variable {c : Cfg} {A : Args}

/-- What the ladder and the power leave, from `s`: `R` holds `[k]P`, `ACC`
`Z^(p-2)`, and the other slots, the flag and the table of `n - 2` are
unchanged. -/
structure LadPost (c : Cfg) (s₀ : State) (base : Addr) (k : Nat) (P : Point c.C) (s s' : State) : Prop
    extends Keep c s₀ base s' where
  same : ∀ {i}, i < 45 → i ∉ ACC :: PT :: ladIx → sv c base s' i = sv c base s i
  flag : flagW c base s' = flagW c base s
  t₂ : ∀ t < 64 * c.n, s'.mem (off base (bitsAt c.n 2 + t)) = s.mem (off base (bitsAt c.n 2 + t))
  rep : Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
    (tmv c.C c.n base s' (c.sl RZ)) (mul k P)
  rx_lt : sv c base s' RX < c.C.p
  ry_lt : sv c base s' RY < c.C.p
  rz_lt : sv c base s' RZ < c.C.p
  acc_lt : sv c base s' ACC < c.C.p
  acc : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) = tmv c.C c.n base s' (c.sl RZ) ^ (c.C.p - 2)

/-- What a multiplication `R = [k]P` leaves, from `s`: the registers but
`powClob`, memory but what the ladder may write (`ladWp`, for any point) and
`genX`, and `R` reduced and representing `[k]P`. -/
def GeneratorPost (c : Cfg) (base : Addr) (k : Nat) (P : Point c.C) (s t : State) : Prop :=
  Rk powClob s t ∧ Unch base (ladWp (ladderAt c GX GY) ++ genX c) s.mem t.mem ∧
    (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal t.mem base x c.n < c.C.p) ∧
    Rep c.C (tmv c.C c.n base t (c.sl RX)) (tmv c.C c.n base t (c.sl RY)) (tmv c.C c.n base t (c.sl RZ))
      (mul k P)

/-- `R = [k]P` by any `generator` meeting `GeneratorPost`, then `Z^(p-2)`. -/
theorem ladPowWith_ok (hc : CfgOk c) (h3 : 3 ≤ c.n) {s₀ : State} {base : Addr} {s : State}
    (S : Keep c s₀ base s) {k : Nat} {P : Point c.C} {generator : Prog isa}
    (hMul : WP isa generator s (GeneratorPost c base k P s))
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', LadPost c s₀ base k P s s' → WP isa rest s' Q) :
    WP isa (.seq generator (.seq c.invP rest)) s Q := by
  have h7 := hc.n10
  have hn := S.ws.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  refine WP.seq (WP.mono hMul fun s₅ ⟨K₅, U₅, L₅, R₅⟩ => ?_)
  have hW₅ : FixedOk c (ladWp (ladderAt c GX GY) ++ genX c) := (fixedOk_ladWp h3 h7 GX GY).append (fixedOk_genX h7)
  have hWs₅ : ∀ w ∈ ladWp (ladderAt c GX GY) ++ genX c, w.1 + w.2 ≤ size := fun w hw =>
    (List.mem_append.mp hw).elim (ladWp_le h3 h7 GX GY w) (genX_le h7 w)
  have K₅' : Keep c s₀ base s₅ := S.step h7 K₅ (hU := U₅) (hW := hW₅) (hWs := hWs₅)
  have e₅ : ∀ {i}, i < 45 → i ∉ ACC :: PT :: ladIx → sv c base s₅ i = sv c base s i := fun hi hr =>
    sv_unch U₅ h7 hn hi (apart_append (apart_ladWp h3 h7 hi (nmem_of hr (by decide)))
      (apart_genX h7 hi (nmem_of hr (by decide))))
  have tA₅ : ∀ {j t : Nat}, j ≠ 0 → t < 64 * c.n → ∀ w ∈ ladWp (ladderAt c GX GY) ++ genX c,
      bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := fun hj ht w hw =>
    (List.mem_append.mp hw).elim (tbl_apart_ladWp h3 h7 GX GY _ _ w) (tbl_apart_genX h7 hj ht w)
  have lx₅ : sv c base s₅ RX < c.C.p := L₅ _ (List.mem_cons_self ..)
  have ly₅ : sv c base s₅ RY < c.C.p := L₅ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have lz₅ : sv c base s₅ RZ < c.C.p :=
    L₅ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  refine WP.seq (WP.mono (chainPow_ok (P := c.chainP) (S := c.SP) (e := c.C.p - 2) hc.fpk hc.fpm (modP hc)
    (chainLayP hc) hpR K₅'.ws lz₅ hc.chainP) fun s₆ ⟨K₆, U₆, lt₆, v₆⟩ => h s₆ ?_)
  rw [chainWP_eq] at U₆
  have K₆' : Keep c s₀ base s₆ := K₅'.step h7 K₆ (hU := U₆) (hW := fixedOk_chainW h7) (hWs := chainW_le h7)
  have e₆ : ∀ {i}, i < 45 → i ≠ ACC → (i < DX ∨ T2 < i) → sv c base s₆ i = sv c base s₅ i := fun hi hr ht =>
    sv_unch U₆ h7 hn hi (apart_chainW h7 hi hr ht)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  have apF₅ : ∀ w ∈ ladWp (ladderAt c GX GY) ++ genX c, c.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG := fun w hw => by
    rcases apart_append (apart_ladWp h3 h7 (i := FLAG) (gx := GX) (gy := GY) (by decide) (by decide))
      (apart_genX h7 (i := FLAG) (by decide) (by decide)) w hw with h | h
    · exact Or.inl (by omega_arith)
    · exact Or.inr h
  have apF₆ : ∀ w ∈ [(c.sl ACC, 8 * c.n), (c.sl DX, 9 * (8 * c.n)), (own c.n, 64 * c.n)],
      c.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG := fun w hw => by
    rcases apart_chainW h7 (i := FLAG) (by decide) (by decide) (by decide) w hw with h | h
    · exact Or.inl (by omega_arith)
    · exact Or.inr h
  have tR : ∀ i ∈ [RX, RY, RZ], tmv c.C c.n base s₆ (c.sl i) = tmv c.C c.n base s₅ (c.sl i) := by
    intro i hi
    show toM _ _ (sv c base s₆ i) = toM _ _ (sv c base s₅ i)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> rw [e₆ (by decide) (by decide) (by decide)]
  refine ⟨K₆', fun hi hl => ?_, by rw [flagW, U₆.word apF₆ (by omega_arith), U₅.word apF₅ (by omega_arith), ← flagW], ?_,
    by rw [tR RX (by simp), tR RY (by simp), tR RZ (by simp)]; exact R₅,
    by rw [e₆ (by decide) (by decide) (by decide)]; exact lx₅,
    by rw [e₆ (by decide) (by decide) (by decide)]; exact ly₅,
    by rw [e₆ (by decide) (by decide) (by decide)]; exact lz₅, lt₆, ?_⟩
  · rw [e₆ hi (by intro h; subst h; simp at hl)
      ((by decide : ∀ i < 45, i ∉ ACC :: PT :: ladIx → i < DX ∨ T2 < i) _ hi hl), e₅ hi hl]
  · intro t ht
    rw [tbl_unch U₆ h7 (j := 2) (by decide) ht (tbl_apart_chainW h7 2 t),
      tbl_unch U₅ h7 (j := 2) (by decide) ht (tA₅ (by decide) ht)]
  · rw [tR RZ (by simp)]; exact v₆


/-- `[k]P` by `qMul` (the call or the ladder inline), for the point `P` the
slots `gx`, `gy` and `ONEP` represent and the table of bits of any `k` of
`8 len` bits, from `R = O`. -/
theorem qMulPost_ok (hc : CfgOk c) (h3 : 3 ≤ c.n) (hC : Law c.C) {gx gy : Nat} (hgx : gx < 45)
    (hgy : gy < 45) (hgw : gx ∉ MP :: ladIx) (hgw' : gy ∉ MP :: ladIx) {s₀ : State} {base : Addr} {s : State} (S : Keep c s₀ base s) {k : Nat}
    (hkl : k < 2 ^ (8 * c.C.len)) (hrx : sv c base s RX = 0) (hry : sv c base s RY = c.mont 1)
    (hrz : sv c base s RZ = 0) (hk : c.mul.isSome → sv c base s K = k)
    (ht₀ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0)
    {P : Point c.C} (hP : onCurve c.C P = true)
    (hG : Rep c.C (tmv c.C c.n base s (c.sl gx)) (tmv c.C c.n base s (c.sl gy)) (tmv c.C c.n base s (c.sl ONEP)) P)
    (hlx : sv c base s gx < c.C.p) (hly : sv c base s gy < c.C.p) :
    WP isa (c.qMul gx gy) s (GeneratorPost c base k P s) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := S.ws.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have F' := S.fixed
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  have hstep := step_rep' (L := ladderAt c gx gy) (k := k) (a0 := c.qA0) hC hP (by
      show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl AP) c.n) = _
      rw [F'.ap]; exact toM_cmont hc _)
    (by
      show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl B3P) c.n) = _
      rw [F'.b3p]; exact toM_cmont hc _) hG
    (fun h => ⟨by
      simp only [Impl.Ecdsa.PPC64LE.Cfg.qA0, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.2.1]; rfl, by
      show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl ONEP) c.n) = 1
      rw [F'.onep]; exact toM_one (unitMod_pow_two hc.p_odd _)⟩)
  have hR : Rep c.C (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))
      (tmv c.C c.n base s (c.sl RZ)) (mul (k >>> (8 * c.C.len)) P) := by
    show Rep c.C (toM _ _ (sv c base s RX)) (toM _ _ (sv c base s RY)) (toM _ _ (sv c base s RZ)) _
    rw [hrx, hry, hrz, toM_cmont hc, toM_zero, shiftRight_eq_zero hkl, mul_zero_pt]
    exact rep_infinity' hC
  have hz : sv c base s ZERO = 0 := F'.zero
  have hone : sv c base s ONEP = c.mont 1 := by
    rw [show sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p from F'.onep, Cfg.mont, Cfg.R, Nat.one_mul]
  have hO : Rep c.C (tmv c.C c.n base s (c.sl ZERO)) (tmv c.C c.n base s (c.sl ONEP))
      (tmv c.C c.n base s (c.sl ZERO)) (mul (k >>> (8 * c.C.len)) P) := by
    show Rep c.C (toM _ _ (sv c base s ZERO)) (toM _ _ (sv c base s ONEP)) (toM _ _ (sv c base s ZERO)) _
    rw [hz, hone, toM_cmont hc, toM_zero, shiftRight_eq_zero hkl, mul_zero_pt]
    exact rep_infinity' hC
  exact WP.mono (qMul_ok hc h3 hc.mulNf hgx hgy hgw hgw' S.ws
    (lt_of_eq_of_lt F'.ap (hmont _)) (lt_of_eq_of_lt F'.b3p (hmont _)) (by rw [hone]; exact hmont _)
    (by rw [hz]; omega_arith) hlx hly (by rw [hrx]; omega_arith) (by rw [hry]; exact hmont _)
    (by rw [hrz]; omega_arith) hstep hR hO hk fun _ => ht₀) fun s₅ ⟨K₅, U₅, L₅, R₅⟩ =>
    ⟨K₅, U₅, L₅, by rw [Nat.shiftRight_zero] at R₅; exact R₅⟩

/-- `[k]P` by the ladder over the point functions, for the point `P` the
slots `gx`, `gy` and `ONEP` represent and the table of bits of any `k` of
`8 len` bits, from `R = O`, then `Z^(p-2)`. -/
theorem ladPow_ok (hc : CfgOk c) (h3 : 3 ≤ c.n) (hC : Law c.C) {gx gy : Nat} (hgx : gx < 45)
    (hgy : gy < 45) (hgw : gx ∉ MP :: ladIx) (hgw' : gy ∉ MP :: ladIx) {s₀ : State} {base : Addr} {s : State} (S : Keep c s₀ base s) {k : Nat}
    (hkl : k < 2 ^ (8 * c.C.len)) (hrx : sv c base s RX = 0) (hry : sv c base s RY = c.mont 1)
    (hrz : sv c base s RZ = 0) (hk : c.mul.isSome → sv c base s K = k)
    (ht₀ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0)
    {P : Point c.C} (hP : onCurve c.C P = true)
    (hG : Rep c.C (tmv c.C c.n base s (c.sl gx)) (tmv c.C c.n base s (c.sl gy)) (tmv c.C c.n base s (c.sl ONEP)) P)
    (hlx : sv c base s gx < c.C.p) (hly : sv c base s gy < c.C.p)
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', LadPost c s₀ base k P s s' → WP isa rest s' Q) :
    WP isa (.seq (c.qMul gx gy) (.seq c.invP rest)) s Q :=
  ladPowWith_ok hc h3 S (qMulPost_ok hc h3 hC hgx hgy hgw hgw' S hkl hrx hry hrz hk ht₀ hP hG hlx hly) h

/-- `gen`: `R = [k]G`, by the call or the ladder, after the setup and the tables. -/
theorem gen_ok (hc : CfgOk c) (h3 : 3 ≤ c.n) (hC : Law c.C) {s₀ : State} {base : Addr} {F : BitVec 64}
    {s : State} (S : St₁ c A s₀ base F s) : WP isa c.gen s (GeneratorPost c base (kv c A s₀) (G c.C) s) := by
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  have F' := S.fixed
  have hG : Rep c.C (tmv c.C c.n base s (c.sl GX)) (tmv c.C c.n base s (c.sl GY))
      (tmv c.C c.n base s (c.sl ONEP)) (G c.C) := by
    show Rep c.C (toM _ _ (wordsVal s.mem _ (c.sl GX) c.n)) (toM _ _ (wordsVal s.mem _ (c.sl GY) c.n))
      (toM _ _ (wordsVal s.mem _ (c.sl ONEP) c.n)) (G c.C)
    rw [F'.gx, F'.gy, F'.onep, toM_cmont hc, toM_cmont hc, toM_one hpR]
    exact rep_affine' hC _ _
  exact qMulPost_ok hc h3 hC (gx := GX) (gy := GY) (by decide) (by decide) (by decide) (by decide) S.toKeep
    (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (ofBytes_bytesAt_lt _ _ _)) S.rx S.ry S.rz (fun _ => S.k) S.t₀
    hc.onG hG (lt_of_eq_of_lt F'.gx (hmont _)) (lt_of_eq_of_lt F'.gy (hmont _))

/-- `[k]P` and `Z^(p-2)`, after the setup and the tables. -/
theorem stage₂ (hc : CfgOk c) (h3 : 3 ≤ c.n) (hC : Law c.C) {gx gy : Nat} (hgx : gx < 45)
    (hgy : gy < 45) (hgw : gx ∉ MP :: ladIx) (hgw' : gy ∉ MP :: ladIx) {s₀ : State} {base : Addr} {F : BitVec 64} {s : State} (S : St₁ c A s₀ base F s)
    {P : Point c.C} (hP : onCurve c.C P = true)
    (hG : Rep c.C (tmv c.C c.n base s (c.sl gx)) (tmv c.C c.n base s (c.sl gy)) (tmv c.C c.n base s (c.sl ONEP)) P)
    (hlx : sv c base s gx < c.C.p) (hly : sv c base s gy < c.C.p)
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', St₂ c A s₀ base F P s' → WP isa rest s' Q) :
    WP isa (.seq (c.qMul gx gy) (.seq c.invP rest)) s Q :=
  ladPow_ok hc h3 hC hgx hgy hgw hgw' S.toKeep (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (ofBytes_bytesAt_lt _ _ _))
    S.rx S.ry S.rz (fun _ => S.k) S.t₀ hP hG hlx hly fun s' L => h s'
      ⟨L.toKeep, by rw [L.same (by decide) (by decide), S.k], by rw [L.same (by decide) (by decide), S.d],
        by rw [L.same (by decide) (by decide), S.e], by rw [L.flag, S.flag],
        fun t ht => by rw [L.t₂ t ht, S.t₂ t ht], L.rep, L.rx_lt, L.ry_lt, L.rz_lt, L.acc_lt, L.acc⟩

/-- `[k]P` by any `generator` meeting `GeneratorPost`, and `Z^(p-2)`, after
the setup and the tables. -/
theorem stage₂With (hc : CfgOk c) (h3 : 3 ≤ c.n) {s₀ : State} {base : Addr} {F : BitVec 64} {s : State}
    (S : St₁ c A s₀ base F s) {P : Point c.C} {generator : Prog isa}
    (hMul : WP isa generator s (GeneratorPost c base (kv c A s₀) P s))
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', St₂ c A s₀ base F P s' → WP isa rest s' Q) :
    WP isa (.seq generator (.seq c.invP rest)) s Q :=
  ladPowWith_ok hc h3 S.toKeep hMul fun s' L => h s'
      ⟨L.toKeep, by rw [L.same (by decide) (by decide), S.k], by rw [L.same (by decide) (by decide), S.d],
        by rw [L.same (by decide) (by decide), S.e], by rw [L.flag, S.flag],
        fun t ht => by rw [L.t₂ t ht, S.t₂ t ht], L.rep, L.rx_lt, L.ry_lt, L.rz_lt, L.acc_lt, L.acc⟩

end VG.Proof.Ecdsa.PPC64LE
