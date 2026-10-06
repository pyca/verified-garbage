import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Scalars

/-!
# ECDSA verification on 32-bit ARM: `[u]G + [v]Q`

As on x86 (`Proof/Ecdsa/Verify/X86/Points.lean`).

`points_ok`: from what `mid_ok` leaves, the table of `u`'s bits, the
signature's ladder (from `G`), `save` (`[u]G` to `U`, and `R = O`), the
table of `v`'s bits, ECDH's ladder (from the key's point) and `sum` (the
complete addition of `U` and `R`, into `R`), for any invariants of the two
ladders: `R` holds `rcbAdd` of what the two ladders end with. `Main.lean`
gives the invariants of the group law.
-/

namespace VG.Proof.Ecdsa.Verify.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.Arm VG.Proof.Ecdh.Arm
open VG.Proof.X25519.Arm (Rest)
open VG.Impl.Ecdh.Arm (PX PY)
open VG.Impl.Ecdsa.Verify.Arm (SM' EM' RM' UM VM U V UX UY UZ)

variable {c : Cfg}

theorem tbl_le (h7 : c.n < 10) : bitsAt c.n 0 + 64 * c.n ≤ 8192 := bitsAt_le c h7 (j := 0) (by decide)

/-- `[o] = [a]`, on numbered slots. -/
theorem copySl_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size) {o a : Nat}
    (ho : o < 45) (ha : a < 45) (hoa : o ≠ a) :
    WP isa (.block (copy (2 * c.n) (c.sl o) (c.sl a))) s fun s' =>
      sv c base s' o = sv c base s a ∧ Rest [.r4] s s' ∧
      Outside base (c.sl o) (8 * c.n) s.mem s'.mem := by
  have := sl_apart c hoa
  have := sl_le c hc.n10 ho
  have := sl_le c hc.n10 ha
  refine WP.mono (copy_ok (2 * c.n) hs (by omega) (by omega) (by omega)) fun s' ⟨e, k, O⟩ => ⟨?_, k, ?_⟩
  · show wordsVal _ _ _ _ = wordsVal _ _ _ _
    rw [wordsVal_eq_val32, wordsVal_eq_val32, e]
  · rw [show 8 * c.n = 4 * (2 * c.n) by omega]; exact O

/-- `[o] = x`, on numbered slots. -/
theorem setSl_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size) {o x : Nat}
    (ho : o < 45) (hx : x < 2 ^ (64 * c.n)) :
    WP isa (.block (setConst c.n (c.sl o) x)) s fun s' =>
      sv c base s' o = x ∧ Rest [.r4] s s' ∧ Outside base (c.sl o) (8 * c.n) s.mem s'.mem :=
  setConst_ok hs (sl_le c hc.n10 ho) hx

/-- The slots `save` writes. -/
abbrev saveW : List Nat := [UX, UY, UZ, RX, RY, RZ]

theorem save_eq (c : Cfg) : Impl.Ecdsa.Verify.Arm.Cfg.save c =
    copy (2 * c.n) (c.sl UX) (c.sl RX) ++ (copy (2 * c.n) (c.sl UY) (c.sl RY) ++
    (copy (2 * c.n) (c.sl UZ) (c.sl RZ) ++ (setConst c.n (c.sl RX) 0 ++
    (setConst c.n (c.sl RY) (c.mont 1) ++ setConst c.n (c.sl RZ) 0)))) := by
  simp only [Impl.Ecdsa.Verify.Arm.Cfg.save, List.append_assoc]

/-- `U = R`, and `R = O`. -/
theorem save_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size) :
    WP isa (.block (Impl.Ecdsa.Verify.Arm.Cfg.save c)) s fun s' =>
      Scr s' base size ∧ Rest [.r4] s s' ∧ Unch base (slW c saveW) s.mem s'.mem ∧
      sv c base s' UX = sv c base s RX ∧ sv c base s' UY = sv c base s RY ∧
      sv c base s' UZ = sv c base s RZ ∧ sv c base s' RX = 0 ∧ sv c base s' RY = c.mont 1 ∧
      sv c base s' RZ = 0 := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hp := hc.p_lt
  have hp3 := hc.p_ge
  have hm1 : c.mont 1 < 2 ^ (64 * c.n) := by
    have : c.mont 1 < c.C.p := Nat.mod_lt _ (by omega)
    omega
  rw [save_eq]
  refine WP.block_append (WP.mono (copySl_ok hc hs (o := UX) (a := RX) (by decide) (by decide) (by decide))
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
  have hs₁ := hs.of_rest k₁ (by decide)
  refine WP.block_append (WP.mono (copySl_ok hc hs₁ (o := UY) (a := RY) (by decide) (by decide) (by decide))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  have hs₂ := hs₁.of_rest k₂ (by decide)
  refine WP.block_append (WP.mono (copySl_ok hc hs₂ (o := UZ) (a := RZ) (by decide) (by decide) (by decide))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_)
  have hs₃ := hs₂.of_rest k₃ (by decide)
  refine WP.block_append (WP.mono (setSl_ok hc hs₃ (o := RX) (x := 0) (by decide) (Nat.two_pow_pos _))
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_)
  have hs₄ := hs₃.of_rest k₄ (by decide)
  refine WP.block_append (WP.mono (setSl_ok hc hs₄ (o := RY) (by decide) hm1) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_)
  have hs₅ := hs₄.of_rest k₅ (by decide)
  refine WP.mono (setSl_ok hc hs₅ (o := RZ) (x := 0) (by decide) (Nat.two_pow_pos _))
    fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  have o : ∀ {s s' : State} {j i : Nat}, Outside base (c.sl j) (8 * c.n) s.mem s'.mem → i < 45 → i ≠ j →
      sv c base s' i = sv c base s i := fun O hi hij => sv_out O h7 hn hi hij
  refine ⟨hs₅.of_rest k₆ (by decide), k₁.trans (k₂.trans (k₃.trans (k₄.trans (k₅.trans k₆)))), ?_,
    ?_, ?_, ?_, ?_, ?_, e₆⟩
  · have := O₁.unch.trans (O₂.unch.trans (O₃.unch.trans (O₄.unch.trans (O₅.unch.trans O₆.unch))))
    exact this.mono fun w hw => by simpa [saveW] using hw
  · rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), o O₄ (by decide) (by decide),
      o O₃ (by decide) (by decide), o O₂ (by decide) (by decide), e₁]
  · rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), o O₄ (by decide) (by decide),
      o O₃ (by decide) (by decide), e₂, o O₁ (by decide) (by decide)]
  · rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), o O₄ (by decide) (by decide), e₃,
      o O₂ (by decide) (by decide), o O₁ (by decide) (by decide)]
  · rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), e₄]
  · rw [o O₆ (by decide) (by decide), e₅]

/-- The slots `sum` writes. -/
abbrev sumW : List Nat := [T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, RX, RY, RZ]

/-- The slots of the addition. -/
abbrev sumSl : List Nat := [AP, B3P, T0, T1, T2, T3, T4, T5, DX, DY, DZ, UX, UY, UZ, RX, RY, RZ]

/-- The slots it reads. -/
abbrev sumR : List Nat := [AP, B3P, UX, UY, UZ, RX, RY, RZ]

theorem sum_eq (c : Cfg) : Impl.Ecdsa.Verify.Arm.Cfg.sum c =
    .seq (fprog c.MP' c.wk (rcb c.rcbSlots (c.pt UX UY UZ) (c.pt RX RY RZ) (c.pt DX DY DZ)))
      (.block (copy (2 * c.n) (c.sl RX) (c.sl DX) ++ (copy (2 * c.n) (c.sl RY) (c.sl DY) ++
        copy (2 * c.n) (c.sl RZ) (c.sl DZ)))) := by
  simp only [Impl.Ecdsa.Verify.Arm.Cfg.sum, List.append_assoc]

/-- `R = U + R`, by the complete addition. -/
theorem sum_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size)
    (hM : ModOkW c.MP' size c.C.p s.mem base) (hlt : ∀ i ∈ sumR, sv c base s i < c.C.p) :
    WP isa (Impl.Ecdsa.Verify.Arm.Cfg.sum c) s fun s' =>
      Scr s' base size ∧ Rest clob s s' ∧ Unch base (slWk c sumW) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem base ∧ sv c base s' RZ < c.C.p ∧
      (tmv c.C c.n base s' (c.sl RX), tmv c.C c.n base s' (c.sl RY), tmv c.C c.n base s' (c.sl RZ)) =
        rcbAdd (tmv c.C c.n base s (c.sl AP)) (tmv c.C c.n base s (c.sl B3P))
          (tmv c.C c.n base s (c.sl UX)) (tmv c.C c.n base s (c.sl UY)) (tmv c.C c.n base s (c.sl UZ))
          (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY)) (tmv c.C c.n base s (c.sl RZ)) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hL : Lay c.MP' size (· ∈ sumSl.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  have hW : WkOk c.MP' size c.wk (· ∈ sumSl.map c.sl) := ⟨wk_le c h7 rfl, fun x hx => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have : ∀ i ∈ sumSl, i < 45 := by decide
      exact sl_below_wk c (this i hi),
    sl_below_wk c (i := MP) (by decide), sl_below_wk c (i := TMP) (by decide)⟩
  have hA : RcbApart c.rcbSlots (c.pt UX UY UZ) (c.pt RX RY RZ) (c.pt DX DY DZ) :=
    rcbApart_of h0 (lw := [T0, T1, T2, T3, T4, T5, DX, DY, DZ]) (lr := sumR) rfl rfl (by decide)
      (by decide)
  have hI : Inv c.MP' base size c.C.p (· ∈ sumSl.map c.sl) (sumR.map c.sl)
      (fun x => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base x c.n)) s := by
    refine ⟨hs, hM, fun x hx => ?_, fun x hx => ?_, fun _ _ => rfl⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have sub : ∀ i ∈ sumR, i ∈ sumSl := by decide
      exact List.mem_map_of_mem (sub i hi)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact hlt i hi
  rw [sum_eq]
  refine WP.seq (WP.mono (rcb_ok hL hW hpR hA (fun x hx => ?_) hI (fun x hx => hx))
    fun s₁ ⟨PK, I₁, t₁, _⟩ => ?_)
  · rw [show rcbW c.rcbSlots (c.pt DX DY DZ) ++ rcbR c.rcbSlots (c.pt UX UY UZ) (c.pt RX RY RZ) =
      ([T0, T1, T2, T3, T4, T5, DX, DY, DZ] ++ sumR).map c.sl from rfl] at hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have sub : ∀ i ∈ [T0, T1, T2, T3, T4, T5, DX, DY, DZ] ++ sumR, i ∈ sumSl := by decide
    exact List.mem_map_of_mem (sub i hi)
  have hs₁ := I₁.scr
  have hD : ∀ i ∈ [DX, DY, DZ], c.sl i ∈ rcbW c.rcbSlots (c.pt DX DY DZ) ++ sumR.map c.sl := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> simp [rcbW, Cfg.pt]
  refine WP.block_append (WP.mono (copySl_ok hc hs₁ (o := RX) (a := DX) (by decide) (by decide) (by decide))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  have hs₂ := hs₁.of_rest k₂ (by decide)
  refine WP.block_append (WP.mono (copySl_ok hc hs₂ (o := RY) (a := DY) (by decide) (by decide) (by decide))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_)
  have hs₃ := hs₂.of_rest k₃ (by decide)
  refine WP.mono (copySl_ok hc hs₃ (o := RZ) (a := DZ) (by decide) (by decide) (by decide))
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have o : ∀ {s s' : State} {j i : Nat}, Outside base (c.sl j) (8 * c.n) s.mem s'.mem → i < 45 → i ≠ j →
      sv c base s' i = sv c base s i := fun O hi hij => sv_out O h7 hn hi hij
  have x₄ : sv c base s₄ RX = sv c base s₁ DX := by
    rw [o O₄ (by decide) (by decide), o O₃ (by decide) (by decide), e₂]
  have y₄ : sv c base s₄ RY = sv c base s₁ DY := by
    rw [o O₄ (by decide) (by decide), e₃, o O₂ (by decide) (by decide)]
  have z₄ : sv c base s₄ RZ = sv c base s₁ DZ := by
    rw [e₄, o O₃ (by decide) (by decide), o O₂ (by decide) (by decide)]
  have K₄ : Rest [.r4] s₁ s₄ := k₂.trans (k₃.trans k₄)
  have U₄ : Unch base (slWk c sumW) s.mem s₄.mem := by
    have := ((Outs.unch PK.mem).trans (O₂.unch.trans (O₃.unch.trans O₄.unch)))
    refine this.mono fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw
    · simp only [progW, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with ⟨y, hy, rfl⟩ | hw | hw
      · simp only [rcbW, Cfg.rcbSlots, Cfg.pt, List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [MP'_n]
      · subst hw; simp [MP'_n, MP'_tmp]
      · subst hw; exact List.mem_append_right _ (by rw [accLen_MP']; exact List.mem_singleton_self _)
    · simp only [List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | hw | hw <;> (subst hw; simp)
  refine ⟨hs₃.of_rest k₄ (by decide), PK.rest.trans (K₄.mono (by decide)), U₄, ?_, ?_, ?_⟩
  · have hM₁ := I₁.mod
    refine ⟨hM₁.n0, hM₁.mo, hM₁.tmp, hM₁.sep, ?_, hM₁.inv, hM₁.red⟩
    rw [U₄.wordsVal (fun w hw => ?_) (by have := hM₁.mo; omega)]
    · exact hM.val
    · exact apart_slWk (c := c) (i := MP) (by decide) (by decide) w hw
  · rw [z₄]; exact I₁.lt _ (hD DZ (by simp))
  · have vx := I₁.val _ (hD DX (by simp))
    have vy := I₁.val _ (hD DY (by simp))
    have vz := I₁.val _ (hD DZ (by simp))
    show (toM _ _ (sv c base s₄ RX), toM _ _ (sv c base s₄ RY), toM _ _ (sv c base s₄ RZ)) = _
    rw [x₄, y₄, z₄]
    exact (congrArg₂ Prod.mk vx (congrArg₂ Prod.mk vy vz)).trans t₁

/-- `Step` depends only on what the slots of `a`, `3b` and `G` stand for. -/
theorem Step.congr {L : LadderCfg} {C : Curve} {base : Addr} {s s' : State} {k : Nat}
    {Q : Nat → Fe C → Fe C → Fe C → Prop} (h : Step L C base s k Q)
    (ha : tmv C L.M.n base s' L.S.a = tmv C L.M.n base s L.S.a)
    (hb : tmv C L.M.n base s' L.S.b3 = tmv C L.M.n base s L.S.b3)
    (hx : tmv C L.M.n base s' L.G.x = tmv C L.M.n base s L.G.x)
    (hy : tmv C L.M.n base s' L.G.y = tmv C L.M.n base s L.G.y)
    (hz : tmv C L.M.n base s' L.G.z = tmv C L.M.n base s L.G.z) : Step L C base s' k Q := by
  intro j hj X Y Z X2 Y2 Z2 X3 Y3 Z3 hq h2 h3
  rw [ha, hb] at h2
  rw [ha, hb, hx, hy, hz] at h3
  exact h j hj X Y Z X2 Y2 Z2 X3 Y3 Z3 hq h2 h3

/-- After `[u]G + [v]Q`, for the invariants `Q₁` of the signature's ladder
and `Q₂` of ECDH's: `R` holds the complete addition of what they end with. -/
structure Pts (c : Cfg) (s₀ : State) (base : Addr)
    (Q₁ Q₂ : Nat → Fe c.C → Fe c.C → Fe c.C → Prop) (s : State) : Prop where
  scr : Scr s base size
  far : Far s base 8192
  rest : Rest (.lr :: work) s₀ s
  fixed : Fixed c base s₀.gpr s.mem
  t₁ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) = if (c.C.p - 2).testBit t then 1 else 0
  flag : flagW c base s =
    mask32 (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n))
  rm_lt : sv c base s RM' < c.C.n
  rm : toM c.C.n (2 ^ (64 * c.n)) (sv c base s RM') = Fin.ofNat c.C.n (sigR c s₀)
  rz_lt : sv c base s RZ < c.C.p
  pt : ∃ X1 Y1 Z1 X2 Y2 Z2 : Fe c.C, Q₁ 0 X1 Y1 Z1 ∧ Q₂ 0 X2 Y2 Z2 ∧
    (tmv c.C c.n base s (c.sl RX), tmv c.C c.n base s (c.sl RY), tmv c.C c.n base s (c.sl RZ)) =
      rcbAdd (Fin.ofNat c.C.p c.C.a) (Fin.ofNat c.C.p (3 * c.C.b)) X1 Y1 Z1 X2 Y2 Z2
  unch : Unch base [(0, 8192)] s₀.mem s.mem

theorem points_eq (c : Cfg) : Impl.Ecdsa.Verify.Arm.Cfg.points c =
    .seq (bits (c.sl U) (bitsAt c.n 0) (8 * c.n)) (.seq (ladder c.ladderCfg c.wk)
      (.seq (.block (Impl.Ecdsa.Verify.Arm.Cfg.save c)) (.seq (bits (c.sl V) (bitsAt c.n 0) (8 * c.n))
      (.seq (ladder (Impl.Ecdh.Arm.Cfg.ladderQ c) c.wk) (Impl.Ecdsa.Verify.Arm.Cfg.sum c))))) := rfl

/-- The slots the two ladders and `save` write. -/
abbrev ptsW : List Nat :=
  [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TX, TY, TZ, TMP, UX, UY, UZ]

/-- `[u]G + [v]Q`, into `R`. -/
theorem points_ok (hc : CfgOk c) {s₀ : State} {base : Addr} {s : State}
    (hM : Mid c s₀ base s) {Q₁ Q₂ : Nat → Fe c.C → Fe c.C → Fe c.C → Prop}
    (hstep₁ : Step c.ladderCfg c.C base s (sv c base s U) Q₁) (hO₁ : Q₁ (64 * c.n) 0 1 0)
    (hstep₂ : Step (Impl.Ecdh.Arm.Cfg.ladderQ c) c.C base s (sv c base s V) Q₂)
    (hO₂ : Q₂ (64 * c.n) 0 1 0) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', Pts c s₀ base Q₁ Q₂ s' → WP isa rest s' Q) :
    WP isa (.seq (Impl.Ecdsa.Verify.Arm.Cfg.points c) rest) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hM.scr.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have F := hM.fixed
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  have henc : encodable (BitVec.ofNat 32 (64 * c.n)) = true := by
    have : ∀ n < 10, encodable (BitVec.ofNat 32 (64 * n)) = true := by decide
    exact this _ h7
  have tb : ∀ {i}, i < 45 → ∀ w ∈ [(bitsAt c.n 0, 64 * c.n)], c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
    fun hi => apart_tbl hi 0
  rw [points_eq]
  refine WP.seq ?_
  -- The table of `u`.
  refine WP.seq (WP.mono (tbl_bits_ok hc hM.scr hM.far (i := U) (j := 0) (by decide) (by decide))
    fun s₁ ⟨b₁, k₁, O₁⟩ => ?_)
  have hs₁ := hM.scr.of_rest k₁ (by decide)
  have hf₁ := hM.far.of_rest k₁
  have U₁ : Unch base [(bitsAt c.n 0, 64 * c.n)] s.mem s₁.mem := O₁.unch
  have F₁ := F.unch h7 hn (fixedOk_tbl 0) U₁
  have v₁ : ∀ {i}, i < 45 → sv c base s₁ i = sv c base s i := fun hi => sv_unch U₁ h7 hn hi (tb hi)
  -- `[u]G`.
  have hlt₁ : ∀ x ∈ ladR c.ladderCfg, wordsVal s₁.mem base x c.MP'.n < c.C.p := by
    intro x hx
    have hx' : x ∈ [AP, B3P, GX, GY, ONEP, RX, RY, RZ].map c.sl := hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    show sv c base s₁ i < c.C.p
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt F₁.ap (hmont _)
    · exact lt_of_eq_of_lt F₁.b3p (hmont _)
    · exact lt_of_eq_of_lt F₁.gx (hmont _)
    · exact lt_of_eq_of_lt F₁.gy (hmont _)
    · exact lt_of_eq_of_lt F₁.onep (Nat.mod_lt _ (by omega))
    · rw [v₁ (by decide), hM.rx]; omega
    · rw [v₁ (by decide), hM.ry]; exact hmont _
    · rw [v₁ (by decide), hM.rz]; omega
  have tv₁ : ∀ {i}, i < 45 → tmv c.C c.n base s₁ (c.sl i) = tmv c.C c.n base s (c.sl i) := fun hi => by
    show toM _ _ (sv c base s₁ _) = toM _ _ (sv c base s _)
    rw [v₁ hi]
  have hR₁ : Q₁ c.ladderCfg.nbits (tmv c.C c.n base s₁ (c.sl RX)) (tmv c.C c.n base s₁ (c.sl RY))
      (tmv c.C c.n base s₁ (c.sl RZ)) := by
    show Q₁ (64 * c.n) (toM _ _ (sv c base s₁ RX)) (toM _ _ (sv c base s₁ RY)) (toM _ _ (sv c base s₁ RZ))
    rw [v₁ (by decide), v₁ (by decide), v₁ (by decide), hM.rx, hM.ry, hM.rz, toM_cmont hc, toM_zero]
    exact hO₁
  refine WP.seq (WP.mono (ladder_ok (ladLay hc) (ladWk hc) hpR (bitsAt_lt hc (j := 0) (by decide)) hs₁ hf₁
    (modP_of hc F₁.mp) hlt₁
    (Step.congr hstep₁ (tv₁ (by decide)) (tv₁ (by decide)) (tv₁ (by decide)) (tv₁ (by decide))
      (tv₁ (by decide))) hR₁ (fun t ht => by
        show s₁.mem (off base (bitsAt c.n 0 + t)) = _
        rw [b₁ t ht]) henc)
    fun s₂ ⟨K₂, U₂, M₂, L₂, q₂⟩ => ?_)
  rw [ladWx_eq, accLen_MP'] at U₂
  have hs₂ := hs₁.of_rest K₂ (by decide)
  have F₂ := F₁.unch h7 hn (fixedOk_slWk (by decide)) U₂
  -- `U = [u]G`, `R = O`.
  refine WP.seq (WP.mono (save_ok hc hs₂) fun s₃ ⟨hs₃, k₃, U₃, ux₃, uy₃, uz₃, rx₃, ry₃, rz₃⟩ => ?_)
  have F₃ := F₂.unch h7 hn (fixedOk_slW (by decide)) U₃
  -- The table of `v`.
  have sub₂ : ∀ i ∈ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ,
      TMP], i ∈ ptsW := by decide
  have sub₃ : ∀ i ∈ saveW, i ∈ ptsW := by decide
  have W₃ : ∀ {i}, i < 45 → i ∉ ptsW → sv c base s₃ i = sv c base s i := fun hi hl =>
    ((sv_unch U₃ h7 hn hi (apart_slW (fun h => hl (sub₃ _ h)))).trans
      (sv_unch U₂ h7 hn hi (apart_slWk hi (fun h => hl (sub₂ _ h))))).trans (v₁ hi)
  have hf₃ := (hf₁.of_rest K₂).of_rest k₃
  refine WP.seq (WP.mono (tbl_bits_ok hc hs₃ hf₃ (i := V) (j := 0) (by decide) (by decide))
    fun s₄ ⟨b₄, k₄, O₄⟩ => ?_)
  have hs₄ := hs₃.of_rest k₄ (by decide)
  have hf₄ := hf₃.of_rest k₄
  have U₄ : Unch base [(bitsAt c.n 0, 64 * c.n)] s₃.mem s₄.mem := O₄.unch
  have F₄ := F₃.unch h7 hn (fixedOk_tbl 0) U₄
  have v₄ : ∀ {i}, i < 45 → sv c base s₄ i = sv c base s₃ i := fun hi => sv_unch U₄ h7 hn hi (tb hi)
  -- `[v]Q`.
  have hlt₄ : ∀ x ∈ ladR (Impl.Ecdh.Arm.Cfg.ladderQ c), wordsVal s₄.mem base x c.MP'.n < c.C.p := by
    intro x hx
    have hx' : x ∈ [AP, B3P, PX, PY, ONEP, RX, RY, RZ].map c.sl := hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    show sv c base s₄ i < c.C.p
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt F₄.ap (hmont _)
    · exact lt_of_eq_of_lt F₄.b3p (hmont _)
    · rw [v₄ (by decide), W₃ (by decide) (by decide)]; exact hM.px_lt
    · rw [v₄ (by decide), W₃ (by decide) (by decide)]; exact hM.py_lt
    · exact lt_of_eq_of_lt F₄.onep (Nat.mod_lt _ (by omega))
    · rw [v₄ (by decide), rx₃]; omega
    · rw [v₄ (by decide), ry₃]; exact hmont _
    · rw [v₄ (by decide), rz₃]; omega
  have tv₄ : ∀ {i}, i < 45 → i ∉ ptsW → tmv c.C c.n base s₄ (c.sl i) = tmv c.C c.n base s (c.sl i) :=
    fun hi hl => by
      show toM _ _ (sv c base s₄ _) = toM _ _ (sv c base s _)
      rw [v₄ hi, W₃ hi hl]
  have hR₄ : Q₂ (Impl.Ecdh.Arm.Cfg.ladderQ c).nbits (tmv c.C c.n base s₄ (c.sl RX))
      (tmv c.C c.n base s₄ (c.sl RY)) (tmv c.C c.n base s₄ (c.sl RZ)) := by
    show Q₂ (64 * c.n) (toM _ _ (sv c base s₄ RX)) (toM _ _ (sv c base s₄ RY)) (toM _ _ (sv c base s₄ RZ))
    rw [v₄ (by decide), v₄ (by decide), v₄ (by decide), rx₃, ry₃, rz₃, toM_cmont hc, toM_zero]
    exact hO₂
  refine WP.seq (WP.mono (ladder_ok (ladLayQ hc) (ladWkQ hc) hpR (bitsAt_lt hc (j := 0) (by decide)) hs₄ hf₄
    (modP_of hc F₄.mp) hlt₄
    (Step.congr hstep₂ (tv₄ (by decide) (by decide)) (tv₄ (by decide) (by decide))
      (tv₄ (by decide) (by decide)) (tv₄ (by decide) (by decide)) (tv₄ (by decide) (by decide))) hR₄
      (fun t ht => by
        show s₄.mem (off base (bitsAt c.n 0 + t)) = _
        rw [b₄ t ht, show wordsVal s₃.mem base (c.sl V) c.n = sv c base s V from
          W₃ (by decide) (by decide)]) henc)
    fun s₅ ⟨K₅, U₅, M₅, L₅, q₅⟩ => ?_)
  rw [ladWxQ_eq, accLen_MP'] at U₅
  have hs₅ := hs₄.of_rest K₅ (by decide)
  have F₅ := F₄.unch h7 hn (fixedOk_slWk (by decide)) U₅
  have v₅ : ∀ {i}, i < 45 → i ∉ ptsW → sv c base s₅ i = sv c base s₄ i := fun hi hl =>
    sv_unch U₅ h7 hn hi (apart_slWk hi (fun h => hl (sub₂ _ h)))
  -- The sum.
  have u₅ : ∀ {i}, i ∈ [UX, UY, UZ] → sv c base s₅ i = sv c base s₃ i := fun {i} hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
      exact (sv_unch U₅ h7 hn (by decide) (apart_slWk (by decide) (by decide))).trans (v₄ (by decide))
  refine WP.mono (sum_ok hc hs₅ M₅ (fun i hi => ?_)) fun s₆ ⟨hs₆, g₆, U₆, M₆, rz₆, t₆⟩ => h s₆ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt F₅.ap (hmont _)
    · exact lt_of_eq_of_lt F₅.b3p (hmont _)
    · rw [u₅ (by decide), ux₃]; exact L₂ _ (List.mem_cons_self ..)
    · rw [u₅ (by decide), uy₃]; exact L₂ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · rw [u₅ (by decide), uz₃]
      exact L₂ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    · exact L₅ _ (List.mem_cons_self ..)
    · exact L₅ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · exact L₅ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have F₆ := F₅.unch h7 hn (fixedOk_slWk (by decide)) U₆
  have sub₆ : ∀ i ∈ sumW, i ∈ ptsW := by decide
  have UW : Unch base ([(bitsAt c.n 0, 64 * c.n)] ++ slWk c ptsW) s.mem s₆.mem := by
    have hsl : ∀ {l : List Nat}, (∀ i ∈ l, i ∈ ptsW) → ∀ w ∈ slWk c l,
        w ∈ [(bitsAt c.n 0, 64 * c.n)] ++ slWk c ptsW := fun hl w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
        exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem (hl i hi)))
      · exact List.mem_append_right _ (List.mem_append_right _ hw)
    refine (U₁.trans (U₂.trans (U₃.trans (U₄.trans (U₅.trans U₆))))).mono fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw
    · exact List.mem_append_left _ hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hsl sub₂ w hw
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem (sub₃ i hi)))
    rcases List.mem_append.mp hw with hw | hw
    · exact List.mem_append_left _ hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hsl sub₂ w hw
    · exact hsl sub₆ w hw
  have tu : ∀ {i j}, i ∈ [UX, UY, UZ] → j ∈ [RX, RY, RZ] → sv c base s₃ i = sv c base s₂ j →
      tmv c.C c.n base s₅ (c.sl i) = tmv c.C c.n base s₂ (c.sl j) := fun hi _ e => by
    show toM _ _ (sv c base s₅ _) = toM _ _ (sv c base s₂ _)
    rw [u₅ hi, e]
  have tR₅ : ∀ {i}, i ∈ [AP, B3P] → tmv c.C c.n base s₅ (c.sl i) = tmv c.C c.n base s (c.sl i) :=
    fun {i} hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      show toM _ _ (sv c base s₅ _) = toM _ _ (sv c base s _)
      rcases hi with rfl | rfl <;> rw [v₅ (by decide) (by decide), v₄ (by decide), W₃ (by decide) (by decide)]
  have ha : tmv c.C c.n base s (c.sl AP) = Fin.ofNat c.C.p c.C.a := by
    show toM _ _ (wordsVal s.mem base (c.sl AP) c.n) = _
    rw [F.ap]; exact toM_cmont hc _
  have hb : tmv c.C c.n base s (c.sl B3P) = Fin.ofNat c.C.p (3 * c.C.b) := by
    show toM _ _ (wordsVal s.mem base (c.sl B3P) c.n) = _
    rw [F.b3p]; exact toM_cmont hc _
  have hFl := sl_le c h7 (i := FLAG) (by decide)
  have apF : ∀ w ∈ [(bitsAt c.n 0, 64 * c.n)] ++ slWk c ptsW, c.sl FLAG + 4 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG := by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · rw [List.mem_singleton.mp hw]
      have := sl_below_bits c (i := FLAG) (by decide) 0 0
      exact Or.inl (by dsimp only; omega)
    · rcases apart_slWk (c := c) (i := FLAG) (by decide) (by decide) w hw with h | h
      · exact Or.inl (by omega)
      · exact Or.inr h
  have rm₆ : sv c base s₆ RM' = sv c base s RM' :=
    sv_unch UW h7 hn (by decide) (apart_append (tb (by decide)) (apart_slWk (by decide) (by decide)))
  have Kw : Rest work s s₆ := (k₁.mono (by decide)).trans ((K₂.mono powClob_work).trans ((k₃.mono (by decide)).trans
    ((k₄.mono (by decide)).trans ((K₅.mono powClob_work).trans (g₆.mono clob_work)))))
  refine ⟨hs₆, hM.far.of_rest Kw, hM.rest.trans (Kw.mono (by simp)), F₆, fun t ht => ?_,
    by rw [flagW, Unch.readW32 UW apF (by omega), ← flagW]; exact hM.flag,
    by rw [rm₆]; exact hM.rm_lt, by rw [rm₆]; exact hM.rm, rz₆,
    ⟨_, _, _, _, _, _, q₂, q₅, by
      rw [t₆, tR₅ (by decide), tR₅ (by decide), ha, hb, tu (by decide) (by decide) ux₃,
        tu (by decide) (by decide) uy₃, tu (by decide) (by decide) uz₃]
      rfl⟩, ?_⟩
  · rw [tbl_unch UW h7 (j := 1) (by decide) ht (apart_append (tbl_apart_tbl (by decide) ht)
      (tbl_apart_slWk (by decide)))]
    exact hM.t₁ t ht
  · refine whole_of' hM.unch UW fun w hw => (List.mem_append.mp hw).elim
      (fun hw => by rw [List.mem_singleton.mp hw]; exact tbl_le h7)
      fun hw => by have := slWk_le h7 (by decide) w hw; dsimp only [size] at this; omega

end VG.Proof.Ecdsa.Verify.Arm
