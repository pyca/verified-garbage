import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Scalars
import VerifiedGarbage.Proof.Ecdsa.X86_64.GMul
import VerifiedGarbage.Proof.Ecdh.X86_64.Window

/-!
# ECDSA verification on x86-64: `[u]G + [v]Q`

`points_ok`: from what `mid_ok` leaves, the table of `u`'s bits, the
signature's `[u]G` (its comb, or its ladder: `gMul_ok'`), `save` (`[u]G` to
`U`, and `R = O`), `[v]Q` (`mulV_ok`: ECDH's window method for up to six
words, after `b R mod p` is set again in its slot, else the table of `v`'s
bits and ECDH's ladder, with the invariant of the group law) and `sum` (the
complete addition of `U` and `R`, into `R`): `R` holds `rcbAdd` of
representatives of `[u]G` and `[v]Q`.
-/

namespace VG.Proof.Ecdsa.Verify.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64
open VG.Impl.Ecdh.X86_64 (PX PY BP)
open VG.Impl.Ecdsa.Verify.X86_64 (SM' EM' RM' UM VM U V UX UY UZ)

variable {c : Cfg}

/-- `[o] = [a]`, on numbered slots. -/
theorem copySl_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size) {o a : Nat}
    (ho : o < 45) (ha : a < 45) (hoa : o ≠ a) :
    WP isa (.block (copy c.n (c.sl o) (c.sl a))) s fun s' =>
      sv c base s' o = sv c base s a ∧ KeepRegs [.rax] s s' ∧
      Outside base (c.sl o) (8 * c.n) s.mem s'.mem := by
  have := sl_apart c hoa
  exact copy_ok c.n hs (sl_le c hc.n10 ho) (sl_le c hc.n10 ha) (by omega)

/-- `[o] = x`, on numbered slots. -/
theorem setSl_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size) {o x : Nat}
    (ho : o < 45) (hx : x < 2 ^ (64 * c.n)) :
    WP isa (.block (setConst c.n (c.sl o) x)) s fun s' =>
      sv c base s' o = x ∧ KeepRegs [.rax] s s' ∧ Outside base (c.sl o) (8 * c.n) s.mem s'.mem :=
  setConst_ok hs (sl_le c hc.n10 ho) hx

/-- The slots `save` writes. -/
abbrev saveW : List Nat := [UX, UY, UZ, RX, RY, RZ]

theorem save_eq (c : Cfg) : Impl.Ecdsa.Verify.X86_64.Cfg.save c =
    copy c.n (c.sl UX) (c.sl RX) ++ (copy c.n (c.sl UY) (c.sl RY) ++ (copy c.n (c.sl UZ) (c.sl RZ) ++
    (setConst c.n (c.sl RX) 0 ++ (setConst c.n (c.sl RY) (c.mont 1) ++ setConst c.n (c.sl RZ) 0)))) := by
  simp only [Impl.Ecdsa.Verify.X86_64.Cfg.save, List.append_assoc]

/-- `U = R`, and `R = O`. -/
theorem save_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size) :
    WP isa (.block (Impl.Ecdsa.Verify.X86_64.Cfg.save c)) s fun s' =>
      Scr s' base size ∧ KeepRegs [.rax] s s' ∧ Unch base (slW c saveW) s.mem s'.mem ∧
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
  rw [WP.block_append_iff]
  refine WP.mono (copySl_ok hc hs (o := UX) (a := RX) (by decide) (by decide) (by decide))
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copySl_ok hc hs₁ (o := UY) (a := RY) (by decide) (by decide) (by decide))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copySl_ok hc hs₂ (o := UZ) (a := RZ) (by decide) (by decide) (by decide))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (setSl_ok hc hs₃ (o := RX) (x := 0) (by decide) (Nat.two_pow_pos _))
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (setSl_ok hc hs₄ (o := RY) (by decide) hm1) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  have hs₅ := hs₄.of_keepRegs k₅ (by decide)
  refine WP.mono (setSl_ok hc hs₅ (o := RZ) (x := 0) (by decide) (Nat.two_pow_pos _))
    fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  have o : ∀ {s s' : State} {j i : Nat}, Outside base (c.sl j) (8 * c.n) s.mem s'.mem → i < 45 → i ≠ j →
      sv c base s' i = sv c base s i := fun O hi hij => sv_out O h7 hn hi hij
  refine ⟨hs₅.of_keepRegs k₆ (by decide),
    (k₁.trans (k₂.trans (k₃.trans (k₄.trans (k₅.trans k₆))))).mono (by intro r hr; simpa using hr), ?_,
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

theorem sum_eq (c : Cfg) : Impl.Ecdsa.Verify.X86_64.Cfg.sum c =
    .seq (fprogB c.MP' (rcb c.rcbSlots (c.pt UX UY UZ) (c.pt RX RY RZ) (c.pt DX DY DZ)))
      (.block (copy c.n (c.sl RX) (c.sl DX) ++ (copy c.n (c.sl RY) (c.sl DY) ++
        copy c.n (c.sl RZ) (c.sl DZ)))) := by
  simp only [Impl.Ecdsa.Verify.X86_64.Cfg.sum, List.append_assoc]

/-- `R = U + R`, by the complete addition. -/
theorem sum_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size)
    (hM : ModOkW c.MP' size c.C.p s.mem base) (hlt : ∀ i ∈ sumR, sv c base s i < c.C.p) :
    WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.sum c) s fun s' =>
      Scr s' base size ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Unch base (slW c sumW) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem base ∧
      sv c base s' RX < c.C.p ∧ sv c base s' RZ < c.C.p ∧
      (tmv c.C c.n base s' (c.sl RX), tmv c.C c.n base s' (c.sl RY), tmv c.C c.n base s' (c.sl RZ)) =
        rcbAdd (tmv c.C c.n base s (c.sl AP)) (tmv c.C c.n base s (c.sl B3P))
          (tmv c.C c.n base s (c.sl UX)) (tmv c.C c.n base s (c.sl UY)) (tmv c.C c.n base s (c.sl UZ))
          (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY)) (tmv c.C c.n base s (c.sl RZ)) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hL : Lay c.MP' size (· ∈ sumSl.map c.sl) := lay_map hc rfl rfl rfl (by decide)
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
  refine WP.seq ((fprogB_wp _ _).mpr (WP.mono (rcb_ok hL hpR hA (fun x hx => ?_) hI (fun x hx => hx))
    fun s₁ ⟨k₁, I₁, t₁, _⟩ => ?_))
  · rw [show rcbW c.rcbSlots (c.pt DX DY DZ) ++ rcbR c.rcbSlots (c.pt UX UY UZ) (c.pt RX RY RZ) =
      ([T0, T1, T2, T3, T4, T5, DX, DY, DZ] ++ sumR).map c.sl from rfl] at hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have sub : ∀ i ∈ [T0, T1, T2, T3, T4, T5, DX, DY, DZ] ++ sumR, i ∈ sumSl := by decide
    exact List.mem_map_of_mem (sub i hi)
  have hs₁ := k₁.scr hs
  have hD : ∀ i ∈ [DX, DY, DZ], c.sl i ∈ rcbW c.rcbSlots (c.pt DX DY DZ) ++ sumR.map c.sl := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> simp [rcbW, Cfg.pt]
  rw [WP.block_append_iff]
  refine WP.mono (copySl_ok hc hs₁ (o := RX) (a := DX) (by decide) (by decide) (by decide))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copySl_ok hc hs₂ (o := RY) (a := DY) (by decide) (by decide) (by decide))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
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
  have U₄ : Unch base (slW c sumW) s.mem s₄.mem := by
    have := (k₁.unch.trans (O₂.unch.trans (O₃.unch.trans O₄.unch)))
    refine this.mono fun w hw => ?_
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
    rcases hw with (⟨y, hy, rfl⟩ | hw) | hw | hw | hw
    · simp only [rcbW, Cfg.rcbSlots, Cfg.pt, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [MP'_n]
    all_goals (subst hw; simp [MP'_n, MP'_tmp])
  refine ⟨hs₃.of_keepRegs k₄ (by decide), by rw [k₄.rd, k₃.rd, k₂.rd, k₁.rd],
    by rw [k₄.wr, k₃.wr, k₂.wr, k₁.wr], U₄, ?_, ?_, ?_, ?_⟩
  · have hM₁ := I₁.mod
    refine ⟨hM₁.n0, hM₁.mo, hM₁.tmp, hM₁.sep, ?_, hM₁.inv, hM₁.red⟩
    rw [U₄.wordsVal (fun w hw => ?_) (by have := hM₁.mo; omega)]
    · exact hM.val
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      have ne : ∀ i ∈ sumW, MP ≠ i := by decide
      exact sl_apart c (ne i hi)
  · rw [x₄]; exact I₁.lt _ (hD DX (by simp))
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

/-! ## `[v]Q` -/

/-- The slots `mulV` may write, in either case. -/
abbrev vI : List Nat := BP :: (otherI ++ tblI ++ [TMP])

/-- What `mulV` writes: for up to nine words, `BP` and the window method's
areas and slots; for more, the table of bits and the ladder's slots. -/
def vW (c : Cfg) : List (Nat × Nat) :=
  if c.n ≤ 9 then winX c ++ slW c vI
  else [(bitsAt c.n 0, 64 * c.n)] ++ slW c [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2,
    T3, T4, T5, TX, TY, TZ, TMP]

theorem fixedOk_vW : FixedOk c (vW c) := by
  unfold vW; split
  · exact fixedOk_winX.append (fixedOk_slW (by decide))
  · exact (fixedOk_tbl 0).append (fixedOk_slW (by decide))

/-- A numbered slot below the tables not in `vI` is apart from what `mulV`
writes. -/
theorem apart_vW {i : Nat} (hi : i < 45) (hl : i ∉ vI) :
    ∀ w ∈ vW c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  unfold vW; split
  · exact apart_append (apart_winX hi) (apart_slW hl)
  · have sub : ∀ j ∈ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ,
        TMP], j ∈ vI := by decide
    exact apart_append (apart_tbl hi 0) (apart_slW fun h => hl (sub _ h))

/-- The table of the bits of `p - 2` is apart from what `mulV` writes. -/
theorem tbl₁_apart_vW {t : Nat} (ht : t < 64 * c.n) :
    ∀ w ∈ vW c, bitsAt c.n 1 + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n 1 + t := by
  unfold vW; split
  · exact apart_append (tbl_apart_winX (by decide) ht) (tbl_apart_slW' (by decide) (by decide) ht)
  · refine apart_append (fun w hw => ?_) (tbl_apart_slW (by decide) 1 t)
    rw [List.mem_singleton.mp hw]; simp only [bitsAt_eq]; exact Or.inr (by omega)

/-- What `mulV` writes is in the working space. -/
theorem vW_le (h7 : c.n < 10) : ∀ w ∈ vW c, w.1 + w.2 ≤ size := by
  unfold vW; split
  · rename_i h9
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · simp only [winX, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · show c.sl WK + 16 * c.n ≤ size
        have := sl_le_win c h9 (i := WK + 1) (by decide)
        rw [sl_eq] at this ⊢; rw [Nat.mul_add] at this; omega
      · show c.sl WB + 80 * c.n ≤ size
        have := sl_le_win c h9 (i := WB + 9) (by decide)
        rw [sl_eq] at this ⊢; rw [Nat.mul_add] at this; omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      have lt : ∀ i ∈ vI, i < 107 := by decide
      exact sl_le_win c h9 (lt i hi)
  · intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · rw [List.mem_singleton.mp hw]; have := bitsAt_le c h7 (j := 0) (by decide); exact this
    · exact slW_le h7 (by decide) w hw

/-- What `mulV` leaves: `R` represents `[k]P`. -/
structure VMulPost (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (powClob c.n) s s'
  unch : Unch base (vW c) s.mem s'.mem
  mod : ModOkW c.MP' size c.C.p s'.mem base
  lt : ∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p
  q : Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
    (tmv c.C c.n base s' (c.sl RZ)) (mul k P)

/-- `[v]P`, for `v` at `V`, `P` at `PX`, `PY` and `R = O`: by windows for up
to nine words, else by the ladder. -/
theorem mulV_ok (hc : CfgOk c) (hC : Law c.C) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (F : Fixed c base g s.mem)
    {P : Point c.C} (hP : onCurve c.C P = true) (hpx : sv c base s PX < c.C.p) (hpy : sv c base s PY < c.C.p)
    (hrep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P)
    (hrx : sv c base s RX = 0) (hry : sv c base s RY = c.mont 1) (hrz : sv c base s RZ = 0)
    {rest : Prog isa} {R : State → Prop}
    (hv8 : sv c base s V < 2 ^ c.nbits)
    (h : ∀ s', VMulPost c base P (sv c base s V) s s' → WP isa rest s' R) :
    WP isa (.seq (Impl.Ecdsa.Verify.X86_64.Cfg.mulV c) rest) s R := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  unfold Impl.Ecdsa.Verify.X86_64.Cfg.mulV
  split
  · rename_i h9
    have hb : c.mont c.C.b < 2 ^ (64 * c.n) := by have := hc.p_lt; have := hmont c.C.b; omega
    refine WP.seq (WP.seq (WP.mono (setSl_ok hc hs (o := BP) (by decide) hb) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_))
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have F₁ := F.unch h7 hn (fixedOk_slW (l := [BP]) (by decide)) O₁.unch
    have v₁ : ∀ {i}, i < 45 → i ≠ BP → sv c base s₁ i = sv c base s i := fun hi hij => sv_out O₁ h7 hn hi hij
    have hrep₁ : Rep c.C (tmv c.C c.n base s₁ (c.sl PX)) (tmv c.C c.n base s₁ (c.sl PY))
        (tmv c.C c.n base s₁ (c.sl ONEP)) P := by
      show Rep _ (toM _ _ (sv c base s₁ PX)) (toM _ _ (sv c base s₁ PY)) (toM _ _ (sv c base s₁ ONEP)) P
      rw [v₁ (by decide) (by decide), v₁ (by decide) (by decide), v₁ (by decide) (by decide)]
      exact hrep
    refine WP.seq_iff.mp (winMul_ok hc h9 hC hs₁ F₁ e₁ hP (by rw [v₁ (by decide) (by decide)]; exact hpx)
      (by rw [v₁ (by decide) (by decide)]; exact hpy) hrep₁ (ks := V) (by decide)
      (by rw [v₁ (by decide) (by decide)]; exact hv8) fun s₂ W => h s₂ ?_)
    rw [v₁ (by decide) (by decide)] at W
    refine ⟨W.scr, (k₁.mono fun r hr => ?_).trans W.keep, ?_, W.mod, W.lt, W.q⟩
    · rw [List.mem_singleton.mp hr]; simp [powClob, clob]
    · simp only [vW, h9, ↓reduceIte]
      refine (O₁.unch.trans W.unch).mono fun w hw => ?_
      rcases List.mem_append.mp hw with hw | hw
      · rw [List.mem_singleton.mp hw]; exact List.mem_append_right _ (List.mem_cons_self ..)
      · rcases List.mem_append.mp hw with hw | hw
        · exact List.mem_append_left _ hw
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ hw)
  · rename_i h9
    refine WP.seq (WP.seq (WP.mono (bits_ok hs h0 (by omega) (sl_le c h7 (i := V) (by decide))
      (bitsAt_le c h7 (j := 0) (by decide)) (Or.inl (by have := sl_below_bits c (i := V) (by decide) 0 0; omega)))
      fun s₁ ⟨b₁, k₁, O₁⟩ => ?_))
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have U₁ : Unch base [(bitsAt c.n 0, 64 * c.n)] s.mem s₁.mem := O₁.unch
    have F₁ := F.unch h7 hn (fixedOk_tbl 0) U₁
    have v₁ : ∀ {i}, i < 45 → sv c base s₁ i = sv c base s i := fun hi => sv_unch U₁ h7 hn hi (apart_tbl hi 0)
    have hk : sv c base s V < 2 ^ (64 * c.n) := wordsVal_lt _ _ _ _
    have hstep := step_rep (L := Impl.Ecdh.X86_64.Cfg.ladderQ c) (s := s₁) (k := sv c base s V) hC hP
      (by
        show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₁.mem _ (c.sl AP) c.n) = _
        rw [F₁.ap]; exact toM_cmont hc _)
      (by
        show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₁.mem _ (c.sl B3P) c.n) = _
        rw [F₁.b3p]; exact toM_cmont hc _)
      (by
        show Rep _ (toM _ _ (sv c base s₁ PX)) (toM _ _ (sv c base s₁ PY)) (toM _ _ (sv c base s₁ ONEP)) P
        rw [v₁ (by decide), v₁ (by decide), v₁ (by decide)]
        exact hrep)
    have hlt : ∀ x ∈ ladR (Impl.Ecdh.X86_64.Cfg.ladderQ c), wordsVal s₁.mem base x c.MP'.n < c.C.p := by
      intro x hx
      have hx' : x ∈ [AP, B3P, PX, PY, ONEP, RX, RY, RZ].map c.sl := hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      show sv c base s₁ i < c.C.p
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact lt_of_eq_of_lt F₁.ap (hmont _)
      · exact lt_of_eq_of_lt F₁.b3p (hmont _)
      · rw [v₁ (by decide)]; exact hpx
      · rw [v₁ (by decide)]; exact hpy
      · exact lt_of_eq_of_lt F₁.onep (Nat.mod_lt _ (by omega))
      · rw [v₁ (by decide), hrx]; omega
      · rw [v₁ (by decide), hry]; exact hmont _
      · rw [v₁ (by decide), hrz]; omega
    have hR : Rep c.C (tmv c.C c.n base s₁ (c.sl RX)) (tmv c.C c.n base s₁ (c.sl RY))
        (tmv c.C c.n base s₁ (c.sl RZ)) (mul (sv c base s V >>> (64 * c.n)) P) := by
      show Rep _ (toM _ _ (sv c base s₁ RX)) (toM _ _ (sv c base s₁ RY)) (toM _ _ (sv c base s₁ RZ)) _
      rw [v₁ (by decide), v₁ (by decide), v₁ (by decide), hrx, hry, hrz, toM_cmont hc, toM_zero,
        shiftRight_eq_zero hk, mul_zero_pt]
      exact rep_infinity' hC
    refine WP.mono (ladder_ok (ladLayQ hc) hpR hs₁ (modP_of hc F₁.mp) hlt hstep hR (fun t ht => b₁ t ht))
      fun s₂ ⟨K₂, U₂, M₂, L₂, q₂⟩ => h s₂ ⟨hs₁.of_keepRegs K₂ (rdi_not_powClob _),
        (k₁.mono fun r hr => ?_).trans K₂, ?_, M₂, L₂, by rwa [Nat.shiftRight_zero] at q₂⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [powClob, clob]
    · simp only [vW, h9, ↓reduceIte]
      rw [← ladWQ_eq]
      exact U₁.trans U₂

/-- After `[u]G + [v]P`: `R` holds the complete addition of representatives
of `[u]G` and `[v]P`. -/
structure Pts (c : Cfg) (s₀ : State) (base : Addr) (g : Reg → BitVec 64) (u v : Nat) (P : Point c.C)
    (s : State) : Prop where
  scr : Scr s base size
  wr : s.wr = s₀.wr
  rd : s.rd = s₀.rd
  fixed : Fixed c base g s.mem
  k : sv c base s K = sigR c s₀
  t₁ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) = if (c.C.p - 2).testBit t then 1 else 0
  flag : word s.mem base (c.sl FLAG) =
    mask (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n))
  rm_lt : sv c base s RM' < c.C.n
  rm : toM c.C.n (2 ^ (64 * c.n)) (sv c base s RM') = Fin.ofNat c.C.n (sigR c s₀)
  rx_lt : sv c base s RX < c.C.p
  rz_lt : sv c base s RZ < c.C.p
  pt : ∃ X1 Y1 Z1 X2 Y2 Z2 : Fe c.C, Rep c.C X1 Y1 Z1 (mul u (G c.C)) ∧ Rep c.C X2 Y2 Z2 (mul v P) ∧
    (tmv c.C c.n base s (c.sl RX), tmv c.C c.n base s (c.sl RY), tmv c.C c.n base s (c.sl RZ)) =
      rcbAdd (Fin.ofNat c.C.p c.C.a) (Fin.ofNat c.C.p (3 * c.C.b)) X1 Y1 Z1 X2 Y2 Z2
  unch : Unch base [(0, size)] s₀.mem s.mem

theorem points_eq (c : Cfg) : Impl.Ecdsa.Verify.X86_64.Cfg.points c =
    .seq (bits (c.sl U) (bitsAt c.n 0) (8 * c.n)) (.seq (c.gMul c.pubVerify)
      (.seq (.block (Impl.Ecdsa.Verify.X86_64.Cfg.save c)) (.seq (Impl.Ecdsa.Verify.X86_64.Cfg.mulV c)
        (Impl.Ecdsa.Verify.X86_64.Cfg.sum c)))) := rfl

/-- The slots `[u]G`, `save` and the sum write (`vW` has `mulV`'s). -/
abbrev ptsW : List Nat :=
  [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TX, TY, TZ, PT, TMP, UX, UY, UZ, EM]

/-- `[u]G + [v]Q`, into `R`. -/
theorem points_ok (hc : CfgOk c) (hC : Law c.C) (hT : CombTbls c) {s₀ : State} {base : Addr}
    {g : Reg → BitVec 64} {s : State} (hM : Mid c s₀ base g s) (htb : TblsHeld c s₀ s₀.wr)
    (hsc : (⟨base, size⟩ : Region) ∈ s₀.wr)
    (hrdT : ∀ r ∈ Abi.constRegions (fun n => s₀.syms n) c.combConsts, r ∈ s₀.rd)
    {P : Point c.C} (hP : onCurve c.C P = true)
    (hrep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', Pts c s₀ base g (sv c base s U) (sv c base s V) P s' → WP isa rest s' Q) :
    WP isa (.seq (Impl.Ecdsa.Verify.X86_64.Cfg.points c) rest) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hM.scr.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have F := hM.fixed
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  have tb : ∀ {i}, i < 45 → ∀ w ∈ [(bitsAt c.n 0, 64 * c.n)], c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
    fun hi => apart_tbl hi 0
  rw [points_eq]
  refine WP.seq ?_
  -- The table of `u`.
  refine WP.seq (WP.mono_syms (bits_ok hM.scr h0 (by omega) (sl_le c h7 (i := U) (by decide))
    (bitsAt_le c h7 (j := 0) (by decide)) (Or.inl (by have := sl_below_bits c (i := U) (by decide) 0 0; omega)))
    fun s₁ ⟨b₁, k₁, O₁⟩ sy₁ => ?_)
  have hs₁ := hM.scr.of_keepRegs k₁ (by decide)
  have U₁ : Unch base [(bitsAt c.n 0, 64 * c.n)] s.mem s₁.mem := O₁.unch
  have F₁ := F.unch h7 hn (fixedOk_tbl 0) U₁
  have v₁ : ∀ {i}, i < 45 → sv c base s₁ i = sv c base s i := fun hi => sv_unch U₁ h7 hn hi (tb hi)
  -- `[u]G`.
  have hTb : ∀ d, c.comb = some d → TblMem s₁ (s₁.syms d.tsym) (c.combWords d) ∧
      ∀ i < (c.combWords d).length, ∀ b < 8,
        size ≤ ofs base (s₁.syms d.tsym + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b) := fun d hcd => by
    rw [sy₁, hM.syms]
    refine tbl_of_held hcd htb hsc (fun r hr => by rw [k₁.rd, hM.rd]; exact hrdT r hr) ?_
    have hb0 := bitsAt_le c h7 (j := 0) (by decide)
    exact Unch.cover (hM.unch.trans U₁) fun w hw => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact ⟨_, List.mem_singleton_self _, Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨_, List.mem_singleton_self _, Nat.zero_le _, by dsimp only; omega⟩
  refine WP.seq (WP.mono (gMul_ok' (publicLookup := c.pubVerify) hc hC hT hs₁ F₁ (k := sv c base s U) (wordsVal_lt _ _ _ _)
    (by rw [v₁ (by decide), hM.rx]) (by rw [v₁ (by decide), hM.ry]) (by rw [v₁ (by decide), hM.rz])
    (fun t ht => b₁ t ht) hTb)
    fun s₂ ⟨K₂, U₂, M₂, L₂, q₂⟩ => ?_)
  have hs₂ := hs₁.of_keepRegs K₂ (rdi_not_powClob _)
  have F₂ := F₁.unch h7 hn fixedOk_gW U₂
  -- `U = [u]G`, `R = O`.
  refine WP.seq (WP.mono (save_ok hc hs₂) fun s₃ ⟨hs₃, k₃, U₃, ux₃, uy₃, uz₃, rx₃, ry₃, rz₃⟩ => ?_)
  have F₃ := F₂.unch h7 hn (fixedOk_slW (by decide)) U₃
  have sub₂ : ∀ i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM], i ∈ ptsW := by
    decide
  have sub₃ : ∀ i ∈ saveW, i ∈ ptsW := by decide
  have W₃ : ∀ {i}, i < 45 → i ∉ ptsW → sv c base s₃ i = sv c base s i := fun hi hl =>
    ((sv_unch U₃ h7 hn hi (apart_slW (fun h => hl (sub₃ _ h)))).trans
      (sv_unch U₂ h7 hn hi (apart_gW hi (fun h => hl (sub₂ _ h))))).trans (v₁ hi)
  -- `[v]P`.
  have tv₃ : ∀ {i}, i < 45 → i ∉ ptsW → tmv c.C c.n base s₃ (c.sl i) = tmv c.C c.n base s (c.sl i) :=
    fun hi hl => by
      show toM _ _ (sv c base s₃ _) = toM _ _ (sv c base s _)
      rw [W₃ hi hl]
  refine mulV_ok hc hC hs₃ F₃ hP (by rw [W₃ (by decide) (by decide)]; exact hM.px_lt)
    (by rw [W₃ (by decide) (by decide)]; exact hM.py_lt)
    (by rw [tv₃ (by decide) (by decide), tv₃ (by decide) (by decide), tv₃ (by decide) (by decide)]; exact hrep)
    rx₃ ry₃ rz₃ (by rw [W₃ (by decide) (by decide)]; exact Nat.lt_of_lt_of_le hM.v_lt hc.n_bits)
    fun s₅ V₅ => ?_
  rw [show sv c base s₃ V = sv c base s V from W₃ (by decide) (by decide)] at V₅
  have hs₅ := V₅.scr
  have F₅ := F₃.unch h7 hn fixedOk_vW V₅.unch
  have v₅ : ∀ {i}, i < 45 → i ∉ vI → sv c base s₅ i = sv c base s₃ i := fun hi hl =>
    sv_unch V₅.unch h7 hn hi (apart_vW hi hl)
  -- The sum.
  have u₅ : ∀ {i}, i ∈ [UX, UY, UZ] → sv c base s₅ i = sv c base s₃ i := fun {i} hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> exact v₅ (by decide) (by decide)
  refine WP.mono (sum_ok hc hs₅ V₅.mod (fun i hi => ?_)) fun s₆ ⟨hs₆, rd₆, wr₆, U₆, M₆, rx₆, rz₆, t₆⟩ => h s₆ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt F₅.ap (hmont _)
    · exact lt_of_eq_of_lt F₅.b3p (hmont _)
    · rw [u₅ (by decide), ux₃]; exact L₂ _ (List.mem_cons_self ..)
    · rw [u₅ (by decide), uy₃]; exact L₂ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · rw [u₅ (by decide), uz₃]; exact L₂ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    · exact V₅.lt _ (List.mem_cons_self ..)
    · exact V₅.lt _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · exact V₅.lt _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have F₆ := F₅.unch h7 hn (fixedOk_slW (by decide)) U₆
  have sub₆ : ∀ i ∈ sumW, i ∈ ptsW := by decide
  have v₆ : ∀ {i}, i < 45 → i ∉ ptsW → i ∉ vI → sv c base s₆ i = sv c base s i := fun hi hl hl' =>
    (sv_unch U₆ h7 hn hi (apart_slW (fun h => hl (sub₆ _ h)))).trans ((v₅ hi hl').trans (W₃ hi hl))
  have UW : Unch base ([(bitsAt c.n 0, 64 * c.n + 8)] ++ (slW c ptsW ++ vW c)) s.mem s₆.mem := by
    have sl : ∀ {l : List Nat}, (∀ i ∈ l, i ∈ ptsW) → ∀ w ∈ slW c l,
        ∃ w' ∈ [(bitsAt c.n 0, 64 * c.n + 8)] ++ (slW c ptsW ++ vW c), w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 :=
      fun hl w hw => ⟨w, List.mem_append_right _ (List.mem_append_left _
        (List.map_subset _ (fun i hi => hl i hi) hw)), Nat.le_refl _, Nat.le_refl _⟩
    have tb0 : ∀ w ∈ [(bitsAt c.n 0, 64 * c.n)],
        ∃ w' ∈ [(bitsAt c.n 0, 64 * c.n + 8)] ++ (slW c ptsW ++ vW c), w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 :=
      fun w hw => by
        rw [List.mem_singleton.mp hw]
        exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), Nat.le_refl _, by dsimp only; omega⟩
    refine Unch.cover (U₁.trans (U₂.trans (U₃.trans (V₅.unch.trans U₆)))) fun w hw => ?_
    simp only [List.mem_append] at hw
    rcases hw with hw | (hw | hw) | hw | hw | hw
    · exact tb0 w hw
    · exact sl sub₂ w hw
    · rw [List.mem_singleton.mp hw]
      exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), by dsimp only; omega,
        by dsimp only; omega⟩
    · exact sl sub₃ w hw
    · exact ⟨w, List.mem_append_right _ (List.mem_append_right _ hw), Nat.le_refl _, Nat.le_refl _⟩
    · exact sl sub₆ w hw
  have tu : ∀ {i j}, i ∈ [UX, UY, UZ] → j ∈ [RX, RY, RZ] → sv c base s₃ i = sv c base s₂ j →
      tmv c.C c.n base s₅ (c.sl i) = tmv c.C c.n base s₂ (c.sl j) := fun hi _ e => by
    show toM _ _ (sv c base s₅ _) = toM _ _ (sv c base s₂ _)
    rw [u₅ hi, e]
  have tR₅ : ∀ {i}, i ∈ [AP, B3P] → tmv c.C c.n base s₅ (c.sl i) = tmv c.C c.n base s (c.sl i) :=
    fun {i} hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      show toM _ _ (sv c base s₅ _) = toM _ _ (sv c base s _)
      rcases hi with rfl | rfl <;> rw [v₅ (by decide) (by decide), W₃ (by decide) (by decide)]
  have ha : tmv c.C c.n base s (c.sl AP) = Fin.ofNat c.C.p c.C.a := by
    show toM _ _ (wordsVal s.mem base (c.sl AP) c.n) = _
    rw [F.ap]; exact toM_cmont hc _
  have hb : tmv c.C c.n base s (c.sl B3P) = Fin.ofNat c.C.p (3 * c.C.b) := by
    show toM _ _ (wordsVal s.mem base (c.sl B3P) c.n) = _
    rw [F.b3p]; exact toM_cmont hc _
  refine ⟨hs₆, by rw [wr₆, V₅.keep.wr, k₃.wr, K₂.wr, k₁.wr, hM.wr],
    by rw [rd₆, V₅.keep.rd, k₃.rd, K₂.rd, k₁.rd, hM.rd], F₆,
    by rw [v₆ (i := K) (by decide) (by decide) (by decide), hM.k], fun t ht => ?_, ?_,
    by rw [v₆ (by decide) (by decide) (by decide)]; exact hM.rm_lt,
    by rw [v₆ (by decide) (by decide) (by decide)]; exact hM.rm, rx₆, rz₆,
    ⟨_, _, _, _, _, _, q₂, V₅.q, by
      rw [t₆, tR₅ (by decide), tR₅ (by decide), ha, hb, tu (by decide) (by decide) ux₃,
        tu (by decide) (by decide) uy₃, tu (by decide) (by decide) uz₃]⟩, ?_⟩
  · rw [tbl_unch UW h7 hn (j := 1) (by decide) ht (apart_append (fun w hw => by
      rw [List.mem_singleton.mp hw]; simp only [bitsAt_eq]; exact Or.inr (by omega))
      (apart_append (tbl_apart_slW (by decide) 1 t) (tbl₁_apart_vW ht)))]
    exact hM.t₁ t ht
  · rw [UW.word (fun w hw => ?_) (by have := sl_le c h7 (i := FLAG) (by decide); omega)]
    · exact hM.flag
    · rcases List.mem_append.mp hw with hw | hw
      · rw [List.mem_singleton.mp hw]
        have := sl_below_bits c (i := FLAG) (by decide) 0 0
        exact Or.inl (by dsimp only; omega)
      · rcases List.mem_append.mp hw with hw | hw
        · exact (apart_slW (c := c) (i := FLAG) (by decide)) w hw |>.elim
            (fun h => Or.inl (by omega)) (fun h => Or.inr h)
        · exact (apart_vW (c := c) (i := FLAG) (by decide) (by decide)) w hw |>.elim
            (fun h => Or.inl (by omega)) (fun h => Or.inr h)
  · refine unch_whole (hM.unch.trans UW) fun w hw => ?_
    simp only [List.mem_append] at hw
    rcases hw with hw | hw | hw | hw
    · rw [List.mem_singleton.mp hw]; exact Nat.le_of_eq (Nat.zero_add _)
    · rw [List.mem_singleton.mp hw]; have := bitsAt_le_pad c h7 (j := 0) (by decide); dsimp only; omega
    · exact slW_le h7 (by decide) w hw
    · exact vW_le h7 w hw

end VG.Proof.Ecdsa.Verify.X86_64
