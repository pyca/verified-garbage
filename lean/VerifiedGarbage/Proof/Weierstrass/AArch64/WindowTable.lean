import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase

/-!
# The window method on AArch64: the table

The table `[1 … 8]P`: `P`, then `[m + 1]P = [m]P + P` by the complete addition (`build_ok`).
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

/-- The table's invariant: entries `[1 … m]P` built. -/
structure BuildInv (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ : State)
    (m : Nat) (s : State) : Prop where
  scr : Scr s base size
  keep : KeepRegs (.x19 :: clob K.M.n) s₀ s
  unch : Unch base (winW K) s₀.mem s.mem
  mod : ModOkA K.M size C.p s.mem base
  tbl : TblOk K C base P m s

theorem tblPt_slots (K : WinCfg) {m : Nat} (h1 : 1 ≤ m) (h8 : m ≤ 8) :
    ∀ x ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z], x ∈ winSlots K ∧ x ∈ winWs K := by
  intro x hx
  obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K h1 h8 x hx
  refine ⟨?_, winTbl_ws K hi⟩
  simp only [winSlots, List.mem_append]
  exact Or.inr (winTbl_mem K hi)

/-- The slots of entry `j` are apart from what the addition into entry
`m + 1 ≠ j` writes. -/
theorem tbl_apart_add {K : WinCfg} {size : Nat} (hL : WinLay K size) {j m : Nat} (hj1 : 1 ≤ j)
    (hj8 : j ≤ 8) (hm1 : 1 ≤ m + 1) (hm8 : m + 1 ≤ 8) (hjm : j ≠ m + 1) :
    ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
      ∀ w ∈ (rcbW K.S (K.tblPt (m + 1))).map (·, 8 * K.M.n) ++ [(K.M.tmp, 8 * K.M.n)],
        x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  intro x hx w hw
  obtain ⟨i, hi, rfl, hi₁, hi₂⟩ := tblPt_mem K hj1 hj8 x hx
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at hw
  rcases hw with ⟨y, hy, rfl⟩ | rfl
  · have ets : rcbW K.S (K.tblPt (m + 1)) = [K.S.t0, K.S.t1, K.S.t2, K.S.t3, K.S.t4, K.S.t5] ++
        [(K.tblPt (m + 1)).x, (K.tblPt (m + 1)).y, (K.tblPt (m + 1)).z] := rfl
    rw [ets, List.mem_append] at hy
    dsimp only
    rcases hy with hy | hy
    · exact (hL.tbl_apart (rcbW_mem_other y hy) hi).symm
    · obtain ⟨i', hi', rfl, hi'₁, hi'₂⟩ := tblPt_mem K hm1 hm8 y hy
      exact winTbl_apart K (by omega_using [hjm, hi₁, hi₂, hi'₁, hi'₂])
  · exact hL.lay.tmp _ (by
      simp only [winSlots, List.mem_append]; exact Or.inr (winTbl_mem K hi))

/-- `o = a`, a point, for `o`'s slots apart from each other and from `a`'s. -/
theorem copyPt_ok {s : State} {base : Addr} {size n : Nat} (hs : Scr s base size) {o a : Pt}
    (hle : ∀ x ∈ [o.x, o.y, o.z, a.x, a.y, a.z], x + 8 * n ≤ size)
    (hal : ∀ x ∈ [o.x, o.y, o.z, a.x, a.y, a.z], x % 8 = 0)
    (hap : ∀ x ∈ [o.x, o.y, o.z], ∀ y ∈ [o.x, o.y, o.z, a.x, a.y, a.z], x ≠ y →
      x + 8 * n ≤ y ∨ y + 8 * n ≤ x)
    (hne : ∀ x ∈ [o.x, o.y, o.z], x ∉ [a.x, a.y, a.z]) (ho : o.x ≠ o.y ∧ o.x ≠ o.z ∧ o.y ≠ o.z) :
    WP isa (.block (copyPt n o a)) s fun t =>
      wordsVal t.mem base o.x n = wordsVal s.mem base a.x n ∧
      wordsVal t.mem base o.y n = wordsVal s.mem base a.y n ∧
      wordsVal t.mem base o.z n = wordsVal s.mem base a.z n ∧
      KeepRegs [.x1] s t ∧ Unch base [(o.x, 8 * n), (o.y, 8 * n), (o.z, 8 * n)] s.mem t.mem := by
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, not_or] at hle hal hap hne
  obtain ⟨⟨xa, xb, xc⟩, ⟨ya, yb, yc⟩, ⟨za, zb, zc⟩⟩ := hne
  have pxy := hap.1.2.1 ho.1
  have pxz := hap.1.2.2.1 ho.2.1
  have pyz := hap.2.1.2.2.1 ho.2.2
  have pxa := hap.1.2.2.2.1 xa
  have pxb := hap.1.2.2.2.2.1 xb
  have pxc := hap.1.2.2.2.2.2 xc
  have pyb := hap.2.1.2.2.2.2.1 yb
  have pyc := hap.2.1.2.2.2.2.2 yc
  have pzc := hap.2.2.2.2.2.2.2 zc
  rw [copyPt, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copy_ok n hs (o := o.x) (a := a.x) hle.1 hle.2.2.2.1 hal.1 hal.2.2.2.1 (by omega_using [pxa]))
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  refine WP.mono (copy_ok n hs₁ (o := o.y) (a := a.y) hle.2.1 hle.2.2.2.2.1 hal.2.1 hal.2.2.2.2.1
    (by omega_using [pyb])) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (copy_ok n hs₂ (o := o.z) (a := a.z) hle.2.2.1 hle.2.2.2.2.2 hal.2.2.1 hal.2.2.2.2.2
    (by omega_using [pzc])) fun t ⟨e₃, k₃, O₃⟩ => ⟨?_, ?_, ?_, (k₁.trans k₂).trans k₃, ?_⟩
  · rw [O₃.wordsVal (by omega_using [pxz]) (by omega_using [hn, hle]), O₂.wordsVal (by omega_using [pxy]) (by omega_using [hn, hle]), e₁]
  · rw [O₃.wordsVal (by omega_using [pyz]) (by omega_using [hn, hle]), e₂, O₁.wordsVal (by omega_using [pxb]) (by omega_using [hn, hle])]
  · rw [e₃, O₂.wordsVal (by omega_using [pyc]) (by omega_using [hn, hle]), O₁.wordsVal (by omega_using [pxc]) (by omega_using [hn, hle])]
  · exact (O₁.unch.trans (O₂.unch.trans O₃.unch)).mono fun w hw => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      rcases hw with h | h | h <;> simp [h]

/-- The table's entries `[1 … m]P`, `E = [m]P`, and `x19 = 8 - m`: what holds
between the additions that build the table. -/
structure BuildInvE (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ : State)
    (m : Nat) (s : State) : Prop where
  inv : BuildInv K C base size P s₀ m s
  lt : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s.mem base x K.M.n < C.p
  rep : Rep C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z) (mul m P)
  x19 : s.gpr .x19 = BitVec.ofNat 64 (8 - m)

/-- `x2 = x19 - i`. -/
theorem subCounter_ok (s : State) {j i : Nat} (hi : i < 4096) (hj : j < 2 ^ 63)
    (h19 : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block [.subImm .x .x2 .x19 i]) s fun t =>
      isa.eval (.zero .x .x2) t = some (decide (j = i)) ∧ Keeps [.x2] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, hi, ite_true,
    Option.some.injEq, exists_eq_left', h19]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · show some (_ == 0) = _
    congr 1
    simp only [read_x, RegUpd.gpr_write_self, BitVec.setWidth_eq, Size.bits]
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj]
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega_using [hi]),
      Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega_using [hj])]
    change _ = 0 ↔ _
    omega_using [hi, hj]
  · simp only [List.mem_singleton] at hr
    exact RegUpd.gpr_write_of_ne _ _ _ hr

/-- The table's slots of entry `j`, apart from what a store into entry `m`,
`m ≠ j`, writes. -/
theorem tbl_apart_entry {K : WinCfg} {j m : Nat} (hj1 : 1 ≤ j) (hj8 : j ≤ 8) (hm1 : 1 ≤ m) (hm8 : m ≤ 8)
    (hjm : j ≠ m) : ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
      ∀ y ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z],
        x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := by
  intro x hx y hy
  obtain ⟨i, hi, rfl, hi₁, hi₂⟩ := tblPt_mem K hj1 hj8 x hx
  obtain ⟨i', hi', rfl, hi'₁, hi'₂⟩ := tblPt_mem K hm1 hm8 y hy
  exact winTbl_apart K (by omega_using [hjm, hi₁, hi₂, hi'₁, hi'₂])

/-- The facts a copy from `D` into entry `m` of the table needs. -/
theorem copyD_tbl {K : WinCfg} {size : Nat} (hL : WinLay K size) (hA : WinA K) {m : Nat} (hm1 : 1 ≤ m)
    (hm8 : m ≤ 8) :
    (∀ x ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z, K.D.x, K.D.y, K.D.z], x + 8 * K.M.n ≤ size) ∧
    (∀ x ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z, K.D.x, K.D.y, K.D.z], x % 8 = 0) ∧
    (∀ x ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z],
      ∀ y ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z, K.D.x, K.D.y, K.D.z], x ≠ y →
        x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x) ∧
    (∀ x ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z], x ∉ [K.D.x, K.D.y, K.D.z]) ∧
    ((K.tblPt m).x ≠ (K.tblPt m).y ∧ (K.tblPt m).x ≠ (K.tblPt m).z ∧ (K.tblPt m).y ≠ (K.tblPt m).z) := by
  have st := tblPt_slots K hm1 hm8
  have dO : ∀ y ∈ [K.D.x, K.D.y, K.D.z], y ∈ winOther K := by
    intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl <;> win_in
  have sl : ∀ x ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z, K.D.x, K.D.y, K.D.z], x ∈ winSlots K := by
    intro x hx
    rcases List.mem_append.mp (show x ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z] ++
      [K.D.x, K.D.y, K.D.z] from hx) with h | h
    · exact (st x h).1
    · exact winOther_mem (dO x h)
  have td : ∀ x ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z], ∀ y ∈ [K.D.x, K.D.y, K.D.z],
      x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := by
    intro x hx y hy
    obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K hm1 hm8 x hx
    exact (hL.tbl_apart (List.mem_append_right _ (dO y hy)) hi).symm
  have ne : (K.tblPt m).x ≠ (K.tblPt m).y ∧ (K.tblPt m).x ≠ (K.tblPt m).z ∧ (K.tblPt m).y ≠ (K.tblPt m).z := by
    rw [tblPt_x, tblPt_y, tblPt_z]
    exact ⟨hL.tbl_ne₂ (by omega_using []), hL.tbl_ne₂ (by omega_using []), hL.tbl_ne₂ (by omega_using [])⟩
  refine ⟨fun x hx => hL.lay.le x (sl x hx), fun x hx => hA.sl x (sl x hx), fun x hx y hy hxy => ?_,
    fun x hx hy => ?_, ne⟩
  · rcases List.mem_append.mp (show y ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z] ++
      [K.D.x, K.D.y, K.D.z] from hy) with h | h
    · exact hL.apart₂ (st x hx).2 (st y h).2 hxy
    · exact td x hx y h
  · have := td x hx x hy
    have := hL.n0
    omega

/-- `D` into entry `8 - i` of the table, for `x19 = i ≤ j ≤ 6`. -/
theorem storeEntry_ok {K : WinCfg} {size : Nat} (hL : WinLay K size) (hA : WinA K) {base : Addr} {i : Nat} :
    ∀ (j : Nat) {s : State}, i ≤ j → j ≤ 6 → Scr s base size → s.gpr .x19 = BitVec.ofNat 64 i →
      WP isa (WinCfg.storeEntry K j) s fun t =>
        wordsVal t.mem base (K.tblPt (8 - i)).x K.M.n = wordsVal s.mem base K.D.x K.M.n ∧
        wordsVal t.mem base (K.tblPt (8 - i)).y K.M.n = wordsVal s.mem base K.D.y K.M.n ∧
        wordsVal t.mem base (K.tblPt (8 - i)).z K.M.n = wordsVal s.mem base K.D.z K.M.n ∧
        KeepRegs [.x1, .x2] s t ∧
        Unch base [((K.tblPt (8 - i)).x, 8 * K.M.n), ((K.tblPt (8 - i)).y, 8 * K.M.n),
          ((K.tblPt (8 - i)).z, 8 * K.M.n)] s.mem t.mem
  | 0, s, hi, _, hs, _ => by
    obtain rfl : i = 0 := by omega_using [hi]
    rw [WinCfg.storeEntry]
    obtain ⟨a, b, c, d, e⟩ := copyD_tbl hL hA (m := 8) (by decide) (Nat.le_refl _)
    exact WP.mono (copyPt_ok hs a b c d e) fun t ⟨e1, e2, e3, k, U⟩ =>
      ⟨e1, e2, e3, k.mono fun r hr => by simp at hr; simp [hr], U⟩
  | j + 1, s, hi, hj, hs, h19 => by
    rw [WinCfg.storeEntry]
    refine WP.seq (WP.mono (subCounter_ok s (j := i) (i := j + 1) (by omega_using [hj]) (by omega_using [hi, hj]) h19)
      fun t ⟨ev, kt⟩ => ?_)
    have hst := hs.of_keeps kt (by decide)
    have mt : t.mem = s.mem := kt.mem
    have kt' : KeepRegs [.x1, .x2] s t := (Keeps.regs kt).mono fun r hr => by simp at hr; simp [hr]
    refine WP.ite _ ev (fun he => ?_) (fun he => ?_)
    · obtain rfl : i = j + 1 := of_decide_eq_true he
      obtain ⟨a, b, c, d, e⟩ := copyD_tbl hL hA (m := 7 - j) (by omega_using [hj]) (by omega_using [])
      rw [show 8 - (j + 1) = 7 - j by omega_using []]
      exact WP.mono (copyPt_ok hst a b c d e) fun u ⟨e1, e2, e3, k, U⟩ =>
        ⟨by rw [e1, mt], by rw [e2, mt], by rw [e3, mt], kt'.trans (k.mono fun r hr => by
          simp at hr; simp [hr]), by rw [← mt]; exact U⟩
    · have hne : i ≠ j + 1 := of_decide_eq_false he
      exact WP.mono (storeEntry_ok hL hA j (by omega_using [hi, hne]) (by omega_using [hj]) hst ((kt.gpr _ (by decide)).trans h19))
        fun u ⟨e1, e2, e3, k, U⟩ => ⟨by rw [e1, mt], by rw [e2, mt], by rw [e3, mt], kt'.trans k,
          by rw [← mt]; exact U⟩

/-- An entry of the table: `D = E + P` (`[m + 1]P`), `E = D`, and `D` into
entry `m + 1`. -/
theorem buildStep_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    (hP : onCurve C P = true) {s₀ : State} (hF : WinFixed K C base s₀ P k) {m : Nat} (h1 : 1 ≤ m)
    (h7 : m ≤ 7) {s : State} (hI : BuildInvE K C base size P s₀ m s) :
    WP isa (WinCfg.buildStep K) s fun s' =>
      BuildInvE K C base size P s₀ (m + 1) s' ∧ s'.gpr .x19 = BitVec.ofNat 64 (8 - (m + 1)) := by
  have hn := hI.inv.scr.nowrap
  rw [WinCfg.buildStep]
  refine WP.seq (WP.mono (decCounter_ok s (j := 8 - m) (by omega_using [h7]) (by omega_using []) hI.x19) fun s₁ ⟨x₁, k₁⟩ => ?_)
  have hs₁ := hI.inv.scr.of_keeps k₁ (by decide)
  have m₁ : s₁.mem = s.mem := k₁.mem
  have tb : tmv C K.M.n base s₁ K.S.b3 = Fin.ofNat C.p C.b := by
    show toM _ _ _ = _; rw [m₁, hL.ro_val hI.inv.unch hn (by simp [winRo])]; exact hF.b
  have ro_lt : ∀ x ∈ winRo K, wordsVal s₁.mem base x K.M.n < C.p := fun x hx => by
    rw [m₁, hL.ro_val hI.inv.unch hn hx]; exact hF.ro_lt x hx
  have tP : ∀ x ∈ [K.P.x, K.P.y, K.P.z], tmv C K.M.n base s₁ x = tmv C K.M.n base s₀ x := by
    intro x hx; show toM _ _ _ = toM _ _ _; rw [m₁, hL.ro_val hI.inv.unch hn (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [winRo])]
  have hLo : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.E K.P, x ∈ winRo K ++ winOther K := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_right _ (List.mem_append_right _ hx)
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> win_in
  have hO : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.E K.P, x ∈ winSlots K := fun x hx =>
    List.mem_append_left _ (hLo x hx)
  have hlt : ∀ x ∈ rcbR K.S K.E K.P, wordsVal s₁.mem base x K.M.n < C.p := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ro_lt _ (by simp [winRo])
    · exact ro_lt _ (by simp [winRo])
    · rw [m₁]; exact hI.lt _ (by simp)
    · rw [m₁]; exact hI.lt _ (by simp)
    · rw [m₁]; exact hI.lt _ (by simp)
    · exact ro_lt _ (by simp [winRo])
    · exact ro_lt _ (by simp [winRo])
    · exact ro_lt _ (by simp [winRo])
  have hI₁ : Inv K.M base size C.p (· ∈ winSlots K) (rcbR K.S K.E K.P) (tmv C K.M.n base s₁) s₁ :=
    ⟨hs₁, by rw [m₁]; exact hI.inv.mod, fun x hx => hO x (List.mem_append_right _ hx), hlt,
      fun _ _ => rfl⟩
  have W := rcb3_ok hL.lay hA.al hp hL.rcbApart_EP hO (hA.low hLo) hI₁ (fun x hx => hx)
  refine WP.seq (WP.mono W fun s₂ ⟨k₂, I₂, v₂⟩ => ?_)
  -- `D` is `[m + 1]P`.
  have hox : K.D.x ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.E K.P := by simp
  have hoy : K.D.y ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.E K.P := by simp
  have hoz : K.D.z ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.E K.P := by simp
  have dlt : ∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal s₂.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact I₂.lt _ hox
    · exact I₂.lt _ hoy
    · exact I₂.lt _ hoz
  have dRep : Rep C (tmv C K.M.n base s₂ K.D.x) (tmv C K.M.n base s₂ K.D.y) (tmv C K.M.n base s₂ K.D.z)
      (mul (m + 1) P) := by
    have hS : (tmv C K.M.n base s₂ K.D.x, tmv C K.M.n base s₂ K.D.y, tmv C K.M.n base s₂ K.D.z) =
        VG.Proof.Weierstrass.rcbAdd3 (tmv C K.M.n base s₁ K.S.b3)
          (tmv C K.M.n base s₁ K.E.x) (tmv C K.M.n base s₁ K.E.y) (tmv C K.M.n base s₁ K.E.z)
          (tmv C K.M.n base s₁ K.P.x) (tmv C K.M.n base s₁ K.P.y) (tmv C K.M.n base s₁ K.P.z) := by
      rw [← v₂]
      show (toM _ _ _, toM _ _ _, toM _ _ _) = _
      rw [I₂.val _ hox, I₂.val _ hoy, I₂.val _ hoz]
    rw [tb, tP K.P.x (by simp), tP K.P.y (by simp), tP K.P.z (by simp)] at hS
    have hE : Rep C (tmv C K.M.n base s₁ K.E.x) (tmv C K.M.n base s₁ K.E.y) (tmv C K.M.n base s₁ K.E.z)
        (mul m P) := by
      show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _; rw [m₁]; exact hI.rep
    have hPr : Rep C (tmv C K.M.n base s₀ K.P.x) (tmv C K.M.n base s₀ K.P.y)
        (tmv C K.M.n base s₀ K.P.z) (mul 1 P) := by rw [mul_one_pt]; exact hF.pt
    have hR := hC.add3 hM3 (hC.onCurve_mul hP m) (hC.onCurve_mul hP 1) hE hPr hS.symm
    rw [hC.add_mul_mul hP] at hR
    exact hR
  have hs₂ := k₂.scr hs₁
  have U₂ := k₂.unch
  -- `E = D`.
  have eO : ∀ y ∈ [K.E.x, K.E.y, K.E.z, K.D.x, K.D.y, K.D.z], y ∈ winOther K := by
    intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> win_in
  obtain ⟨-, -, -, -, exy, exz, eyz, hED, -, -⟩ := hL.other_ne
  have hEd : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ∉ [K.D.x, K.D.y, K.D.z] := by
    intro x hx hd
    refine hED x hx (List.mem_cons_of_mem _ ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> simp [rcbW]
  refine WP.seq (WP.mono (copyPt_ok hs₂ (o := K.E) (a := K.D) (n := K.M.n)
    (fun x hx => hL.lay.le x (winOther_mem (eO x hx))) (fun x hx => hA.sl x (winOther_mem (eO x hx)))
    (fun x hx y hy hxy => hL.apart₂ (winOther_ws K x (eO x (List.mem_append_left [K.D.x, K.D.y, K.D.z] hx)))
      (winOther_ws K y (eO y hy)) hxy) hEd ⟨exy, exz, eyz⟩) fun s₃ ⟨e1, e2, e3, k₃, U₃⟩ => ?_)
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have x₃ : s₃.gpr .x19 = BitVec.ofNat 64 (7 - m) := by
    rw [k₃.gpr _ (by decide), k₂.gpr _ (x19_not_clob _), x₁]; congr 1; omega_using []
  -- `D` into entry `m + 1`.
  refine WP.mono (storeEntry_ok hL hA (i := 7 - m) 6 (by omega_using [h1]) (Nat.le_refl _) hs₃ x₃)
    fun s₄ ⟨f1, f2, f3, k₄, U₄⟩ => ?_
  rw [show 8 - (7 - m) = m + 1 by omega_using [h7]] at f1 f2 f3 U₄
  have b64 : ∀ x ∈ winSlots K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := hL.lay.le x hx; omega_using [hn, this]
  have sT := tblPt_slots K (m := m + 1) (by omega_using []) (by omega_using [h7])
  -- `D` is kept by the copy into `E`, and `E` by the store.
  have dE : ∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal s₃.mem base x K.M.n = wordsVal s₂.mem base x K.M.n := by
    intro x hx
    refine U₃.wordsVal (fun w hw => ?_) (b64 x (winOther_mem (eO x (List.mem_append_right [K.E.x, K.E.y, K.E.z] hx))))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    have hxE : ∀ y ∈ [K.E.x, K.E.y, K.E.z], x ≠ y := fun y hy hxy => hEd y hy (hxy ▸ hx)
    rcases hw with rfl | rfl | rfl <;> dsimp only <;>
      exact hL.apart₂ (winOther_ws K x (eO x (List.mem_append_right [K.E.x, K.E.y, K.E.z] hx)))
        (winOther_ws K _ (eO _ (by simp))) (hxE _ (by simp))
  have tE : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s₄.mem base x K.M.n = wordsVal s₃.mem base x K.M.n := by
    intro x hx
    refine U₄.wordsVal (fun w hw => ?_) (b64 x (winOther_mem (eO x (List.mem_append_left [K.D.x, K.D.y, K.D.z] hx))))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    have hxo : x ∈ winRo K ++ winOther K := List.mem_append_right _ (eO x (List.mem_append_left [K.D.x, K.D.y, K.D.z] hx))
    rcases hw with rfl | rfl | rfl <;> dsimp only
    · obtain ⟨i, hi, e, -, -⟩ := tblPt_mem K (m := m + 1) (by omega_using []) (by omega_using [h7]) _ (by simp : (K.tblPt (m + 1)).x ∈ _)
      rw [e]; exact hL.tbl_apart hxo hi
    · obtain ⟨i, hi, e, -, -⟩ := tblPt_mem K (m := m + 1) (by omega_using []) (by omega_using [h7]) _ (by simp : (K.tblPt (m + 1)).y ∈ _)
      rw [e]; exact hL.tbl_apart hxo hi
    · obtain ⟨i, hi, e, -, -⟩ := tblPt_mem K (m := m + 1) (by omega_using []) (by omega_using [h7]) _ (by simp : (K.tblPt (m + 1)).z ∈ _)
      rw [e]; exact hL.tbl_apart hxo hi
  have vEx : wordsVal s₄.mem base K.E.x K.M.n = wordsVal s₂.mem base K.D.x K.M.n := by
    rw [tE _ (by simp), e1]
  have vEy : wordsVal s₄.mem base K.E.y K.M.n = wordsVal s₂.mem base K.D.y K.M.n := by
    rw [tE _ (by simp), e2]
  have vEz : wordsVal s₄.mem base K.E.z K.M.n = wordsVal s₂.mem base K.D.z K.M.n := by
    rw [tE _ (by simp), e3]
  have vTx : wordsVal s₄.mem base (K.tblPt (m + 1)).x K.M.n = wordsVal s₂.mem base K.D.x K.M.n := by
    rw [f1, dE _ (by simp)]
  have vTy : wordsVal s₄.mem base (K.tblPt (m + 1)).y K.M.n = wordsVal s₂.mem base K.D.y K.M.n := by
    rw [f2, dE _ (by simp)]
  have vTz : wordsVal s₄.mem base (K.tblPt (m + 1)).z K.M.n = wordsVal s₂.mem base K.D.z K.M.n := by
    rw [f3, dE _ (by simp)]
  -- What the step writes: the addition's slots and temporary area, `E` and the entry.
  have UU := U₂.trans (U₃.trans U₄)
  have L2 : ∀ w ∈ (rcbW K.S K.D).map (·, 8 * K.M.n) ++ [(K.M.tmp, 8 * K.M.n)],
      w = (K.M.tmp, 8 * K.M.n) ∨ ∃ y ∈ winOther K, w = (y, 8 * K.M.n) := by
    intro w hw
    rcases List.mem_append.mp hw with h | h
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
      exact Or.inr ⟨y, List.mem_append_right _ hy, rfl⟩
    · exact Or.inl (List.mem_singleton.mp h)
  have L3 : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)],
      ∃ y ∈ winOther K, w = (y, 8 * K.M.n) := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact ⟨_, by win_in, rfl⟩
    · exact ⟨_, by win_in, rfl⟩
    · exact ⟨_, by win_in, rfl⟩
  have L4 : ∀ w ∈ [((K.tblPt (m + 1)).x, 8 * K.M.n), ((K.tblPt (m + 1)).y, 8 * K.M.n),
      ((K.tblPt (m + 1)).z, 8 * K.M.n)], ∃ y ∈ [(K.tblPt (m + 1)).x, (K.tblPt (m + 1)).y,
        (K.tblPt (m + 1)).z], w = (y, 8 * K.M.n) := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact ⟨_, by simp, rfl⟩
    · exact ⟨_, by simp, rfl⟩
    · exact ⟨_, by simp, rfl⟩
  have split : ∀ {Q : Nat × Nat → Prop}, (w : Nat × Nat) →
      w ∈ (rcbW K.S K.D).map (·, 8 * K.M.n) ++ [(K.M.tmp, 8 * K.M.n)] ++
        ([(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)] ++
          [((K.tblPt (m + 1)).x, 8 * K.M.n), ((K.tblPt (m + 1)).y, 8 * K.M.n),
            ((K.tblPt (m + 1)).z, 8 * K.M.n)]) →
      Q (K.M.tmp, 8 * K.M.n) → (∀ y ∈ winOther K, Q (y, 8 * K.M.n)) →
      (∀ y ∈ [(K.tblPt (m + 1)).x, (K.tblPt (m + 1)).y, (K.tblPt (m + 1)).z], Q (y, 8 * K.M.n)) → Q w := by
    intro Q w hw qt qo qT
    rcases List.mem_append.mp hw with h | h
    · rcases L2 w h with rfl | ⟨y, hy, rfl⟩
      · exact qt
      · exact qo y hy
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨y, hy, rfl⟩ := L3 w h; exact qo y hy
      · obtain ⟨y, hy, rfl⟩ := L4 w h; exact qT y hy
  have U : Unch base (winW K) s.mem s₄.mem := by
    rw [← m₁]
    refine UU.mono fun w hw => split w hw (by simp [winW])
      (fun y hy => by simp only [winW, List.mem_append, List.mem_map]; exact Or.inl ⟨y, winOther_ws K y hy, rfl⟩)
      (fun y hy => by simp only [winW, List.mem_append, List.mem_map]; exact Or.inl ⟨y, (sT y hy).2, rfl⟩)
  have keep : KeepRegs (.x19 :: clob K.M.n) s s₄ := by
    have c1 : ∀ r ∈ [Reg.x1], r ∈ Reg.x19 :: clob K.M.n := by intro r hr; simp at hr; subst hr; simp [clob]
    have c2 : ∀ r ∈ [Reg.x1, Reg.x2], r ∈ Reg.x19 :: clob K.M.n := by
      intro r hr; simp at hr; rcases hr with rfl | rfl <;> simp [clob]
    exact (((Keeps.regs k₁).mono fun r hr => by simp at hr; simp [hr]).trans
      ((⟨fun r hr => k₂.gpr r fun h => hr (List.mem_cons_of_mem _ h), k₂.rd, k₂.wr, k₂.sp⟩ :
        KeepRegs (.x19 :: clob K.M.n) s₁ s₂).trans ((k₃.mono c1).trans (k₄.mono c2))))
  refine ⟨⟨⟨hs₃.of_keepRegs k₄ (by decide), hI.inv.keep.trans keep,
    (hI.inv.unch.trans U).mono fun w hw => by rcases List.mem_append.mp hw with h | h <;> exact h,
    hI.inv.mod.unch U (winW_mo hL hI.inv.mod) hn, fun j hj1 hjm => ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · rcases Nat.lt_or_ge j (m + 1) with hj | hj
    · -- An entry built before keeps its numbers.
      have Tj := hI.inv.tbl j hj1 (by omega_using [hj])
      have sj := tblPt_slots K (m := j) hj1 (by omega_using [h7, hj])
      have e : ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
          wordsVal s₄.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
        intro x hx
        rw [← m₁]
        obtain ⟨i, hi, hxi, -, -⟩ := tblPt_mem K hj1 (by omega_using [h7, hj]) x hx
        refine UU.wordsVal (fun w hw => split (Q := fun w =>
            x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x) w hw
          (by rw [hxi]; exact hL.lay.tmp _ (by
            simp only [winSlots, List.mem_append]; exact Or.inr (winTbl_mem K hi)))
          (fun y hy => by rw [hxi]; exact (hL.tbl_apart (List.mem_append_right _ hy) hi).symm)
          (fun y hy => tbl_apart_entry (K := K) hj1 (by omega_using [h7, hj]) (by omega_using []) (by omega_using [h7]) (by omega_using [hj]) x hx
            y hy)) (b64 _ (sj _ hx).1)
      refine ⟨fun x hx => by rw [e x hx]; exact Tj.1 x hx, ?_⟩
      have ex : ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
          tmv C K.M.n base s₄ x = tmv C K.M.n base s x := fun x hx => by
        show toM _ _ _ = toM _ _ _; rw [e x hx]
      rw [ex _ (by simp), ex _ (by simp), ex _ (by simp)]
      exact Tj.2
    · obtain rfl : j = m + 1 := by omega_using [hjm, hj]
      refine ⟨fun x hx => ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · rw [vTx]; exact dlt _ (by simp)
        · rw [vTy]; exact dlt _ (by simp)
        · rw [vTz]; exact dlt _ (by simp)
      · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
        rw [vTx, vTy, vTz]; exact dRep
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [vEx]; exact dlt _ (by simp)
    · rw [vEy]; exact dlt _ (by simp)
    · rw [vEz]; exact dlt _ (by simp)
  · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [vEx, vEy, vEz]; exact dRep
  · rw [k₄.gpr _ (by decide), x₃]; congr 1; omega_using []
  · rw [k₄.gpr _ (by decide), x₃]; congr 1; omega_using []

/-- The table `[1 … 8]P`. -/
theorem build_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    (hP : onCurve C P = true) {s : State} (hs : Scr s base size) (hM : ModOkA K.M size C.p s.mem base)
    (hF : WinFixed K C base s P k) :
    WP isa (WinCfg.build K) s (BuildInv K C base size P s 8) := by
  have hn := hs.nowrap
  have s1 := tblPt_slots K (m := 1) (Nat.le_refl _) (by omega_using [])
  have pRo : ∀ x ∈ [K.P.x, K.P.y, K.P.z], x ∈ winRo K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [winRo]
  have eO : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ∈ winOther K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> win_in
  have b64 : ∀ x ∈ winSlots K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := hL.lay.le x hx; omega_using [hn, this]
  -- `[1]P = P`.
  have tP : ∀ x ∈ [(K.tblPt 1).x, (K.tblPt 1).y, (K.tblPt 1).z], ∀ y ∈ [K.P.x, K.P.y, K.P.z],
      x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := by
    intro x hx y hy
    obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K (m := 1) (Nat.le_refl _) (by omega_using []) x hx
    exact (hL.tbl_apart (List.mem_append_left _ (pRo y hy)) hi).symm
  have ne1 : (K.tblPt 1).x ≠ (K.tblPt 1).y ∧ (K.tblPt 1).x ≠ (K.tblPt 1).z ∧
      (K.tblPt 1).y ≠ (K.tblPt 1).z := by
    rw [tblPt_x, tblPt_y, tblPt_z]
    exact ⟨hL.tbl_ne₂ (by omega_using []), hL.tbl_ne₂ (by omega_using []), hL.tbl_ne₂ (by omega_using [])⟩
  have slP : ∀ x ∈ [(K.tblPt 1).x, (K.tblPt 1).y, (K.tblPt 1).z, K.P.x, K.P.y, K.P.z], x ∈ winSlots K := by
    intro x hx
    rcases List.mem_append.mp (show x ∈ [(K.tblPt 1).x, (K.tblPt 1).y, (K.tblPt 1).z] ++
      [K.P.x, K.P.y, K.P.z] from hx) with h | h
    · exact (s1 x h).1
    · exact winRo_slots K x (pRo x h)
  rw [WinCfg.build]
  refine WP.seq ?_
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (copyPt_ok hs (o := K.tblPt 1) (a := K.P) (n := K.M.n)
    (fun x hx => hL.lay.le x (slP x hx)) (fun x hx => hA.sl x (slP x hx))
    (fun x hx y hy hxy => by
      rcases List.mem_append.mp (show y ∈ [(K.tblPt 1).x, (K.tblPt 1).y, (K.tblPt 1).z] ++
        [K.P.x, K.P.y, K.P.z] from hy) with h | h
      · exact hL.apart₂ (s1 x hx).2 (s1 y h).2 hxy
      · exact tP x hx y h)
    (fun x hx h => by have := tP x hx x h; have := hL.n0; omega) ne1) fun s₁ ⟨a1, a2, a3, k₁, U₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  -- `E = P`.
  obtain ⟨-, -, -, -, exy, exz, eyz, -⟩ := hL.other_ne
  have eP : ∀ x ∈ [K.E.x, K.E.y, K.E.z], ∀ y ∈ [K.P.x, K.P.y, K.P.z], x ≠ y := fun x hx y hy h =>
    hL.ro y (pRo y hy) (h ▸ eO x hx)
  have slE : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.P.x, K.P.y, K.P.z], x ∈ winSlots K := by
    intro x hx
    rcases List.mem_append.mp (show x ∈ [K.E.x, K.E.y, K.E.z] ++ [K.P.x, K.P.y, K.P.z] from hx) with h | h
    · exact winOther_mem (eO x h)
    · exact winRo_slots K x (pRo x h)
  rw [WP.block_append_iff]
  refine WP.mono (copyPt_ok hs₁ (o := K.E) (a := K.P) (n := K.M.n)
    (fun x hx => hL.lay.le x (slE x hx)) (fun x hx => hA.sl x (slE x hx))
    (fun x hx y hy hxy => hL.lay.apart x y (slE x (List.mem_append_left [K.P.x, K.P.y, K.P.z] hx)) (slE y hy) hxy)
    (fun x hx h => eP x hx x h rfl) ⟨exy, exz, eyz⟩) fun s₂ ⟨c1, c2, c3, k₂, U₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (setCounter_ok s₂ (j := 7) (by decide)) fun s₃ ⟨x₃, k₃⟩ => ?_
  -- The invariant for `[1]P`.
  have U : Unch base (winW K) s.mem s₃.mem := by
    rw [k₃.mem]
    refine (U₁.trans U₂).mono fun w hw => ?_
    rcases List.mem_append.mp hw with h | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      simp only [winW, List.mem_append, List.mem_map]
      rcases h with rfl | rfl | rfl
      · exact Or.inl ⟨_, (s1 _ (by simp)).2, rfl⟩
      · exact Or.inl ⟨_, (s1 _ (by simp)).2, rfl⟩
      · exact Or.inl ⟨_, (s1 _ (by simp)).2, rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      simp only [winW, List.mem_append, List.mem_map]
      rcases h with rfl | rfl | rfl
      · exact Or.inl ⟨_, winOther_ws K _ (eO _ (by simp)), rfl⟩
      · exact Or.inl ⟨_, winOther_ws K _ (eO _ (by simp)), rfl⟩
      · exact Or.inl ⟨_, winOther_ws K _ (eO _ (by simp)), rfl⟩
  have m₃ : s₃.mem = s₂.mem := k₃.mem
  -- `[1]P` is kept by the copy into `E`.
  have kT : ∀ x ∈ [(K.tblPt 1).x, (K.tblPt 1).y, (K.tblPt 1).z],
      wordsVal s₃.mem base x K.M.n = wordsVal s₁.mem base x K.M.n := by
    intro x hx
    rw [m₃]
    refine U₂.wordsVal (fun w hw => ?_) (b64 x (s1 x hx).1)
    obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K (m := 1) (Nat.le_refl _) (by omega_using []) x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact (hL.tbl_apart (x := K.E.x) (List.mem_append_right _ (by win_in)) hi).symm
    · exact (hL.tbl_apart (x := K.E.y) (List.mem_append_right _ (by win_in)) hi).symm
    · exact (hL.tbl_apart (x := K.E.z) (List.mem_append_right _ (by win_in)) hi).symm
  have kP : ∀ x ∈ [K.P.x, K.P.y, K.P.z], wordsVal s₁.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
    intro x hx
    refine U₁.wordsVal (fun w hw => ?_) (b64 x (winRo_slots K x (pRo x hx)))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;>
      exact (tP _ (by simp) x hx).symm
  have c1' : ∀ r ∈ [Reg.x1], r ∈ Reg.x19 :: clob K.M.n := by intro r hr; simp at hr; subst hr; simp [clob]
  have I₁ : BuildInvE K C base size P s 1 s₃ := by
    refine ⟨⟨hs₂.of_keeps k₃ (by decide), ((k₁.mono c1').trans (k₂.mono c1')).trans
      ((Keeps.regs k₃).mono fun r hr => by simp at hr; simp [hr]), U, hM.unch U (winW_mo hL hM) hn,
      fun j hj1 hj => ?_⟩, fun x hx => ?_, ?_, by rw [x₃]⟩
    · obtain rfl : j = 1 := by omega_using [hj1, hj]
      refine ⟨fun x hx => ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · rw [kT _ (by simp), a1]; exact hF.ro_lt _ (by simp [winRo])
        · rw [kT _ (by simp), a2]; exact hF.ro_lt _ (by simp [winRo])
        · rw [kT _ (by simp), a3]; exact hF.ro_lt _ (by simp [winRo])
      · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
        rw [kT _ (by simp), kT _ (by simp), kT _ (by simp), a1, a2, a3, mul_one_pt]
        exact hF.pt
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rw [m₃]
      rcases hx with rfl | rfl | rfl
      · rw [c1, kP _ (by simp)]; exact hF.ro_lt _ (by simp [winRo])
      · rw [c2, kP _ (by simp)]; exact hF.ro_lt _ (by simp [winRo])
      · rw [c3, kP _ (by simp)]; exact hF.ro_lt _ (by simp [winRo])
    · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
      rw [m₃, c1, c2, c3, kP _ (by simp), kP _ (by simp), kP _ (by simp), mul_one_pt]
      exact hF.pt
  exact countLoop_ok (Inv := fun j t => BuildInvE K C base size P s (8 - j) t) (n := 7) (by decide)
    (fun j t h1 h2 hi => WP.mono (buildStep_ok hL hA hp hC hM3 hP hF (m := 8 - j) (by omega_using [h2]) (by omega_using [h1]) hi)
      fun u ⟨I, x⟩ => ⟨by rw [show 8 - (j - 1) = 8 - j + 1 by omega_using [h1, h2]]; exact I,
        by rw [x]; congr 1; omega_using [h2]⟩)
    (fun t hi => hi.inv) (by decide) I₁

end VG.Proof.Weierstrass.AArch64
