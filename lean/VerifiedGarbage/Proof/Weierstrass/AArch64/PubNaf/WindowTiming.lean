module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.TableTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Digit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.DigitTiming
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.AddTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTableTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.CacheBuild
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.TableCoZ
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Table
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ed25519.AArch64.Mem

/-!
# Timing of the public NAF multiplication

Two runs multiplying the same point by the same scalar leak the same trace
(`window_relCT`): the table's construction (`table_relCT`), the top digit and
every iteration (`digit_relCT`, `stepRaw_relCT`) branch and address only by
the values of the point and the digits, which both runs share, and the
conversion to projective coordinates is constant time.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.PubNaf

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

/-- The pieces of the multiplication whose timing taint tracking checks. -/
structure WindowChecks (K : WinCfg) : Prop where
  table : TableChecks K
  cache : FieldCT (cache K)
  infinity : FieldCT (.block (Jacobian.infinity K K.D))
  counter : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
    (.block [.movz .x .x19 (BitVec.ofNat 16 (64 * K.M.n)) 0])
  step : StepChecks K
  finish : FieldCT (finish K)

theorem digitLive_sub (K : WinCfg) :
    ∀ x ∈ digitLive K, x ∈ [K.D.x, K.D.y, K.D.z] ++ (winRo K ++ winTblSlots K) := by
  intro x hx
  simp only [digitLive, jacCoords, List.mem_append] at hx ⊢
  rcases hx with (hx | hx) | hx
  · exact Or.inr (Or.inl hx)
  · exact Or.inr (Or.inr hx)
  · exact Or.inl hx

/-- The slots read only and the table survive the cache. -/
theorem cache_keep {K : WinCfg} {size : Nat} (hL : NafLay K size) {base : Addr} {m m' : Mem}
    (hU : Unch base (cacheW K ++ loopW K) m m') (hn : base.toNat + size ≤ 2 ^ 64) :
    ∀ x ∈ winRo K ++ winTblSlots K, wordsVal m' base x K.M.n = wordsVal m base x K.M.n := by
  have hW := hL.win
  have hC := hL.cache
  intro x hx
  have hs : x ∈ winSlots K := by
    rcases List.mem_append.mp hx with hx | hx
    · exact winRo_slots K x hx
    · simp only [winSlots, List.mem_append]; exact Or.inr hx
  refine hU.wordsVal (fun w hw => ?_) (by have := hW.lay.le x hs; omega_using [hn, this])
  rcases List.mem_append.mp hw with hw | hw
  · simp only [cacheW, List.mem_singleton] at hw; subst hw; exact Or.inl (hC.slots x hs)
  · rcases List.mem_append.mp hx with hx | hx
    · exact hW.ro_w hx w (loopW_sub K w hw)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have hi' := List.mem_range.mp hi
      simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton] at hw
      rcases hw with ⟨y, hy, rfl⟩ | rfl
      · exact (hW.tbl_apart (List.mem_append_right _ hy) hi').symm
      · exact hW.lay.tmp _ hs

/-- The cache, for the values of the table: the slots read only and the table keep their values. -/
theorem cache_relCT {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : NafLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hc : WindowChecks K) {P : Point C} {E : Nat → Fe C} :
    RelCT isa (fun s t => FieldPair K.M base size C.p (· ∈ winSlots K) (winRo K ++ winTblSlots K) E s t ∧
        OddTbl K C base P 8 s ∧ OddTbl K C base P 8 t)
      (cache K) (FieldPair K.M base size C.p (· ∈ winSlots K) (winRo K ++ winTblSlots K) E) := by
  apply relCT_of_ct hc.cache (fun s t h => h.1.public)
  intro s t ⟨hp', Ts, Tt⟩
  let F := fun (a : State) (b : State) => Scr b base size ∧ KeepRegs (nafClob K.M.n) a b ∧
    Unch base (cacheW K ++ loopW K) a.mem b.mem ∧ ModOkA K.M size C.p b.mem base ∧
    OddTbl K C base P 8 b ∧ CacheUpTo K C base 8 b
  refine ⟨F s, F t, cacheTo_ok hL hp hp'.left.scr hp'.left.mod Ts 8 (Nat.le_refl _),
    cacheTo_ok hL hp hp'.right.scr hp'.right.mod Tt 8 (Nat.le_refl _), fun s' t' fs ft => ?_⟩
  obtain ⟨ss, ks, Us, Ms, -, -⟩ := fs
  obtain ⟨st, kt, Ut, Mt, -, -⟩ := ft
  have inv : ∀ {a b : State}, Inv K.M base size C.p (· ∈ winSlots K) (winRo K ++ winTblSlots K) E a →
      Scr b base size → ModOkA K.M size C.p b.mem base → Unch base (cacheW K ++ loopW K) a.mem b.mem →
      Inv K.M base size C.p (· ∈ winSlots K) (winRo K ++ winTblSlots K) E b :=
    fun ia sb mb ub => ⟨sb, mb, ia.sl, fun x hx => by
      rw [cache_keep hL ub ia.scr.nowrap x hx]; exact ia.lt x hx, fun x hx => by
      rw [cache_keep hL ub ia.scr.nowrap x hx]; exact ia.val x hx⟩
  exact ⟨inv hp'.left ss Ms Us, inv hp'.right st Mt Ut, ks.sp.trans (hp'.sp.trans kt.sp.symm)⟩

theorem loopLive_sub (K : WinCfg) : ∀ x ∈ loopLive K, x ∈ jacCoords K.R ++ digitLive K := by
  intro x hx
  simp only [loopLive, digitLive, List.mem_append] at hx ⊢
  rcases hx with (hx | hx) | hx
  · exact Or.inr (Or.inl (Or.inl hx))
  · exact Or.inr (Or.inl (Or.inr hx))
  · exact Or.inl hx

/-- `D = O` and the count, for the values they set. -/
theorem head_relCT {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : NafLay K size)
    (hone : K.one < C.p) (hc : WindowChecks K) {E : Nat → Fe C} :
    RelCT isa (FieldPair K.M base size C.p (· ∈ winSlots K) (winRo K ++ winTblSlots K) E)
      (.block (Jacobian.infinity K K.D ++
        ([.movz .x .x19 (BitVec.ofNat 16 (64 * K.M.n)) 0] : List Instr)))
      (fun s t => (∃ E', FieldPair K.M base size C.p (· ∈ winSlots K) (digitLive K) E' s t) ∧
        s.gpr .x19 = BitVec.ofNat 64 (64 * K.M.n) ∧ t.gpr .x19 = BitVec.ofNat 64 (64 * K.M.n)) := by
  have hW := hL.win
  have hDs : ∀ x ∈ [K.D.x, K.D.y, K.D.z], x ∈ winSlots K := fun x hx => winOther_mem (D_other K x hx)
  apply RelCT.block_append
  refine RelCT.seq (infinity_relCT hW.lay hL.al.al hDs hone hc.infinity) ?_
  have cnt := keepsField_relCT (M := K.M) (base := base) (size := size) (m := C.p)
    (Sl := (· ∈ winSlots K)) (V := [K.D.x, K.D.y, K.D.z] ++ (winRo K ++ winTblSlots K))
    (E := infinityEnv K.M C.p K.one E K.D) (pub := [.x0]) (rs := [.x19]) (Pre := fun _ => True)
    (Post := fun a => a.gpr .x19 = BitVec.ofNat 64 (64 * K.M.n)) (by decide) hc.counter
    (fun a b hp _ _ => ⟨hp.sp, fun q hq => pub_x0 hp (Taint.mem_ofRegs.mp hq)⟩)
    (fun a _ _ => setCounter_ok a (j := 64 * K.M.n) (by have := hL.n6; omega))
  exact cnt.mono (fun _ _ h => ⟨h, trivial, trivial⟩)
    (fun _ _ ⟨h, a, b⟩ => ⟨⟨_, h.sub (digitLive_sub K)⟩, a, b⟩)

/-- The iterations, from the top digit's result to `[k]P`. -/
theorem loop_relCT {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : NafLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) (hone : K.one < C.p)
    (hc : StepChecks K) {P : Point C} (hP : onCurve C P = true) {s₀ t₀ : State}
    (hF₁ : NafFixed K C base s₀ P k) (hF₂ : NafFixed K C base t₀ P k) :
    RelCT isa (fun s t => (∃ E, FieldPair K.M base size C.p (· ∈ winSlots K) (loopLive K) E s t) ∧
        NInv K C base size P s₀ s (64 * K.M.n) (Naf5.residual k (64 * K.M.n)) ∧
        NInv K C base size P t₀ t (64 * K.M.n) (Naf5.residual k (64 * K.M.n)))
      (.loop (PubNaf.step K) (.nonzero .x .x19))
      (fun s t => (∃ E, FieldPair K.M base size C.p (· ∈ winSlots K) (loopLive K) E s t) ∧
        NInv K C base size P s₀ s 0 (Naf5.residual k 0) ∧
        NInv K C base size P t₀ t 0 (Naf5.residual k 0)) := by
  have h6 := hL.n6
  have hn0 := hL.win.n0
  let I := fun j s t => 1 ≤ j ∧ j ≤ 64 * K.M.n ∧
    ((∃ E, FieldPair K.M base size C.p (· ∈ winSlots K) (loopLive K) E s t) ∧
      NInv K C base size P s₀ s j (Naf5.residual k j) ∧ NInv K C base size P t₀ t j (Naf5.residual k j))
  have step : ∀ j, RelCT isa (I j) (PubNaf.step K) (fun s t =>
      eval (.nonzero .x .x19) s = eval (.nonzero .x .x19) t ∧
      (eval (.nonzero .x .x19) s = some false →
        (∃ E, FieldPair K.M base size C.p (· ∈ winSlots K) (loopLive K) E s t) ∧
        NInv K C base size P s₀ s 0 (Naf5.residual k 0) ∧
        NInv K C base size P t₀ t 0 (Naf5.residual k 0)) ∧
      (eval (.nonzero .x .x19) s = some true → ∃ n < j, I n s t)) := by
    intro j
    by_cases hj : 1 ≤ j
    · by_cases hjn : j ≤ 64 * K.M.n
      · have e : j - 1 + 1 = j := by omega
        have raw := (stepRaw_relCT (base := base) (size := size) hL hp hone hc hF₁ hF₂
          (j := j - 1) (by omega)).mono (P' := I j)
          (fun _ _ h => ⟨h.2.2.1, h.2.2.2.1.st, h.2.2.2.2.st, h.2.2.2.1.cache, h.2.2.2.2.cache,
            by rw [e]; exact h.2.2.2.1.x19, by rw [e]; exact h.2.2.2.2.x19⟩) (fun _ _ h => h)
        have hw := raw.wp (F₁ := fun s => NInv K C base size P s₀ s (j - 1) (Naf5.residual k (j - 1)))
          (F₂ := fun s => NInv K C base size P t₀ s (j - 1) (Naf5.residual k (j - 1)))
          (fun s t h => ⟨step_ok hL hp hC hM3 hone hP hF₁ (j := j - 1) (by omega) (by rw [e]; exact h.2.2.2.1),
            step_ok hL hp hC hM3 hone hP hF₂ (j := j - 1) (by omega) (by rw [e]; exact h.2.2.2.2)⟩)
        refine hw.mono (fun _ _ h => h) ?_
        intro s t ⟨pair, Is, It⟩
        have s19 := Is.x19
        have t19 := It.x19
        refine ⟨by simp only [eval, State.read, s19, t19], fun he => ?_, fun he => ?_⟩
        · have hz : j - 1 = 0 := by
            by_contra hn
            have hb : (BitVec.ofNat 64 (j - 1) != 0) = true := by
              rw [bne_iff_ne]
              intro hh
              have hh' := congrArg BitVec.toNat hh
              simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : j - 1 < 2 ^ 64)] at hh'
              exact hn hh'
            have htrue : eval (.nonzero .x .x19) s = some true := by
              change some (s.read .x .x19 != 0) = some true
              rw [read_x, s19, hb]
            rw [htrue] at he; cases he
          rw [hz] at Is It
          exact ⟨pair, Is, It⟩
        · have hz : j - 1 ≠ 0 := by
            intro hz; simp only [eval, State.read, s19, hz] at he; cases he
          exact ⟨j - 1, by omega, by omega, by omega, pair, Is, It⟩
      · exact RelCT.of_false (fun _ _ h => hjn h.2.1)
    · exact RelCT.of_false (fun _ _ h => hj h.1)
  exact (RelCT.loop I step (64 * K.M.n)).mono (fun _ _ h => ⟨by omega, Nat.le_refl _, h⟩)
    (fun _ _ h => h)

/-- `[k]P`, for a public point `P` and scalar `k`: two runs with the same values of
the slots read only, the same point and the same digits leak the same trace. -/
theorem window_relCT {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : NafLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) (hpn : C.p < 2 ^ (64 * K.M.n))
    (hone_lt : K.one < C.p) (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) (hc : WindowChecks K)
    (hO : PrimeOrder C) (hn17 : 17 ≤ C.n)
    {P : Point C} (hP : onCurve C P = true) (hk : k < 2 ^ (64 * K.M.n)) {E : Nat → Fe C}
    (hz1 : E K.P.z = 1) :
    RelCT isa (fun s t => FieldPair K.M base size C.p (· ∈ winSlots K) (winRo K) E s t ∧
        (Scr s base size ∧ ModOkA K.M size C.p s.mem base ∧ NafFixed K C base s P k) ∧
        (Scr t base size ∧ ModOkA K.M size C.p t.mem base ∧ NafFixed K C base t P k))
      (PubNaf.window K) (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
  have hn0 := hL.win.n0
  intro s t ts tt s' t' ⟨pair, ⟨hs₁, hM₁, hF₁⟩, ⟨hs₂, hM₂, hF₂⟩⟩ es et
  rw [PubNaf.window] at es et
  cases es with | seq e1 es => cases es with | seq ec es => cases es with | seq e2 es =>
  cases es with | seq e3 es => cases es with | seq e4 e5 =>
  cases et with | seq f1 et => cases et with | seq fc et => cases et with | seq f2 et =>
  cases et with | seq f3 et => cases et with | seq f4 f5 =>
  -- The table.
  have hPz : K.P.z ∈ winRo K := by simp [winRo]
  obtain ⟨tr1, E1, p1⟩ := table_relCT hL hp hc.table _ _ _ _ _ _ pair e1 f1
  obtain ⟨_, _, x1, S1⟩ := table_ok hL hp hC hM3 hO hn17 hP hs₁ hM₁ hF₁
    ((pair.left.val _ hPz).trans hz1)
  obtain ⟨_, rfl⟩ := Exec.det e1 x1
  obtain ⟨_, _, y1, T1⟩ := table_ok hL hp hC hM3 hO hn17 hP hs₂ hM₂ hF₂
    ((pair.right.val _ hPz).trans hz1)
  obtain ⟨_, rfl⟩ := Exec.det f1 y1
  -- The cache, from which each run's loop goes on.
  have hsub : ∀ x ∈ winRo K ++ winTblSlots K, x ∈ tblLive K 8 := by
    intro x hx
    simp only [tblLive, winTblSlots, List.mem_append] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl (Or.inl (Or.inl hx))
    · exact Or.inr hx
  have trc := (cache_relCT hL hp hc (P := P) _ _ _ _ _ _ ⟨p1.sub hsub, S1.tbl, T1.tbl⟩ ec fc).1
  have pc := (cache_relCT hL hp hc (P := P) _ _ _ _ _ _ ⟨p1.sub hsub, S1.tbl, T1.tbl⟩ ec fc).2
  have side : ∀ {a₀ a a' : State} {ta : List Leak}, Scr a₀ base size → NafFixed K C base a₀ P k →
      NSt K C base size P a₀ a → Exec isa (cache K) a ta a' →
      NafFixed K C base a' P k ∧ NSt K C base size P a' a' ∧ CacheOk K C base a' ∧
        KeepRegs (nafClob K.M.n) a₀ a' ∧ Unch base (winW K ++ cacheW K) a₀.mem a'.mem := by
    intro a₀ a a' ta h₀ hF S ea
    obtain ⟨_, _, xa, sc, kc, Uc, Mc, Tc, Cc⟩ := cacheTo_ok hL hp S.scr S.mod S.tbl 8 (Nat.le_refl _)
    obtain ⟨_, rfl⟩ := Exec.det ea xa
    have U : Unch base (winW K ++ cacheW K) a₀.mem a'.mem := (S.unch.trans Uc).mono fun w hw => by
      simp only [List.mem_append] at hw ⊢
      rcases hw with hw | hw | hw
      · exact Or.inl hw
      · exact Or.inr hw
      · exact Or.inl (loopW_sub K w hw)
    exact ⟨hF.rebase hL U h₀.nowrap, ⟨sc, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Unch.refl _ _ _, Mc, Tc⟩, Cc,
      S.keep.trans kc, U⟩
  obtain ⟨G₁, Sc1, Cc1, -, -⟩ := side hs₁ hF₁ S1 ec
  obtain ⟨G₂, Tc1, Cc2, -, -⟩ := side hs₂ hF₂ T1 fc
  -- `D = O` and the count.
  obtain ⟨tr2, ⟨E2, p2⟩, a19, b19⟩ := head_relCT hL hone_lt hc _ _ _ _ _ _ pc e2 f2
  obtain ⟨_, _, x2, S2, C2, _, Dl2, DJ2⟩ := head_ok hL hone_lt G₁ Sc1 Cc1 hk
  obtain ⟨_, rfl⟩ := Exec.det e2 x2
  obtain ⟨_, _, y2, T2, D2, _, Dl2', DJ2'⟩ := head_ok hL hone_lt G₂ Tc1 Cc2 hk
  obtain ⟨_, rfl⟩ := Exec.det f2 y2
  -- The top digit.
  obtain ⟨tr3, E3, p3⟩ := digit_relCT hL hp hone_lt hc.step.digit G₁ G₂ (j := 64 * K.M.n)
    (by omega) _ _ _ _ _ _ ⟨p2, S2, T2, C2, D2, a19, b19⟩ e3 f3
  obtain ⟨_, _, x3, I3⟩ := digit_ok hL hp hC hM3 hone_lt hP S2 G₁ C2 (j := 64 * K.M.n) (by omega)
    a19 Dl2 DJ2
  obtain ⟨_, rfl⟩ := Exec.det e3 x3
  obtain ⟨_, _, y3, J3⟩ := digit_ok hL hp hC hM3 hone_lt hP T2 G₂ D2 (j := 64 * K.M.n) (by omega)
    b19 Dl2' DJ2'
  obtain ⟨_, rfl⟩ := Exec.det f3 y3
  -- The iterations.
  obtain ⟨tr4, ⟨E4, p4⟩, I4, J4⟩ := loop_relCT hL hp hC hM3 hone_lt hc.step hP G₁ G₂
    _ _ _ _ _ _ ⟨⟨E3, p3.sub (loopLive_sub K)⟩, I3, J3⟩ e4 f4
  -- Projective coordinates.
  have tr5 := hc.finish _ _ _ _ _ _ trivial trivial
    ⟨p4.sp, fun q hq => pub_x0 p4 (Taint.mem_ofRegs.mp hq)⟩ e5 f5
  obtain ⟨_, _, x5, S5, -, -⟩ := finish_ok hL hp hC hpn hone_lt hone G₁ I4.st I4.rlt I4.r
  obtain ⟨_, rfl⟩ := Exec.det e5 x5
  obtain ⟨_, _, y5, T5, -, -⟩ := finish_ok hL hp hC hpn hone_lt hone G₂ J4.st J4.rlt J4.r
  obtain ⟨_, rfl⟩ := Exec.det f5 y5
  refine ⟨by rw [tr1, trc, tr2, tr3, tr4, tr5], ?_, fun q hq => ?_⟩
  · exact (Exec.rdwr x5).2.2.trans (p4.sp.trans (Exec.rdwr y5).2.2.symm)
  · simp only [Taint.mem_ofRegs, List.mem_singleton] at hq
    subst hq
    exact S5.scr.x0.trans T5.scr.x0.symm

end VG.Proof.Weierstrass.AArch64.PubNaf
