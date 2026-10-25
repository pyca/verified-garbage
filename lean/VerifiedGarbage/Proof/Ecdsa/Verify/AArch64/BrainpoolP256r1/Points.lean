module

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Sum
public import VerifiedGarbage.Proof.Ecdh.AArch64.BrainpoolP256r1.Mul
public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP256r1.AArch64
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Points
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Framework.Block

/-! # brainpoolP256r1 verification: two complete ladders and their sum -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (U V UX UY UZ RM')
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.BrainpoolP256r1
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

abbrev ptsW : List Nat := [EXPP, BM, K, EM, RX, RY, RZ, ACC, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ,
  TX, TY, TZ, TMP, UX, UY, UZ]

/-- A slot apart from what the calls of `vg_brainpoolp256r1_mul` (`qW`) and the slots of `ptsW` write. -/
theorem apart_pts {i : Nat} (hi : i < 45) (hl : i ∉ ptsW)
    (hiA : i ≠ 54 ∧ i ≠ 61 ∧ i ≠ 82 := by first | decide | exact ⟨by omega_arith, by omega_arith⟩) :
    ∀ w ∈ Proof.Ecdh.AArch64.BrainpoolP256r1.qW, brainpoolp256r1.sl i + 8 * brainpoolp256r1.n ≤ w.1 ∨ w.1 + w.2 ≤ brainpoolp256r1.sl i := by
  have s₁ : ∀ x ∈ [EXPP], x ∈ ptsW := by decide
  have s₂ : ∀ x ∈ [BM], x ∈ ptsW := by decide
  have s₃ : ∀ x ∈ [RX, RY, RZ, ACC, PT, TX, TY, TZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP], x ∈ ptsW := by decide
  exact apart_append (apart_slW (fun h => hl (s₁ _ h)) hiA)
    (apart_append (apart_slW (fun h => hl (s₂ _ h)) hiA) (apart_mulWF (.inl (by decide)) hi (fun h => hl (s₃ _ h)) hiA))

theorem points_ok (hc : BaseCfgOk brainpoolp256r1) {s₀ : State} {base : Addr} {g : Reg → BitVec 64} {s : State}
    (hM : Mid brainpoolp256r1 s₀ base g s) {Q₁ Q₂ : Nat → Fe brainpoolp256r1.C → Fe brainpoolp256r1.C → Fe brainpoolp256r1.C → Prop}
    (hC : Law brainpoolp256r1.C)
    (hQ₁ : ∀ X Y Z, Rep brainpoolp256r1.C X Y Z (mul (sv brainpoolp256r1 base s U) (G brainpoolp256r1.C)) → Q₁ 0 X Y Z)
    {P : Point brainpoolp256r1.C} (hP : onCurve brainpoolp256r1.C P = true)
    (hrep : Rep brainpoolp256r1.C (tmv brainpoolp256r1.C brainpoolp256r1.n base s (brainpoolp256r1.sl PX)) (tmv brainpoolp256r1.C brainpoolp256r1.n base s (brainpoolp256r1.sl PY))
      (tmv brainpoolp256r1.C brainpoolp256r1.n base s (brainpoolp256r1.sl ONEP)) P)
    (hQ₂ : ∀ X Y Z, Rep brainpoolp256r1.C X Y Z (mul (sv brainpoolp256r1 base s V) P) → Q₂ 0 X Y Z)
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', Pts brainpoolp256r1 s₀ base g Q₁ Q₂ s' → WP isa rest s' Q) :
    WP isa (.seq (Impl.Ecdsa.Verify.AArch64.BrainpoolP256r1.points) rest) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hM.scr.nowrap
  have hp3 := hc.p_ge
  have F := hM.fixed
  have hmont : ∀ x, brainpoolp256r1.mont x < brainpoolp256r1.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  have sz : ∀ {i}, i < 45 → brainpoolp256r1.sl i + 8 * brainpoolp256r1.n ≤ size := fun hi => sl_le brainpoolp256r1 h7 hi
  have m8 := sl_mod8 brainpoolp256r1
  have ap : ∀ {i j}, i ≠ j → brainpoolp256r1.sl i ≤ brainpoolp256r1.sl j ∨ brainpoolp256r1.sl j + 8 * brainpoolp256r1.n ≤ brainpoolp256r1.sl i := fun h => by
    rcases sl_apart4 brainpoolp256r1 (by decide) h with h | h <;> omega_arith
  unfold Impl.Ecdsa.Verify.AArch64.BrainpoolP256r1.points
  refine WP.seq ?_
  -- `r` to `EM`, and `u` to `K`.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok (size := size) brainpoolp256r1.n hM.scr (o := brainpoolp256r1.sl EM) (a := brainpoolp256r1.sl K)
    (sz (by decide)) (sz (by decide)) (m8 _) (m8 _) (ap (by decide))) fun s₀' ⟨v₀, k₀, O₀⟩ => ?_
  have hs₀ := hM.scr.of_keepRegs k₀ (by decide)
  refine WP.mono (copy_ok (size := size) brainpoolp256r1.n hs₀ (o := brainpoolp256r1.sl K) (a := brainpoolp256r1.sl U)
    (sz (by decide)) (sz (by decide)) (m8 _) (m8 _) (ap (by decide))) fun s₁ ⟨v₁, k₁, O₁⟩ => ?_
  have hs₁ := hs₀.of_keepRegs k₁ (by decide)
  have U₁ : Unch base (slW brainpoolp256r1 [EM, K]) s.mem s₁.mem :=
    (O₀.unch.trans O₁.unch).mono fun w hw => by simpa using hw
  have F₁ := F.unch h7 hn (fixedOk_slW (l := [EM, K]) (by decide)) U₁
  have e₁ : ∀ {i}, i < 45 → i ∉ [EM, K] → sv brainpoolp256r1 base s₁ i = sv brainpoolp256r1 base s i := fun hi hl =>
    sv_unch U₁ h7 hn hi (apart_slW hl)
  have em₁ : sv brainpoolp256r1 base s₁ EM = sv brainpoolp256r1 base s K :=
    (sv_unch (c := brainpoolp256r1) (W := slW brainpoolp256r1 [K]) O₁.unch h7 hn (i := EM) (by decide) (apart_slW (by decide))).trans v₀
  have k₁' : sv brainpoolp256r1 base s₁ K = sv brainpoolp256r1 base s U :=
    v₁.trans (sv_unch (c := brainpoolp256r1) (W := slW brainpoolp256r1 [EM]) O₀.unch h7 hn (i := U) (by decide) (apart_slW (by decide)))
  -- `[u]G`, by a call.
  refine WP.seq (WP.mono (Ecdsa.AArch64.BrainpoolP256r1.gMul_ok hc hC hs₁ F₁) fun s₂ ⟨K₂, U₂, F₂, M₂, L₂, R₂⟩ => ?_)
  rw [k₁'] at R₂
  have q₂ := hQ₁ _ _ _ R₂
  have hs₂ := hs₁.of_keepRegs K₂ (x0_not_powClob h7)
  refine WP.seq (WP.mono (save_ok hc hs₂) fun s₃ ⟨hs₃, k₃, U₃, ux₃, uy₃, uz₃, _, _, _⟩ => ?_)
  have F₃ := F₂.unch h7 hn (fixedOk_slW (by decide)) U₃
  have sub₃ : ∀ i ∈ saveW, i ∈ ptsW := by decide
  have sEK : ∀ x ∈ [EM, K], x ∈ ptsW := by decide
  have hKp : K ∈ ptsW := by decide
  have W₃ : ∀ {i}, i < 45 → i ∉ ptsW → sv brainpoolp256r1 base s₃ i = sv brainpoolp256r1 base s i := fun hi hl =>
    ((sv_unch U₃ h7 hn hi (apart_slW (fun h => hl (sub₃ _ h)))).trans
      (sv_unch (c := brainpoolp256r1) U₂ h7 hn hi (fun w hw => (apart_pts hi hl) w (List.mem_append_right _ hw)))).trans
      (e₁ hi (fun h => hl (sEK _ h)))
  -- `v` to `K`.
  refine WP.seq (WP.mono (copy_ok (size := size) brainpoolp256r1.n hs₃ (o := brainpoolp256r1.sl K) (a := brainpoolp256r1.sl V)
    (sz (by decide)) (sz (by decide)) (m8 _) (m8 _) (ap (by decide))) fun s₄ ⟨v₄', k₄, O₄⟩ => ?_)
  have U₄ : Unch base (slW brainpoolp256r1 [K]) s₃.mem s₄.mem := O₄.unch
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  have F₄ := F₃.unch h7 hn (fixedOk_slW (by decide)) U₄
  have v₄ : ∀ {i}, i < 45 → i ≠ K → sv brainpoolp256r1 base s₄ i = sv brainpoolp256r1 base s₃ i := fun hi hk =>
    sv_unch U₄ h7 hn hi (apart_slW (by simpa using hk))
  have tv₄ : ∀ {i}, i < 45 → i ∉ ptsW → tmv brainpoolp256r1.C brainpoolp256r1.n base s₄ (brainpoolp256r1.sl i) = tmv brainpoolp256r1.C brainpoolp256r1.n base s (brainpoolp256r1.sl i) :=
    fun hi hl => by
      show toM _ _ (sv brainpoolp256r1 base s₄ _) = toM _ _ (sv brainpoolp256r1 base s _)
      rw [v₄ hi (fun h => hl (h ▸ hKp)), W₃ hi hl]
  have k₄' : sv brainpoolp256r1 base s₄ K = sv brainpoolp256r1 base s V := v₄'.trans (W₃ (by decide) (by decide))
  -- `[v]P`, by a call.
  refine WP.seq (WP.mono (Ecdh.AArch64.BrainpoolP256r1.qMul_ok hc hC hP hs₄ F₄
    (by rw [v₄ (by decide) (by decide), W₃ (by decide) (by decide)]; exact hM.px_lt)
    (by rw [v₄ (by decide) (by decide), W₃ (by decide) (by decide)]; exact hM.py_lt)
    (by
      change Rep brainpoolp256r1.C (tmv brainpoolp256r1.C brainpoolp256r1.n base s₄ (brainpoolp256r1.sl PX))
        (tmv brainpoolp256r1.C brainpoolp256r1.n base s₄ (brainpoolp256r1.sl PY))
        (tmv brainpoolp256r1.C brainpoolp256r1.n base s₄ (brainpoolp256r1.sl ONEP)) P
      rw [tv₄ (by decide) (by decide), tv₄ (by decide) (by decide), tv₄ (by decide) (by decide)]
      exact hrep))
    fun s₅ ⟨K₅, U₅, F₅, M₅, L₅, R₅, B₅⟩ => ?_)
  rw [k₄'] at R₅
  have hs₅ := hs₄.of_keepRegs K₅ (x0_not_powClob h7)
  have v₅ : ∀ {i}, i < 45 → i ∉ ptsW → sv brainpoolp256r1 base s₅ i = sv brainpoolp256r1 base s₄ i := fun hi hl =>
    sv_unch U₅ h7 hn hi (apart_pts hi hl)
  have q₅ := hQ₂ _ _ _ R₅
  have u₅ : ∀ {i}, i ∈ [UX, UY, UZ] → sv brainpoolp256r1 base s₅ i = sv brainpoolp256r1 base s₃ i := fun {i} hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
      exact (sv_unch U₅ h7 hn (by decide) (apart_append (apart_slW (by decide))
        (apart_append (apart_slW (by decide)) (apart_mulWF (.inl (by decide)) (by decide) (by decide))))).trans
        (v₄ (by decide) (by decide))
  refine WP.seq (WP.mono (sum_ok hc hs₅ M₅ (fun i hi => ?_)) fun s₆ ⟨hs₆, rd₆, wr₆, U₆, M₆, rz₆, t₆⟩ => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change wordsVal s₅.mem base (brainpoolp256r1.sl AP) brainpoolp256r1.n < _
      rw [F₅.ap]; exact hmont _
    · rw [B₅]; exact hmont _
    · rw [u₅ (by decide), ux₃]; exact L₂ _ (by simp)
    · rw [u₅ (by decide), uy₃]; exact L₂ _ (by simp)
    · rw [u₅ (by decide), uz₃]; exact L₂ _ (by simp)
    · exact L₅ _ (by simp)
    · exact L₅ _ (by simp)
    · exact L₅ _ (by simp)
  have F₆ := F₅.unch h7 hn (fixedOk_slW (by decide)) U₆
  have sub₆ : ∀ i ∈ sumW, i ∈ ptsW := by decide
  have e₆ : ∀ {i}, i < 45 → i ∉ ptsW → sv brainpoolp256r1 base s₆ i = sv brainpoolp256r1 base s₅ i := fun hi hl =>
    sv_unch U₆ h7 hn hi (apart_slW (fun h => hl (sub₆ _ h)))
  -- `r` back to `K`.
  refine WP.mono (copy_ok (size := size) brainpoolp256r1.n hs₆ (o := brainpoolp256r1.sl K) (a := brainpoolp256r1.sl EM)
    (sz (by decide)) (sz (by decide)) (m8 _) (m8 _) (ap (by decide))) fun s₇ ⟨v₇, k₇, O₇⟩ => h s₇ ?_
  have U₇ : Unch base (slW brainpoolp256r1 [K]) s₆.mem s₇.mem := O₇.unch
  have hs₇ := hs₆.of_keepRegs k₇ (by decide)
  have F₇ := F₆.unch h7 hn (fixedOk_slW (by decide)) U₇
  have r₇ : ∀ {i}, i < 45 → i ≠ K → sv brainpoolp256r1 base s₇ i = sv brainpoolp256r1 base s₆ i := fun hi hk =>
    sv_unch U₇ h7 hn hi (apart_slW (by simpa using hk))
  have v₇' : ∀ {i}, i < 45 → i ∉ ptsW → sv brainpoolp256r1 base s₇ i = sv brainpoolp256r1 base s i := fun hi hl =>
    (r₇ hi (fun h => hl (h ▸ hKp))).trans ((e₆ hi hl).trans ((v₅ hi hl).trans
      ((v₄ hi (fun h => hl (h ▸ hKp))).trans (W₃ hi hl))))
  have em₆ : sv brainpoolp256r1 base s₆ EM = sv brainpoolp256r1 base s K := by
    have a₆ := sv_unch (c := brainpoolp256r1) U₆ h7 hn (i := EM) (by decide) (apart_slW (by decide))
    have a₅ := sv_unch (c := brainpoolp256r1) U₅ h7 hn (i := EM) (by decide) (apart_append (apart_slW (by decide))
      (apart_append (apart_slW (by decide)) (apart_mulWF (.inl (by decide)) (by decide) (by decide))))
    have a₃ := sv_unch (c := brainpoolp256r1) U₃ h7 hn (i := EM) (by decide) (apart_slW (by decide))
    have a₂ := sv_unch (c := brainpoolp256r1) U₂ h7 hn (i := EM) (by decide) (apart_append (apart_slW (by decide))
      (apart_mulWF (.inl (by decide)) (by decide) (by decide)))
    exact a₆.trans (a₅.trans ((v₄ (by decide) (by decide)).trans (a₃.trans (a₂.trans em₁))))
  have UW : Unch base ([(bitsAt brainpoolp256r1.n 0, 64 * brainpoolp256r1.n + 8), (brainpoolp256r1.invTmp, 8 * brainpoolp256r1.n)] ++ slW brainpoolp256r1 ptsW) s.mem s₇.mem := by
    refine (U₁.trans (U₂.trans (U₃.trans (U₄.trans (U₅.trans (U₆.trans U₇)))))).mono fun w hw => ?_
    have hB : ∀ {l : List Nat}, (∀ i ∈ l, i ∈ ptsW) → ∀ w ∈ slW brainpoolp256r1 l,
        w ∈ [(bitsAt brainpoolp256r1.n 0, 64 * brainpoolp256r1.n + 8), (brainpoolp256r1.invTmp, 8 * brainpoolp256r1.n)] ++ slW brainpoolp256r1 ptsW := fun hl w hw =>
      List.mem_append_right _ (List.map_subset _ hl hw)
    have hM' : ∀ w ∈ mulWF brainpoolp256r1, w ∈ [(bitsAt brainpoolp256r1.n 0, 64 * brainpoolp256r1.n + 8), (brainpoolp256r1.invTmp, 8 * brainpoolp256r1.n)] ++ slW brainpoolp256r1 ptsW := by
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · exact hB (by decide) w hw
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
        · exact List.mem_append_left _ (List.mem_cons_self ..)
    simp only [List.mem_append] at hw
    rcases hw with hw | (hw | hw) | hw | hw | (hw | hw | hw) | hw | hw
    · exact hB (by decide) w hw
    · exact hB (by decide) w hw
    · exact hM' w (List.mem_append.mpr hw)
    · exact hB (by decide) w hw
    · exact hB (by decide) w hw
    · exact hB (by decide) w hw
    · exact hB (by decide) w hw
    · exact hM' w (List.mem_append.mpr hw)
    · exact hB (by decide) w hw
    · exact hB (by decide) w hw
  have tu : ∀ {i j}, i ∈ [UX, UY, UZ] → j ∈ [RX, RY, RZ] → sv brainpoolp256r1 base s₃ i = sv brainpoolp256r1 base s₂ j →
      tmv brainpoolp256r1.C brainpoolp256r1.n base s₅ (brainpoolp256r1.sl i) = tmv brainpoolp256r1.C brainpoolp256r1.n base s₂ (brainpoolp256r1.sl j) := fun hi _ e => by
    show toM _ _ (sv brainpoolp256r1 base s₅ _) = toM _ _ (sv brainpoolp256r1 base s₂ _)
    rw [u₅ hi, e]
  have ha : tmv brainpoolp256r1.C brainpoolp256r1.n base s₅ (brainpoolp256r1.sl AP) = Fin.ofNat brainpoolp256r1.C.p brainpoolp256r1.C.a := by
    show toM _ _ (wordsVal s₅.mem base (brainpoolp256r1.sl AP) brainpoolp256r1.n) = _
    rw [F₅.ap]; exact toM_cmont hc _
  have hb : tmv brainpoolp256r1.C brainpoolp256r1.n base s₅ (brainpoolp256r1.sl EXPP) = Fin.ofNat brainpoolp256r1.C.p (3 * brainpoolp256r1.C.b) := by
    show toM _ _ (sv brainpoolp256r1 base s₅ EXPP) = _
    rw [B₅]; exact toM_cmont hc _
  have tr₇ : ∀ {i}, i ∈ [RX, RY, RZ] → tmv brainpoolp256r1.C brainpoolp256r1.n base s₇ (brainpoolp256r1.sl i) = tmv brainpoolp256r1.C brainpoolp256r1.n base s₆ (brainpoolp256r1.sl i) :=
    fun {i} hi => by
      show toM _ _ (sv brainpoolp256r1 base s₇ i) = toM _ _ (sv brainpoolp256r1 base s₆ i)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> rw [r₇ (by decide) (by decide)]
  refine ⟨hs₇, by rw [k₇.wr, wr₆, K₅.wr, k₄.wr, k₃.wr, K₂.wr, k₁.wr, k₀.wr, hM.wr],
    by rw [k₇.rd, rd₆, K₅.rd, k₄.rd, k₃.rd, K₂.rd, k₁.rd, k₀.rd, hM.rd], F₇, ?_,
    by rw [v₇' (by decide) (by decide)]; exact hM.rm_lt,
    by rw [v₇' (by decide) (by decide)]; exact hM.rm, by rw [r₇ (by decide) (by decide)]; exact rz₆.1,
    ⟨_, _, _, _, _, _, q₂, q₅, by
      rw [tr₇ (by decide), tr₇ (by decide), tr₇ (by decide), t₆, ha, hb, tu (by decide) (by decide) ux₃,
        tu (by decide) (by decide) uy₃, tu (by decide) (by decide) uz₃]
      rfl⟩,
    ?_, v₇.trans (em₆.trans hM.k), by rw [r₇ (by decide) (by decide)]; exact rz₆.2⟩
  · rw [UW.word (fun w hw => ?_) (by have := sl_le brainpoolp256r1 h7 (i := FLAG) (by decide); omega_arith)]
    · exact hM.flag
    · rcases List.mem_append.mp hw with hw | hw
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · have := sl_below_bits brainpoolp256r1 (i := FLAG) (by decide) 0 0
          exact .inl (by dsimp only; omega_arith)
        · decide
      · exact (apart_slW (c := brainpoolp256r1) (i := FLAG) (l := ptsW) (by decide)) w hw |>.elim
          (fun h => Or.inl (by omega_arith)) (fun h => Or.inr h)
  · refine unch_whole (hM.unch.trans UW) fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw
    · rw [List.mem_singleton.mp hw]; exact Nat.le_refl _
    rcases List.mem_append.mp hw with hw | hw
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · have := bitsAt0_le brainpoolp256r1 h7; show _ ≤ 8192; dsimp only; omega_arith
      · show _ ≤ 8192; decide
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact sl_le brainpoolp256r1 h7 ((show ∀ i ∈ ptsW, i < 45 by decide) i hi)

end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1
