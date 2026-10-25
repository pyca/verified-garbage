module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowSum
import VerifiedGarbage.Proof.Weierstrass.WindowJ
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowTable
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJBuild
import VerifiedGarbage.Proof.Weierstrass.AArch64.WinSelect
import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowEntry
import VerifiedGarbage.Proof.Weierstrass.AArch64.Zero

/-!
# Windows in Jacobian coordinates on AArch64: the last iteration and the loop

The last iteration (`stepLast_ok`): `R = 16 R` in Jacobian coordinates, `R`
into projective coordinates with `Y = 1` where `Z = 0` (`toProjR_ok`), and its
sum with the entry of digit `0` (affine, so projective) by the complete
formulas (`sumStep_ok`). The method (`windowJ_ok`): the table (`build_ok`)
into affine coordinates (`normTbl_ok`), then from `R = O` the iterations of
`winStepJ_ok` for the digits `J - 1` down to `1`, and the last: as on x86-64
(`Proof/Weierstrass/X86_64/WinJLoop.lean`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

/-- `R` and `D`: in the working space and apart, as `copyPt R D` needs. -/
theorem winRDJ {K : WinCfg} {size : Nat} (hL : WinLay K size) :
    (∀ x ∈ [K.R.x, K.R.y, K.R.z, K.D.x, K.D.y, K.D.z], x + 8 * K.M.n ≤ size) ∧
    (∀ x ∈ [K.R.x, K.R.y, K.R.z], ∀ y ∈ [K.R.x, K.R.y, K.R.z, K.D.x, K.D.y, K.D.z], x ≠ y →
      x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x) ∧
    (∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∉ [K.D.x, K.D.y, K.D.z]) ∧
    (K.R.x ≠ K.R.y ∧ K.R.x ≠ K.R.z ∧ K.R.y ≠ K.R.z) := by
  obtain ⟨rxy, rxz, ryz, hRD, -, -, -, -, -, -⟩ := hL.other_ne
  have hw : ∀ z ∈ [K.R.x, K.R.y, K.R.z, K.D.x, K.D.y, K.D.z], z ∈ winWs K := by
    intro z hz
    refine winOther_ws K z ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> win_in
  refine ⟨fun x hx => hL.lay.le x (winWs_slots K x (hw x hx)),
    fun x hx y hy hxy => hL.apart₂ (hw x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h | h <;> simp [h])) (hw y hy) hxy, fun x hx hd => ?_, rxy, rxz, ryz⟩
  refine hRD x hx (List.mem_append_right _ ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl <;> simp [rcbW]

/-- `R` from Jacobian coordinates into projective coordinates, `(XZ : Y : Z³)`,
with `Y` Montgomery's one where `Z = 0`. -/
theorem toProjR_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) {P : Point C}
    {Rp : Fe C → Fe C → Fe C → Point C → Prop} (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {s₀ s : State} (hF : WinFixed K C base s₀ P k)
    (hS : WinStR K C base size Rp P s₀ s) {Q : Point C}
    (hlt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hR : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z) Q) :
    WP isa (WinCfg.toProjR K) s fun s' =>
      WinStR K C base size Rp P s₀ s' ∧ s'.gpr .x19 = s.gpr .x19 ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z) Q := by
  obtain ⟨-, -, ro_lt, hz⟩ := hS.ro_tmv hL hF
  obtain ⟨-, -, aRD⟩ := hL.rcbApart_winJ
  have oR := pt_other (K := K) (p := K.R) (Or.inl rfl)
  have oD := pt_other (K := K) (p := K.D) (Or.inr (Or.inr rfl))
  have sZ : ∀ x ∈ [(WinCfg.zeroPt K).x, (WinCfg.zeroPt K).y, (WinCfg.zeroPt K).z], x ∈ winRo K ++ winOther K := by
    intro x hx
    simp only [WinCfg.zeroPt, List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
    subst hx; win_in
  have w1 := winJ_sl oD (fun x hx => List.mem_append_right _ (oR x hx)) sZ
  have V0 : ∀ x ∈ dblVR K, x ∈ winSlots K ∧ wordsVal s.mem base x K.M.n < C.p := by
    intro x hx
    simp only [dblVR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨winOther_mem (oR _ (by simp)), hlt _ (by simp)⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hlt _ (by simp)⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hlt _ (by simp)⟩
    all_goals exact ⟨by win_in, ro_lt _ (by simp [winRo])⟩
  have I₀ : Inv K.M base size C.p (· ∈ winSlots K) (dblVR K) (tmv C K.M.n base s) s :=
    ⟨hS.scr, hS.mod, fun x hx => (V0 x hx).1, fun x hx => (V0 x hx).2, fun _ _ => rfl⟩
  rw [WinCfg.toProjR, fromJ_eq]
  refine WP.seq (WP.mono (winN_ok hL hA hp fromJN_ok aRD w1.1 w1.2.1 w1.2.2 I₀ (by
      intro x hx
      simp only [rcbR, dblVR, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h | h | h | h | h | h | h <;> simp only [h, true_or, or_true]))
    fun s₁ ⟨k₁, U₁, E₁, I₁, o₁, v₁⟩ => ?_)
  have S₁ := hS.next hL I₁.scr (k₁.mono clob_combClob) U₁
  have v : (E₁ K.D.x, E₁ K.D.y, E₁ K.D.z) = (tmv C K.M.n base s K.R.x * tmv C K.M.n base s K.R.z,
      tmv C K.M.n base s K.R.y + tmv C K.M.n base s K.zero,
      tmv C K.M.n base s K.R.z * tmv C K.M.n base s K.R.z * tmv C K.M.n base s K.R.z) :=
    v₁.trans (fromJN_run _)
  have hDV : ∀ x ∈ [K.D.x, K.D.y, K.D.z], x ∈ [K.D.x, K.D.y, K.D.z] ++ dblVR K := fun x hx =>
    List.mem_append_left _ hx
  have z0 : tmv C K.M.n base s K.zero = 0 := by
    show toM _ _ _ = 0; rw [hz]; exact toM_zero _ _
  obtain ⟨hle, hap, hne, ho⟩ := winRDJ hL
  have hal : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.D.x, K.D.y, K.D.z], x % 8 = 0 := fun x hx =>
    hA.sl x (winOther_mem (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> win_in))
  -- `R = D`.
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (copyPt_ok I₁.scr hle hal hap hne ho) fun s₂ ⟨wx, wy, wz, k₂, U₂⟩ => ?_
  have hs₂ := I₁.scr.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  have hRz : K.R.z + 8 * K.M.n ≤ size := hle _ (by simp)
  have hRy : K.R.y + 8 * K.M.n ≤ size := hle _ (by simp)
  have hRx : K.R.x + 8 * K.M.n ≤ size := hle _ (by simp)
  refine WP.mono (zeroMask_ok hs₂ hL.n0 hRz (hal _ (by simp))) fun s₃ ⟨m₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  refine WP.mono (ySelWords_ok hs₃ K _ m₃ (hal _ (by simp)) K.M.n hRy) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have hn := hs₂.nowrap
  have m₃' : s₃.mem = s₂.mem := k₃.mem
  obtain ⟨rxy, rxz, ryz, -⟩ := hL.other_ne
  have ay : ∀ x ∈ [K.R.x, K.R.z], x ≠ K.R.y → x + 8 * K.M.n ≤ K.R.y ∨ K.R.y + 8 * K.M.n ≤ x :=
    fun x hx h => hap x (by simp at hx ⊢; omega_using [hx]) _ (by simp) h
  have vRx : wordsVal s₄.mem base K.R.x K.M.n = wordsVal s₁.mem base K.D.x K.M.n := by
    rw [O₄.wordsVal (by have := ay _ (by simp) rxy; omega_arith) (by omega_arith), m₃', wx]
  have vRz : wordsVal s₄.mem base K.R.z K.M.n = wordsVal s₁.mem base K.D.z K.M.n := by
    rw [O₄.wordsVal (by have := ay _ (by simp) (Ne.symm ryz); omega_arith) (by omega_arith), m₃', wz]
  have hone' : K.one < 2 ^ (64 * K.M.n) := Nat.lt_trans hone_lt hpn
  have vRy : wordsVal s₄.mem base K.R.y K.M.n =
      if wordsVal s₁.mem base K.D.z K.M.n = 0 then K.one else wordsVal s₁.mem base K.D.y K.M.n := by
    rw [← wz, ← wy]
    by_cases hz0 : wordsVal s₂.mem base K.R.z K.M.n = 0
    · simp only [hz0, ↓reduceIte]
      exact wordsVal_of_shifts _ _ _ _ _ hone' fun j hj => by simp only [e₄ j hj, hz0, ↓reduceIte]; rfl
    · simp only [hz0, ↓reduceIte]
      rw [← m₃']
      exact wordsVal_of_words _ _ _ _ _ _ fun j hj => by simp only [e₄ j hj, hz0, ↓reduceIte]
  -- What changed: `loopW`.
  have inR : ∀ w ∈ [(K.R.x, 8 * K.M.n), (K.R.y, 8 * K.M.n), (K.R.z, 8 * K.M.n)], w ∈ loopW K := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton]
    rcases hw with rfl | rfl | rfl
    · exact Or.inl ⟨_, oR _ (by simp), rfl⟩
    · exact Or.inl ⟨_, oR _ (by simp), rfl⟩
    · exact Or.inl ⟨_, oR _ (by simp), rfl⟩
  have U₄ : Unch base (loopW K) s₁.mem s₄.mem := by
    refine (U₂.trans (m₃' ▸ O₄.unch)).mono fun w hw => ?_
    rcases List.mem_append.mp hw with h | h
    · exact inR w h
    · simp only [List.mem_singleton] at h; rw [h]; exact inR _ (by simp)
  have c : ∀ r ∈ [Reg.x1, .x2, .x4, .x5, .x7, .x9, .x16], r ∈ combClob K.M.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [combClob, clob]
  have kk : KeepRegs (combClob K.M.n) s₁ s₄ :=
    (k₂.mono fun r hr => c r (by simp at hr ⊢; simp [hr])).trans (((Keeps.regs k₃).mono
      fun r hr => c r (by simp at hr ⊢; rcases hr with h | h | h | h | h <;> simp [h])).trans
      (k₄.mono fun r hr => c r (by simp at hr ⊢; rcases hr with h | h <;> simp [h])))
  have S₄ := S₁.next hL (hs₃.of_keepRegs k₄ (by decide)) kk U₄
  -- The values.
  have eD : ∀ x ∈ [K.D.x, K.D.y, K.D.z], toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₁.mem base x K.M.n) = E₁ x :=
    fun x hx => I₁.val x (hDV x hx)
  simp only [Prod.mk.injEq] at v
  obtain ⟨vx, vy, vz⟩ := v
  have hZ : (wordsVal s₁.mem base K.D.z K.M.n = 0) ↔ tmv C K.M.n base s K.R.z = 0 := by
    rw [← toM_eq_zero_iff hp (I₁.lt _ (hDV _ (by simp))), eD _ (by simp), vz]
    constructor
    · intro h; by_contra hn0; exact cube_ne_zero hC hn0 h
    · intro h; rw [h]; simp only [Fin.mul_zero]
  refine ⟨S₄, by rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide),
    k₁.gpr _ (x19_not_clob _)], fun x hx => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [vRx]; exact I₁.lt _ (hDV _ (by simp))
    · rw [vRy]; split
      · exact hone_lt
      · exact I₁.lt _ (hDV _ (by simp))
    · rw [vRz]; exact I₁.lt _ (hDV _ (by simp))
  · have h := InvJ.out hC hR
    show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [vRx, vRy, vRz, toM_iteJ, hone, eD _ (by simp), eD _ (by simp), eD _ (by simp), vx, vy, vz]
    simp only [hZ]
    rw [z0, show ∀ y : Fe C, y + 0 = y from Fin.add_zero]
    exact h

/-- A loop state with the table affine, as one with the table projective. -/
theorem WinStR.toSt {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} {P : Point C} {s₀ s : State}
    (h : WinStR K C base size (RepA C) P s₀ s) : WinSt K C base size P s₀ s :=
  ⟨h.scr, h.keep, h.unch, h.mod, fun j h1 h8 => ⟨(h.tbl j h1 h8).1, (h.tbl j h1 h8).2.1⟩⟩

/-- The last iteration, `x19 = 1` to `0`: adds digit `0` by the complete
formulas, leaving `R` in projective coordinates. -/
theorem stepLast_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C)
    {P : Point C} (hP : onCurve C P = true)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {s₀ : State} (hF : WinFixed K C base s₀ P k)
    (hk8 : 8 * geom K.J ≤ k) {pa : Option (String × Nat)}
    (hpa : AddOk K.M size (· ∈ winSlots K) K.S K.R K.E K.D pa)
    (hr : AddReady base K.M s₀.mem K.S pa) (hfar : AddFar K.M K.S (winW K) pa)
    {s : State} (hI : WinInvJ K C base size k P s₀ s 1)
    {dd : Option (Prog isa × Prog isa)} (hD : DblsOk K C base size dd) {sl : Option (List Instr)}
    (hS : SelOk K size (WinCfg.selOf K sl)) :
    WP isa (WinCfg.stepLast K pa dd sl) s fun s' =>
      WinSt K C base size P s₀ s' ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z)
        (mul (winE k K.J 0) P) := by
  have hJ := hL.J
  rw [WinCfg.stepLast]
  refine WP.seq (WP.mono (decCounter_ok s (Nat.le_refl _) (by decide) hI.x19) fun s₁ ⟨b₁, k₁⟩ => ?_)
  have hS₁ := hI.st.next hL (hI.st.scr.of_keeps k₁ (by decide))
    ((Keeps.regs k₁).mono (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp [combClob]))
    (by rw [k₁.mem]; exact Unch.refl _ _ _)
  have lt₁ : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₁.mem base x K.M.n < C.p := by
    rw [k₁.mem]; exact hI.lt
  have rep₁ : InvJ C (tmv C K.M.n base s₁ K.R.x) (tmv C K.M.n base s₁ K.R.y)
      (tmv C K.M.n base s₁ K.R.z) (mul (winE k K.J 1) P) := by
    have e : ∀ x, tmv C K.M.n base s₁ x = tmv C K.M.n base s x := fun x => by
      show toM _ _ _ = toM _ _ _; rw [k₁.mem]
    rw [e, e, e]; exact hI.rep
  refine WP.seq (WP.mono (quadJ_ok hL hA hp hC hM3 hP hD hF hS₁ (j := 0) (by decide) b₁ lt₁ rep₁)
    fun s₂ ⟨S₂, x₂, l₂, r₂⟩ => ?_)
  refine WP.seq (WP.mono (toProjR_ok hL hA hp hC hpn hone_lt hone hF S₂ l₂ r₂)
    fun s₅ ⟨S₅, x₅, l₅, r₅⟩ => ?_)
  have hx₅ : s₅.gpr .x19 = BitVec.ofNat 64 0 := by rw [x₅, x₂, b₁]
  obtain ⟨-, -, -, hz₅⟩ := S₅.ro_tmv hL hF
  have hbits₅ : ∀ t < 4 * K.J, s₅.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by
      have := hL.bits
      rw [S₅.unch.byte (fun w hw => by have := hL.bits_w w hw; omega_arith) (by have := S₅.scr.nowrap; omega_arith)]
      exact hF.bits t ht
  refine WP.seq (WP.mono (winEntryR_ok hL hA (RepA.infinity hC) RepA.negY (P := P) hpn hone_lt hone
    S₅.scr S₅.mod (i := 0) (by omega_arith) hx₅ hbits₅ hz₅ S₅.tbl hS) fun s₇ E₇ => ?_)
  have hn := S₅.scr.nowrap
  have S₇ := S₅.next hL E₇.scr E₇.keep (E₇.unch.mono (entryW_loopW K))
  have eR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₇.mem base x K.M.n = wordsVal s₅.mem base x K.M.n :=
    fun x hx => E₇.unch.wordsVal (R_apart_entry hL hx) (by
      have := hL.lay.le x (winOther_mem (pt_other (K := K) (p := K.R) (Or.inl rfl) x hx)); omega_arith)
  have lt₇ : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₇.mem base x K.M.n < C.p := fun x hx => by
    rw [eR x hx]; exact l₅ x hx
  have rep₇ : Rep C (tmv C K.M.n base s₇ K.R.x) (tmv C K.M.n base s₇ K.R.y)
      (tmv C K.M.n base s₇ K.R.z) (mul (16 * winE k K.J 1) P) := by
    rw [tmv_congr (eR _ (by simp)), tmv_congr (eR _ (by simp)), tmv_congr (eR _ (by simp))]; exact r₅
  refine WP.mono (sumStep_ok hL hA hp hC hM3 hF S₇.toSt (hC.onCurve_mul hP _) (onCurve_winPt hC hP k 0)
    lt₇ E₇.lt rep₇ E₇.rep.1 hpa hr hfar) fun s₉ ⟨S₉, _, l₉, r₉⟩ => ⟨S₉, l₉, ?_⟩
  have hadd := win_add hC hP (k := k) (J := K.J) (j := 0) hk8 (by omega_arith)
  rw [hadd] at r₉
  exact r₉

/-- A loop whose body takes the invariant from `j` to `j - 1` and leaves
`x4 = j - 2`, run from `n ≥ 2` down to `1`. -/
theorem x4Loop_ok {body : Prog isa} {Inv : Nat → State → Prop} {Q : State → Prop} {n : Nat}
    (hn64 : n < 2 ^ 63)
    (hstep : ∀ j s, 2 ≤ j → j ≤ n → Inv j s →
      WP isa body s fun s' => Inv (j - 1) s' ∧ s'.gpr .x4 = BitVec.ofNat 64 (j - 1) - BitVec.ofNat 64 1)
    (hQ : ∀ s, Inv 1 s → Q s) (hn : 2 ≤ n) {s : State} (hs : Inv n s) :
    WP isa (.loop body (.nonzero .x .x4)) s Q := by
  refine WP.loop (M := isa) (fun j s => 2 ≤ j ∧ j ≤ n ∧ Inv j s) (fun j s ⟨h1, h2, hi⟩ => ?_) n s
    ⟨hn, Nat.le_refl _, hs⟩
  refine WP.mono (hstep j s h1 h2 hi) fun s' ⟨hi', hz⟩ => ?_
  have e : BitVec.ofNat 64 (j - 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (j - 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show j - 1 < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (show j - 2 < 2 ^ 64 by omega_arith),
      show (1 : Nat) % 2 ^ 64 = 1 from rfl, show 2 ^ 64 - 1 + (j - 1) = (j - 2) + 2 ^ 64 by omega_arith,
      Nat.add_mod_right, Nat.mod_eq_of_lt (show j - 2 < 2 ^ 64 by omega_arith)]
  have hx : (s'.read .x .x4 != 0) = decide (j - 1 ≠ 1) := by
    rw [read_x, hz, e]
    by_cases hj : j - 1 = 1
    · rw [show j - 2 = 0 by omega_arith]; simp [hj]
    · rw [decide_eq_true hj, bne_iff_ne, ne_eq]
      intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
      exact hj (by simp at this; omega_arith)
  by_cases hj : j - 1 = 1
  · refine Or.inl ⟨?_, hQ s' (by rw [hj] at hi'; exact hi')⟩
    show some (s'.read .x .x4 != 0) = some false
    rw [hx, hj]; rfl
  · refine Or.inr ⟨?_, j - 1, by omega_arith, by omega_arith, by omega_arith, hi'⟩
    show some (s'.read .x .x4 != 0) = some true
    rw [hx, decide_eq_true hj]

/-- What is read only, and the table of bits, survive writes apart from them. -/
theorem WinFixed.unchJ {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    {P : Point C} {s s' : State} (hF : WinFixed K C base s P k) {W : List (Nat × Nat)}
    (hU : Unch base W s.mem s'.mem) (hn : base.toNat + size ≤ 2 ^ 64)
    (hro : ∀ x ∈ winRo K, ∀ w ∈ W, x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x)
    (hbits : ∀ w ∈ W, K.bits + 4 * K.J ≤ w.1 ∨ w.1 + w.2 ≤ K.bits) : WinFixed K C base s' P k := by
  have e : ∀ x ∈ winRo K, wordsVal s'.mem base x K.M.n = wordsVal s.mem base x K.M.n := fun x hx =>
    hU.wordsVal (hro x hx) (by have := hL.lay.le x (winRo_slots K x hx); omega_arith)
  have hb := hL.bits
  refine ⟨?_, ?_, fun x hx => by rw [e x hx]; exact hF.ro_lt x hx, by rw [e _ (by simp [winRo])]; exact hF.zero,
    ?_, fun t ht => ?_⟩
  · rw [tmv_congr (e _ (by simp [winRo]))]; exact hF.a
  · rw [tmv_congr (e _ (by simp [winRo]))]; exact hF.b
  · rw [tmv_congr (e _ (by simp [winRo])), tmv_congr (e _ (by simp [winRo])), tmv_congr (e _ (by simp [winRo]))]
    exact hF.pt
  · rw [hU.byte (fun w hw => by have := hbits w hw; omega_arith) (by omega_arith)]
    exact hF.bits t ht

/-- `[k - 8 Σ_{i<J} 16^i]P` into `R`, for `8 Σ_{i<J} 16^i ≤ k < 16^J` whose bits
are the table at `K.bits`, by windows in Jacobian coordinates with an affine
table (by the inversion `inv`, writing `IW` and changing `RC`): for `P ≠ O` on
a curve of prime order `n` (`PrimeOrder`), with `16 winE k J 2 + 8 < n` (so
that no addition but the last is of equal or opposite points); only `RC`,
`winW` and `IW` change. -/
theorem windowJ_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C)
    (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true) (hP0 : P ≠ .infinity)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {inv : Prog isa} {RC : List Reg}
    {IW : List (Nat × Nat)} (hI : InvSpecW K C base size inv RC IW)
    (hRC : ∀ r ∈ combClob K.M.n, r ∈ RC) (hx0 : Reg.x0 ∉ RC) {s₀ : State} (hs : Scr s₀ base size)
    (hM : ModOkA K.M size C.p s₀.mem base) (hF₀ : WinFixed K C base s₀ P k) (hk : k < 16 ^ K.J)
    (hk8 : 8 * geom K.J ≤ k) (hJ2 : 2 ≤ K.J) (hb : 16 * winE k K.J 2 + 8 < C.n)
    {pa : Option (String × Nat)} (hpa : AddOk K.M size (· ∈ winSlots K) K.S K.R K.E K.D pa)
    (hr : AddReady base K.M s₀.mem K.S pa) (hfar : AddFar K.M K.S (winW K) pa)
    (hfarI : AddFar K.M K.S IW pa) {dd : Option (Prog isa × Prog isa)} (hD : DblsOk K C base size dd)
    {ma : Option (Prog isa)} (hMa : MaddOk K C base size ma) {sl : Option (List Instr)}
    (hS : SelOk K size (WinCfg.selOf K sl)) :
    WP isa (WinCfg.windowJ K inv pa dd ma sl) s₀ fun s' => KeepRegs RC s₀ s' ∧
      Unch base (winW K ++ IW) s₀.mem s'.mem ∧ ModOkA K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z)
        (mul (k - 8 * geom K.J) P) := by
  have hn := hs.nowrap
  have hJ := hL.J
  have hne : ∀ m, 1 ≤ m → m ≤ 8 → mul m P ≠ .infinity := by
    intro m h1 h8 h
    have h0 : zmul (m : Int) P = zmul 0 P := by
      rw [zmul_natCast, h, show (0 : Int) = ((0 : Nat) : Int) from rfl, zmul_natCast]
      rw [Spec.Weierstrass.mul]; simp
    have := hO.zmul_eq hC hP hP0 (by omega_arith) h0
    omega_arith
  have cc : ∀ r ∈ clob K.M.n, r ∈ RC := fun r h => hRC r (clob_combClob r h)
  have c19 : ∀ r ∈ Reg.x19 :: clob K.M.n, r ∈ RC := fun r h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact hRC _ (by simp [combClob])
    · exact cc r h
  rw [WinCfg.windowJ]
  refine WP.seq (WP.mono (build_ok hL hA hp hC hM3 hP hs hM hF₀ hpa hr hfar) fun sb B => ?_)
  refine WP.seq (WP.mono (normTbl_ok hL hA hp hC hpn hone_lt hone hne hI cc
      (cc _ (by simp [clob])) hx0 B.scr B.mod B.tbl)
    fun s ⟨hs', Kn, Un, hM', T⟩ => ?_)
  have U₀ : Unch base (winW K ++ IW) s₀.mem s.mem := (B.unch.trans Un).mono fun w hw => by
    simp only [List.mem_append] at hw ⊢; rcases hw with hw | hw | hw <;> simp [hw]
  have hF : WinFixed K C base s P k := by
    refine hF₀.unchJ hL U₀ hn (fun x hx w hw => ?_) (fun w hw => ?_)
    · rcases List.mem_append.mp hw with hw | hw
      · exact hL.ro_w hx w hw
      · rcases hI.w w hw with rfl | rfl | rfl | ⟨-, h⟩
        · exact hL.lay.apart x _ (winRo_slots K x hx) (winOther_mem (by win_in))
            fun e => hL.ro x hx (e ▸ by win_in)
        · exact hL.lay.tmp x (winRo_slots K x hx)
        · exact hL.lay.apart x _ (winRo_slots K x hx) (winOther_mem (by win_in))
            fun e => hL.ro x hx (e ▸ by win_in)
        · exact h x (winRo_slots K x hx)
    · rcases List.mem_append.mp hw with hw | hw
      · exact hL.bits_w w hw
      · exact hI.bits w hw
  have hr' : AddReady base K.M s.mem K.S pa :=
    AddReady.unch hpa (by win_in) (by omega_arith) hr U₀ (by
      match pa, hfar, hfarI with
      | none, _, _ => trivial
      | some _, h1, h2 =>
          intro w hw
          rcases List.mem_append.mp hw with hw | hw
          · exact h1 w hw
          · exact h2 w hw)
  have S₁ : WinStR K C base size (RepA C) P s s := ⟨hs', ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Unch.refl _ _ _, hM', T⟩
  obtain ⟨rxy, rxz, ryz, -⟩ := hL.other_ne
  have wR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ winOther K := pt_other (Or.inl rfl)
  have le : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x + 8 * K.M.n ≤ size := fun x hx =>
    hL.lay.le x (winOther_mem (wR x hx))
  have al : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x % 8 = 0 := fun x hx => hA.sl x (winOther_mem (wR x hx))
  have ap := fun {x y} (hx : x ∈ [K.R.x, K.R.y, K.R.z]) (hy : y ∈ [K.R.x, K.R.y, K.R.z]) (h : x ≠ y) =>
    hL.apart₂ (winOther_ws K x (wR x hx)) (winOther_ws K y (wR y hy)) h
  have axy := ap (x := K.R.x) (y := K.R.y) (by simp) (by simp) rxy
  have axz := ap (x := K.R.x) (y := K.R.z) (by simp) (by simp) rxz
  have ayz := ap (x := K.R.y) (y := K.R.z) (by simp) (by simp) ryz
  have hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) hone_lt
  refine WP.seq ?_
  rw [WinCfg.init, List.append_assoc, List.append_assoc, WP.block_append_iff]
  have W1 := setConst_ok S₁.scr (n := K.M.n) (o := K.R.x) (x := 0) (le _ (by simp)) (al _ (by simp))
    (Nat.two_pow_pos _)
  refine WP.mono W1 fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := S₁.scr.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  have W2 := setConst_ok hs₂ (n := K.M.n) (o := K.R.y) (x := K.one) (le _ (by simp)) (al _ (by simp))
    (Nat.lt_trans hone_lt hpn)
  refine WP.mono W2 fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [WP.block_append_iff]
  have W3 := setConst_ok hs₃ (n := K.M.n) (o := K.R.z) (x := 0) (le _ (by simp)) (al _ (by simp))
    (Nat.two_pow_pos _)
  refine WP.mono W3 fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  refine WP.mono (setCounter_ok s₄ (j := K.J) (by omega_using [hJ])) fun s₅ ⟨b₅, k₅⟩ => ?_
  have hU : Unch base (loopW K) s.mem s₅.mem := by
    rw [k₅.mem]
    refine (O₂.unch.trans (O₃.unch.trans O₄.unch)).mono fun w hw => ?_
    simp only [List.mem_append, List.mem_singleton] at hw
    simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton]
    refine Or.inl ⟨w.1, ?_, ?_⟩
    · rcases hw with rfl | rfl | rfl
      · exact wR _ (by simp)
      · exact wR _ (by simp)
      · exact wR _ (by simp)
    · rcases hw with rfl | rfl | rfl <;> rfl
  have c1 : ∀ r ∈ [Reg.x1], r ∈ combClob K.M.n := fun r hr =>
    combClob_mem (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hr)))
  have S₅ : WinStR K C base size (RepA C) P s s₅ := S₁.next hL (hs₄.of_keeps k₅ (by decide))
    ((((k₂.mono c1).trans (k₃.mono c1)).trans (k₄.mono c1)).trans
      ((Keeps.regs k₅).mono (by intro r hr; simp only [List.mem_singleton] at hr; subst hr
                                simp [combClob]))) hU
  have b64 : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := le x hx; omega_arith
  have vx : wordsVal s₅.mem base K.R.x K.M.n = 0 := by
    rw [k₅.mem, O₄.wordsVal axz (b64 _ (by simp)), O₃.wordsVal axy (b64 _ (by simp)), e₂]
  have vy : wordsVal s₅.mem base K.R.y K.M.n = K.one := by
    rw [k₅.mem, O₄.wordsVal ayz (b64 _ (by simp)), e₃]
  have vz : wordsVal s₅.mem base K.R.z K.M.n = 0 := by rw [k₅.mem, e₄]
  have I₅ : WinInvJ K C base size k P s s₅ K.J := by
    refine ⟨S₅, b₅, fun x hx => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · rw [vx]; exact hp0
      · rw [vy]; exact hone_lt
      · rw [vz]; exact hp0
    · refine Or.inl ⟨by rw [winE_top hk, mul_zero_pt'], ?_⟩
      show toM _ _ _ = 0
      rw [vz]; exact toM_zero _ _
  refine WP.seq (x4Loop_ok (Inv := fun j t => WinInvJ K C base size k P s t j) (n := K.J)
    (by omega_using [hJ])
    (fun j t h1 h2 hi => winStepJ_ok hL hA hp hC hM3 hO hP hP0 hpn hone_lt hone hF hk8 h1 h2
      (Nat.lt_of_le_of_lt (Nat.add_le_add_right (Nat.mul_le_mul_left _
        (winE_le_of_le hk8 (by omega_arith) (by omega_arith))) _) hb) hi hD hMa hS)
    (fun t hi => WP.mono (stepLast_ok hL hA hp hC hM3 hP hpn hone_lt hone hF hk8 hpa hr' hfar hi hD hS)
      fun u ⟨S, l, r⟩ => ⟨((B.keep.mono c19).trans Kn).trans (S.keep.mono hRC),
        (U₀.trans S.unch).mono fun w hw => by
          simp only [List.mem_append] at hw ⊢; rcases hw with (hw | hw) | hw <;> simp [hw],
        S.mod, l, by rw [← winE_zero]; exact r⟩) hJ2 I₅)

end VG.Proof.Weierstrass.AArch64
