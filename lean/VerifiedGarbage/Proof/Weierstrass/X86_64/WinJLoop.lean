import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJStep

/-!
# Windows in Jacobian coordinates on x86-64: the last iteration and the loop

The last iteration (`stepLast_ok`): `R = 16 R` in Jacobian coordinates, `R`
into projective coordinates with `Y = 1` where `Z = 0` (`toProjR_ok`), and its
sum with the entry of digit `0` (affine, so projective) by the complete
formulas (`sumStep_ok`). The method (`windowJ_ok`): the table (`build_ok`)
into affine coordinates (`normTbl_ok`), then from `R = O` the iterations of
`winStepJ_ok` for the digits `J - 1` down to `1`, and the last.
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

/-- `R` from Jacobian coordinates into projective coordinates, `(XZ : Y : Z³)`,
with `Y` Montgomery's one where `Z = 0`. -/
theorem toProjR_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) {P : Point C}
    {Rp : Fe C → Fe C → Fe C → Point C → Prop} (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {s₀ s : State} (hF : WinFixed K C base s₀ P k)
    (hS : WinStR K C base size Rp P s₀ s) {Q : Point C}
    (hlt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hR : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z) Q) :
    WP isa (WinCfg.toProjR K) s fun s' =>
      WinStR K C base size Rp P s₀ s' ∧ s'.gpr .rbx = s.gpr .rbx ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z) Q := by
  obtain ⟨-, -, ro_lt, hz⟩ := hS.ro_tmv hL hF
  obtain ⟨-, -, aRD⟩ := hL.rcbApart_winJ
  have oR := pt_other (K := K) (p := K.R) (Or.inl rfl)
  have oD := pt_other (K := K) (p := K.D) (Or.inr (Or.inr rfl))
  have sZ : ∀ x ∈ [(WinCfg.zeroPt K).x, (WinCfg.zeroPt K).y, (WinCfg.zeroPt K).z], x ∈ winSlots K := by
    intro x hx
    simp only [WinCfg.zeroPt, List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
    subst hx; win_mem
  have w1 := winJ_sl oD (fun x hx => winOther_mem (oR x hx)) sZ
  let V := [K.R.x, K.R.y, K.R.z, K.S.a, K.S.b3, K.zero]
  have V0 : ∀ x ∈ V, x ∈ winSlots K ∧ wordsVal s.mem base x K.M.n < C.p := by
    intro x hx
    simp only [V, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨winOther_mem (oR _ (by simp)), hlt _ (by simp)⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hlt _ (by simp)⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hlt _ (by simp)⟩
    all_goals exact ⟨by win_mem, ro_lt _ (by simp [winRo])⟩
  have I₀ : Inv K.M base size C.p (· ∈ winSlots K) V (tmv C K.M.n base s) s :=
    ⟨hS.scr, hS.mod, fun x hx => (V0 x hx).1, fun x hx => (V0 x hx).2, fun _ _ => rfl⟩
  rw [WinCfg.toProjR, fromJ_eq]
  refine WP.seq (WP.mono (winN_ok hL hp fromJN_ok aRD w1.1 w1.2 I₀ (by
      intro x hx
      simp only [rcbR, V, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h | h | h | h | h | h | h <;> simp only [h, true_or, or_true]))
    fun s₁ ⟨k₁, U₁, E₁, I₁, o₁, v₁⟩ => ?_)
  have S₁ := hS.next hL I₁.scr (k₁.mono clob_powClob) U₁
  have v : (E₁ K.D.x, E₁ K.D.y, E₁ K.D.z) = (tmv C K.M.n base s K.R.x * tmv C K.M.n base s K.R.z,
      tmv C K.M.n base s K.R.y + tmv C K.M.n base s K.zero,
      tmv C K.M.n base s K.R.z * tmv C K.M.n base s K.R.z * tmv C K.M.n base s K.R.z) :=
    v₁.trans (fromJN_run _)
  have hDV : ∀ x ∈ [K.D.x, K.D.y, K.D.z], x ∈ [K.D.x, K.D.y, K.D.z] ++ V := fun x hx =>
    List.mem_append_left _ hx
  have z0 : tmv C K.M.n base s K.zero = 0 := by
    show toM _ _ _ = 0; rw [hz]; exact toM_zero _ _
  -- `R = D`.
  obtain ⟨hle, hap, hne, ho⟩ := winRD hL
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (copyPt_ok I₁.scr hle hap hne ho) fun s₂ ⟨wx, wy, wz, k₂, U₂⟩ => ?_
  have hs₂ := I₁.scr.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  have hRz : K.R.z + 8 * K.M.n ≤ size := hle _ (by simp)
  have hRy : K.R.y + 8 * K.M.n ≤ size := hle _ (by simp)
  have hRx : K.R.x + 8 * K.M.n ≤ size := hle _ (by simp)
  refine WP.mono (zmask_ok K hs₂ hL.n0 hRz) fun s₃ ⟨m₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  refine WP.mono (ySelWords_ok hs₃ K _ m₃ K.M.n hRy) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have hn := hs₂.nowrap
  have m₃' : s₃.mem = s₂.mem := k₃.2.1
  obtain ⟨rxy, rxz, ryz, -⟩ := hL.other_ne
  have ay : ∀ x ∈ [K.R.x, K.R.z], x ≠ K.R.y → x + 8 * K.M.n ≤ K.R.y ∨ K.R.y + 8 * K.M.n ≤ x :=
    fun x hx h => hap x (by simp at hx ⊢; omega_using [hx]) _ (by simp) h
  have vRx : wordsVal s₄.mem base K.R.x K.M.n = wordsVal s₁.mem base K.D.x K.M.n := by
    rw [O₄.wordsVal (by have := ay _ (by simp) rxy; omega) (by omega), m₃', wx]
  have vRz : wordsVal s₄.mem base K.R.z K.M.n = wordsVal s₁.mem base K.D.z K.M.n := by
    rw [O₄.wordsVal (by have := ay _ (by simp) (Ne.symm ryz); omega) (by omega), m₃', wz]
  have hone' : K.one < 2 ^ (64 * K.M.n) := Nat.lt_trans hone_lt hpn
  have vRy : wordsVal s₄.mem base K.R.y K.M.n =
      if wordsVal s₁.mem base K.D.z K.M.n = 0 then K.one else wordsVal s₁.mem base K.D.y K.M.n := by
    rw [← wz, ← wy]
    by_cases hz0 : wordsVal s₂.mem base K.R.z K.M.n = 0
    · simp only [hz0, ↓reduceIte]
      exact wordsVal_of_shifts _ _ _ _ _ hone' fun j hj => by simp only [e₄ j hj, hz0, ↓reduceIte]; rfl
    · simp only [hz0, ↓reduceIte]
      rw [← m₃']
      exact wordsVal_congr₂ _ _ _ fun j hj => by simp only [e₄ j hj, hz0, ↓reduceIte]
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
  have c : ∀ r ∈ [Reg.rax, .rdx, .r8], r ∈ powClob K.M.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simp [powClob, clob]
    · simp [powClob, clob]
    · exact List.mem_cons_of_mem _ (r8_mem_clob _)
  have kk : KeepRegs (powClob K.M.n) s₁ s₄ :=
    (k₂.mono fun r hr => c r (by simp at hr ⊢; simp [hr])).trans (((Keeps.regs k₃).mono
      fun r hr => c r (by simp at hr ⊢; simp [hr])).trans (k₄.mono fun r hr => c r (by
        simp at hr ⊢; rcases hr with h | h <;> simp [h])))
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
    · intro h; rw [h]; grind
  refine ⟨S₄, by rw [k₄.gpr _ (by decide), k₃.1 _ (by decide), k₂.gpr _ (by decide),
    k₁.gpr _ (rbx_not_clob _)], fun x hx => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [vRx]; exact I₁.lt _ (hDV _ (by simp))
    · rw [vRy]; split
      · exact hone_lt
      · exact I₁.lt _ (hDV _ (by simp))
    · rw [vRz]; exact I₁.lt _ (hDV _ (by simp))
  · have h := InvJ.out hC hR
    show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [vRx, vRy, vRz, toM_ite, hone, eD _ (by simp), eD _ (by simp), eD _ (by simp), vx, vy, vz]
    simp only [hZ]
    rw [z0, show ∀ y : Fe C, y + 0 = y from fun y => by grind]
    exact h

/-- The last iteration, `rbx = 1` to `0`: adds digit `0` by the complete
formulas, leaving `R` in projective coordinates. -/
theorem stepLast_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hX : WinX K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C)
    {P : Point C} (hP : onCurve C P = true)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {s₀ : State} (hF : WinFixed K C base s₀ P k)
    (hk8 : 8 * geom K.J ≤ k) {s : State} (hI : WinInvJ K C base size k P s₀ s 1) :
    WP isa (WinCfg.stepLast K) s fun s' =>
      WinStR K C base size (RepA C) P s₀ s' ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z)
        (mul (winE k K.J 0) P) := by
  have hJ := hL.J
  rw [WinCfg.stepLast]
  refine WP.seq (WP.mono (decRbx_ok s (by omega) (by omega) hI.rbx) fun s₁ ⟨b₁, k₁⟩ => ?_)
  have hS₁ := hI.st.rbxKeeps hL k₁
  have lt₁ : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₁.mem base x K.M.n < C.p := by
    rw [k₁.2.1]; exact hI.lt
  have rep₁ : InvJ C (tmv C K.M.n base s₁ K.R.x) (tmv C K.M.n base s₁ K.R.y)
      (tmv C K.M.n base s₁ K.R.z) (mul (winE k K.J 1) P) := by
    have e : ∀ x, tmv C K.M.n base s₁ x = tmv C K.M.n base s x := fun x => by
      show toM _ _ _ = toM _ _ _; rw [k₁.2.1]
    rw [e, e, e]; exact hI.rep
  refine WP.seq (WP.mono (quadJ_ok hL hp hC hM3 hP hF hS₁ (i := 0) (by omega) b₁ lt₁ rep₁)
    fun s₂ ⟨S₂, x₂, l₂, r₂⟩ => ?_)
  refine WP.seq (WP.mono (toProjR_ok hL hp hC hpn hone_lt hone hF S₂ l₂ r₂)
    fun s₅ ⟨S₅, x₅, l₅, r₅⟩ => ?_)
  have hx₅ : s₅.gpr .rbx = BitVec.ofNat 64 0 := by rw [x₅, x₂, b₁]
  obtain ⟨-, -, -, hz₅⟩ := S₅.ro_tmv hL hF
  have hbits₅ : ∀ t < 4 * K.J, s₅.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by
      have := hL.bits
      rw [S₅.unch.byte (fun w hw => by have := hL.bits_w w hw; omega) (by have := S₅.scr.nowrap; omega)]
      exact hF.bits t ht
  refine WP.seq (WP.mono (winEntryR_ok hL hX (RepA.infinity hC) RepA.negY (P := P) hpn hone_lt hone
    S₅.scr S₅.mod (i := 0) (by omega) hx₅ hbits₅ hz₅ S₅.tbl) fun s₆ h₆ => WP.seq (WP.mono h₆
      fun s₇ E₇ => ?_))
  have hn := S₅.scr.nowrap
  have S₇ := S₅.next hL E₇.scr (E₇.keep.mono clob_powClob) (E₇.unch.mono (entryW_loopW K))
  have eR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₇.mem base x K.M.n = wordsVal s₅.mem base x K.M.n :=
    fun x hx => E₇.unch.wordsVal (R_apart_entry hL hx) (by
      have := hL.lay.le x (winOther_mem (pt_other (K := K) (p := K.R) (Or.inl rfl) x hx)); omega)
  have lt₇ : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₇.mem base x K.M.n < C.p := fun x hx => by
    rw [eR x hx]; exact l₅ x hx
  have rep₇ : Rep C (tmv C K.M.n base s₇ K.R.x) (tmv C K.M.n base s₇ K.R.y)
      (tmv C K.M.n base s₇ K.R.z) (mul (16 * winE k K.J 1) P) := by
    rw [tmv_congr (eR _ (by simp)), tmv_congr (eR _ (by simp)), tmv_congr (eR _ (by simp))]; exact r₅
  refine WP.mono (sumStep_ok hL hp hC hM3 hF S₇ (hC.onCurve_mul hP _) (onCurve_winPt hC hP k 0)
    lt₇ E₇.lt rep₇ E₇.rep.1) fun s₉ ⟨S₉, _, l₉, r₉⟩ => ⟨S₉, l₉, ?_⟩
  have hadd := win_add hC hP (k := k) (J := K.J) (j := 0) hk8 (by omega)
  rw [hadd] at r₉
  exact r₉

/-- What is read only, and the table of bits, survive writes apart from them. -/
theorem WinFixed.unch {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    {P : Point C} {s s' : State} (hF : WinFixed K C base s P k) {W : List (Nat × Nat)}
    (hU : Unch base W s.mem s'.mem) (hn : base.toNat + size ≤ 2 ^ 64)
    (hro : ∀ x ∈ winRo K, ∀ w ∈ W, x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x)
    (hbits : ∀ w ∈ W, K.bits + 4 * K.J ≤ w.1 ∨ w.1 + w.2 ≤ K.bits) : WinFixed K C base s' P k := by
  have e : ∀ x ∈ winRo K, wordsVal s'.mem base x K.M.n = wordsVal s.mem base x K.M.n := fun x hx =>
    hU.wordsVal (hro x hx) (by have := hL.lay.le x (winRo_slots K x hx); omega)
  have hb := hL.bits
  refine ⟨?_, ?_, fun x hx => by rw [e x hx]; exact hF.ro_lt x hx, by rw [e _ (by simp [winRo])]; exact hF.zero,
    ?_, fun t ht => ?_⟩
  · rw [tmv_congr (e _ (by simp [winRo]))]; exact hF.a
  · rw [tmv_congr (e _ (by simp [winRo]))]; exact hF.b
  · rw [tmv_congr (e _ (by simp [winRo])), tmv_congr (e _ (by simp [winRo])), tmv_congr (e _ (by simp [winRo]))]
    exact hF.pt
  · rw [hU.byte (fun w hw => by have := hbits w hw; omega) (by omega)]
    exact hF.bits t ht

/-- `[k - 8 Σ_{i<J} 16^i]P` into `R`, for `8 Σ_{i<J} 16^i ≤ k < 16^J` whose bits
are the table at `K.bits`, by windows in Jacobian coordinates with an affine
table (by the inversion `inv`, writing `IW`): for `P ≠ O` on a curve of
prime order `n` (`PrimeOrder`), with `16 winE k J 2 + 8 < n` (so that no
addition but the last is of equal or opposite points); only `invClob`,
`winW` and `IW` change. -/
theorem windowJ_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hX : WinX K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C)
    (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true) (hP0 : P ≠ .infinity)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {inv : Prog isa} {IW : List (Nat × Nat)}
    (hI : InvSpecW K C base size inv IW) {s₀ : State} (hs : Scr s₀ base size)
    (hM : ModOkW K.M size C.p s₀.mem base) (hF₀ : WinFixed K C base s₀ P k) (hk : k < 16 ^ K.J)
    (hk8 : 8 * geom K.J ≤ k) (hJ2 : 2 ≤ K.J) (hb : 16 * winE k K.J 2 + 8 < C.n) :
    WP isa (WinCfg.windowJ K inv) s₀ fun s' => KeepRegs (invClob K.M.n) s₀ s' ∧
      Unch base (winW K ++ IW) s₀.mem s'.mem ∧ ModOkW K.M size C.p s'.mem base ∧
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
    have := hO.zmul_eq hC hP hP0 (by omega) h0
    omega
  have pc : ∀ r ∈ powClob K.M.n, r ∈ invClob K.M.n := fun r h => List.mem_cons_of_mem _ h
  rw [WinCfg.windowJ]
  refine WP.seq (WP.mono (build_ok hL hp hC hM3 hP hs hM hF₀) fun sb B => ?_)
  refine WP.seq (WP.mono (normTbl_ok hL hp hC hpn hone_lt hone hne hI B.scr B.mod B.tbl)
    fun s ⟨hs', Kn, Un, hM', T⟩ => ?_)
  have U₀ : Unch base (winW K ++ IW) s₀.mem s.mem := (B.unch.trans Un).mono fun w hw => by
    simp only [List.mem_append] at hw ⊢; rcases hw with hw | hw | hw <;> simp [hw]
  have hF : WinFixed K C base s P k := by
    refine hF₀.unch hL U₀ hn (fun x hx w hw => ?_) (fun w hw => ?_)
    · rcases List.mem_append.mp hw with hw | hw
      · exact hL.ro_w hx w hw
      · rcases hI.w w hw with rfl | rfl | ⟨-, h⟩
        · exact hL.lay.apart x _ (winRo_slots K x hx) (winOther_mem (by win_mem))
            fun e => hL.ro x hx (e ▸ by win_mem)
        · exact hL.lay.tmp x (winRo_slots K x hx)
        · exact h x (winRo_slots K x hx)
    · rcases List.mem_append.mp hw with hw | hw
      · exact hL.bits_w w hw
      · exact hI.bits w hw
  have S₁ : WinStR K C base size (RepA C) P s s := ⟨hs', ⟨fun _ _ => rfl, rfl, rfl⟩, Unch.refl _ _ _, hM', T⟩
  obtain ⟨rxy, rxz, ryz, -⟩ := hL.other_ne
  have wR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ winOther K := pt_other (Or.inl rfl)
  have le : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x + 8 * K.M.n ≤ size := fun x hx =>
    hL.lay.le x (winOther_mem (wR x hx))
  have ap := fun {x y} (hx : x ∈ [K.R.x, K.R.y, K.R.z]) (hy : y ∈ [K.R.x, K.R.y, K.R.z]) (h : x ≠ y) =>
    hL.apart₂ (winOther_ws K x (wR x hx)) (winOther_ws K y (wR y hy)) h
  have axy := ap (x := K.R.x) (y := K.R.y) (by simp) (by simp) rxy
  have axz := ap (x := K.R.x) (y := K.R.z) (by simp) (by simp) rxz
  have ayz := ap (x := K.R.y) (y := K.R.z) (by simp) (by simp) ryz
  have hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) hone_lt
  refine WP.seq ?_
  rw [WinCfg.init, List.append_assoc, List.append_assoc, WP.block_append_iff]
  have W1 := setConst_ok S₁.scr (n := K.M.n) (o := K.R.x) (x := 0) (le _ (by simp)) (Nat.two_pow_pos _)
  refine WP.mono W1 fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := S₁.scr.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  have W2 := setConst_ok hs₂ (n := K.M.n) (o := K.R.y) (x := K.one) (le _ (by simp))
    (Nat.lt_trans hone_lt hpn)
  refine WP.mono W2 fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [WP.block_append_iff]
  have W3 := setConst_ok hs₃ (n := K.M.n) (o := K.R.z) (x := 0) (le _ (by simp)) (Nat.two_pow_pos _)
  refine WP.mono W3 fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  refine WP.mono (mov32Rbx_ok s₄ (j := K.J) (by omega)) fun s₅ ⟨b₅, k₅⟩ => ?_
  have hU : Unch base (loopW K) s.mem s₅.mem := by
    rw [k₅.2.1]
    refine (O₂.unch.trans (O₃.unch.trans O₄.unch)).mono fun w hw => ?_
    simp only [List.mem_append, List.mem_singleton] at hw
    simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton]
    refine Or.inl ⟨w.1, ?_, ?_⟩
    · rcases hw with rfl | rfl | rfl
      · exact wR _ (by simp)
      · exact wR _ (by simp)
      · exact wR _ (by simp)
    · rcases hw with rfl | rfl | rfl <;> rfl
  have c1 : ∀ r ∈ [Reg.rax], r ∈ powClob K.M.n := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp [powClob, clob]
  have S₅ : WinStR K C base size (RepA C) P s s₅ := S₁.next hL (hs₄.of_keeps k₅ (by decide))
    ((((k₂.mono c1).trans (k₃.mono c1)).trans (k₄.mono c1)).trans
      ((Keeps.regs k₅).mono (by intro r hr; simp only [List.mem_singleton] at hr; subst hr
                                simp [powClob]))) hU
  have b64 : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := le x hx; omega
  have vx : wordsVal s₅.mem base K.R.x K.M.n = 0 := by
    rw [k₅.2.1, O₄.wordsVal axz (b64 _ (by simp)), O₃.wordsVal axy (b64 _ (by simp)), e₂]
  have vy : wordsVal s₅.mem base K.R.y K.M.n = K.one := by
    rw [k₅.2.1, O₄.wordsVal ayz (b64 _ (by simp)), e₃]
  have vz : wordsVal s₅.mem base K.R.z K.M.n = 0 := by rw [k₅.2.1, e₄]
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
  refine WP.seq (countLoop_ok (Inv := fun i t => WinInvJ K C base size k P s t (i + 1)) (n := K.J - 1)
    (fun i t h1 h2 hi => WP.mono (winStepJ_ok hL hX hp hC hM3 hO hP hP0 hpn hone_lt hone hF hk8
      (j := i + 1) (by omega) (by omega)
      (Nat.lt_of_le_of_lt (Nat.add_le_add_right (Nat.mul_le_mul_left _
        (winE_le_of_le hk8 (by omega) (by omega))) _) hb) hi)
      fun u ⟨I, z⟩ => ⟨by rw [show i - 1 + 1 = i + 1 - 1 by omega]; exact I,
        by rw [z]; congr 1; simp only [decide_eq_decide]; omega⟩)
    (fun t hi => WP.mono (stepLast_ok hL hX hp hC hM3 hP hpn hone_lt hone hF hk8 hi)
      fun u ⟨S, l, r⟩ => ⟨((B.keep.mono pc).trans Kn).trans (S.keep.mono pc),
        (U₀.trans S.unch).mono fun w hw => by
          simp only [List.mem_append] at hw ⊢; rcases hw with (hw | hw) | hw <;> simp [hw],
        S.mod, l, by rw [← winE_zero]; exact r⟩)
    (by omega) (by rw [Nat.sub_add_cancel (by omega)]; exact I₅))

end VG.Proof.Weierstrass.X86_64
