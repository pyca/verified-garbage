import VerifiedGarbage.Proof.Weierstrass.JacMadd
import VerifiedGarbage.Proof.Ecdh.X86.JacWrites
import VerifiedGarbage.Proof.Ecdh.X86.JacPrep
import VerifiedGarbage.Proof.Weierstrass.X86.WinJacLoop

/-! # The x86 P-256 variable-base product -/

namespace VG.Proof.Ecdh.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86 VG.Impl.Ecdsa.Verify.X86
open VG.Impl.Ecdh.X86 (PX PY)
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass
open VG.Proof.Ecdsa.X86 VG.Proof.Ecdsa.Verify.X86 Spec.Weierstrass
variable {c : Impl.Ecdsa.X86.Cfg}

/-- The Jacobian product is canonical for every scalar and correct for valid scalars. -/
theorem jwinMul_ok (hc : CfgOk c) (h4 : c.n = 4) (hC : Law c.C) (hM3 : AM3 c.C)
    (hO : PrimeOrder c.C) (hn17 : c.C.n % 32 = 17) (hn64 : 64 ≤ c.C.n)
    {s : State} {base : Addr} {g : Reg → BitVec 32} (hs : Scr s base size) (F : Fixed c base g s.mem)
    {P : Point c.C} (hP : onCurve c.C P = true) (hP0 : P ≠ .infinity)
    (hpx : sv c base s PX < c.C.p) (hpy : sv c base s PY < c.C.p)
    (hQ : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P) :
    WP isa (Impl.Ecdh.X86.Cfg.jwinMul c) s fun u =>
      Keeps powClob s u ∧ Unch base (jwinW c) s.mem u.mem ∧
      ModOkW c.MP' size c.C.p u.mem base ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal u.mem base x c.n < c.C.p) ∧
      (sv c base s K < c.C.n → Rep c.C (tmv c.C c.n base u (c.sl RX)) (tmv c.C c.n base u (c.sl RY))
        (tmv c.C c.n base u (c.sl RZ)) (mul (sv c base s K) P)) := by
  have hn := hs.nowrap
  have hp := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  unfold Impl.Ecdh.X86.Cfg.jwinMul
  refine WP.seq (WP.mono (setConst_ok hs (sl_le c hc.n10 (i := EM) (by decide))
    (Nat.lt_trans (hmont _) hc.p_lt)) fun s₁ ⟨v₁, k₁, O₁⟩ => ?_)
  change sv c base s₁ EM = c.mont c.C.b at v₁
  have hs₁ := hs.of_keeps k₁ (by decide)
  have U₁ : Unch base (slW c [EM]) s.mem s₁.mem := O₁.unch
  have F₁ := F.unch hc.n10 hn (fixedOk_slW (by decide)) U₁
  have e₁ : ∀ {i}, i < 45 → i ≠ EM → sv c base s₁ i = sv c base s i :=
    fun hi he => sv_unch U₁ hc.n10 hn hi (apart_slW (by simpa only [List.mem_singleton] using he))
  refine WP.seq (WP.mono (jwinPrep_ok h4 hs₁) fun s₂ ⟨bits, k₂, O₂⟩ => ?_)
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have U₂ := O₂
  have ap₂ : ∀ {i}, i < 45 → ∀ w ∈ [(3520, 120), (Impl.Ecdh.X86.Cfg.windowBits, 320)],
      c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
    intro i hi w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    left; rw [sl_eq, h4]
    rcases hw with rfl | rfl <;> dsimp only [Impl.Ecdh.X86.Cfg.windowBits] <;> omega
  have e₂ : ∀ {i}, i < 45 → sv c base s₂ i = sv c base s₁ i :=
    fun hi => sv_unch U₂ hc.n10 hn hi (ap₂ hi)
  have F₂ := F₁.unch hc.n10 hn (show FixedOk c [(3520, 120), (Impl.Ecdh.X86.Cfg.windowBits, 320)] from by
    intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    right; rw [sl_eq, h4]; rcases hw with rfl | rfl <;> decide) U₂
  have tv : ∀ {i}, i < 45 → i ≠ EM → tmv c.C c.n base s₂ (c.sl i) = tmv c.C c.n base s (c.sl i) := by
    intro i hi he
    change toM _ _ (sv c base s₂ i) = toM _ _ (sv c base s i)
    rw [e₂ hi, e₁ hi he]
  have hlt : ∀ x∈JWin.ro (Impl.Ecdh.X86.Cfg.jwinCfg c),wordsVal s₂.mem base x c.n<c.C.p := by
    intro x hx
    change x ∈ [c.sl AP,c.sl EM,c.sl PX,c.sl PY,c.sl ONEP,c.sl ZERO] at hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact F₂.ap ▸ hmont _
    · change sv c base s₂ EM < _
      rw [e₂ (by decide),v₁]; exact hmont _
    · change sv c base s₂ PX < _
      rw [e₂ (by decide),e₁ (by decide) (by decide)]; exact hpx
    · change sv c base s₂ PY < _
      rw [e₂ (by decide),e₁ (by decide) (by decide)]; exact hpy
    · rw [F₂.onep]; exact Nat.mod_lt _ (by omega)
    · rw [F₂.zero]; omega
  have hz : tmv c.C c.n base s₂ (c.sl ONEP)=1 := by
    change toM _ _ (wordsVal s₂.mem base (c.sl ONEP) c.n)=1
    rw [F₂.onep]
    exact toM_one (unitMod_pow_two hc.p_odd _)
  have hQ₂ : Rep c.C (tmv c.C c.n base s₂ (c.sl PX)) (tmv c.C c.n base s₂ (c.sl PY)) 1 P := by
    rw [← hz,tv (by decide) (by decide),tv (by decide) (by decide),tv (by decide) (by decide)]
    exact hQ
  have hJ : InvJ c.C (tmv c.C c.n base s₂ (c.sl PX)) (tmv c.C c.n base s₂ (c.sl PY))
      (tmv c.C c.n base s₂ (c.sl ONEP)) P := by
    rw [hz,Rep.eq_affine hC hQ₂]
    exact InvJ.affine hC _ _
  have hoff : JacWinCfg.offset 52 = 16*Window5.geom 52 := Window5.offset_eq.symm
  have hb : ∀ t<260,s₂.mem (off base (Impl.Ecdh.X86.Cfg.windowBits+t))=
      if (sv c base s K+16*Window5.geom 52).testBit t then 1 else 0 := by
    intro t ht
    rw [bits t ht,e₁ (by decide) (by decide),hoff]
  have hrec : sv c base s K+16*Window5.geom 52<32^52 := by
    apply Window5.recode_lt
    change wordsVal s.mem base (c.sl K) c.n<2^256
    rw [h4]; exact wordsVal_lt _ _ _ 4
  have hi : Inv c.MP' base size c.C.p (·∈JWin.slots (Impl.Ecdh.X86.Cfg.jwinCfg c))
      (JWin.ro (Impl.Ecdh.X86.Cfg.jwinCfg c)) (tmv c.C c.n base s₂) s₂ :=
    ⟨hs₂,modP_of hc F₂.mp,fun _ hx => List.mem_append_left _ hx,hlt,fun _ _ => rfl⟩
  refine WP.mono (JWin.window_ok (jwinLay h4) (jwinWk hc h4)
    (unitMod_pow_two hc.p_odd _) hC hM3 hO hP hP0 hn17 hn64 (hmont 1)
    (by change toM c.C.p (2^(64*c.n)) (c.mont 1)=1; exact toM_cmont hc 1)
    hi hJ hz F₂.zero hb hrec) fun u ⟨fu,Lu,qu⟩ => ?_
  have UW₁ : Unch base (windowW c) s.mem s₁.mem := U₁.mono (by
    intro w hw; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    exact List.mem_append_left _ (List.mem_map.mpr ⟨i, by rw [List.mem_singleton.mp hi]; decide, rfl⟩))
  have UW₂ : Unch base (windowW c) s₁.mem s₂.mem := U₂.cover (by
    intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨(2640, 1456), List.mem_append_right _ (by simp), by decide, by decide⟩
    · exact ⟨(Impl.Ecdh.X86.Cfg.windowBits, 320), List.mem_append_right _ (by simp), Nat.le_refl _,
        Nat.le_refl _⟩)
  have ku : Keeps powClob s₂ u := ⟨fun r hr => fu.keep.1 r (by simp only [powClob,List.mem_cons] at hr; exact fun h => hr (by simpa only [JWin.clobbers,List.mem_append,List.mem_singleton,or_comm] using h)),fu.keep.2.1,fu.keep.2.2⟩
  have UW : Unch base (jwinW c) s.mem s₂.mem :=
    (show Unch base (windowW c) s.mem s₂.mem from fun x hx => (UW₂ x hx).trans (UW₁ x hx)).mono
      (fun _ hx => List.mem_append_left _ hx)
  exact ⟨((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans ku,
    fun x hx => (fu.unch.cover (jwinW_cover h4) x hx).trans (UW x hx),fu.mod,Lu,qu⟩

end VG.Proof.Ecdh.X86
