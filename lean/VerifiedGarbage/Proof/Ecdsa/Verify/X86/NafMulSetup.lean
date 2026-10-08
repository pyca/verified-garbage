import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafLayout

/-! # The x86 P-256 variable-base product -/

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86 VG.Impl.Ecdsa.Verify.X86
open VG.Impl.Ecdh.X86 (PX PY)
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass
open VG.Proof.Ecdsa.X86 Spec.Weierstrass
variable {c : Impl.Ecdsa.X86.Cfg}

theorem windowMulQ_setup_ok (hc : CfgOk c) (h4 : c.n = 4) (hC : Law c.C)
    {s : State} {base : Addr} {g : Reg → BitVec 32} (hs : Scr s base size) (F : Fixed c base g s.mem)
    {P : Point c.C}
    (hpx : sv c base s PX < c.C.p) (hpy : sv c base s PY < c.C.p)
    (hQ : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P) :
    WP isa (.seq (.block (setConst c.n (c.sl EM) (c.mont c.C.b))) (Naf.prep 3580 (c.sl V) 3520)) s fun u =>
      Keeps powClob s u ∧ Unch base (windowW c) s.mem u.mem ∧ Fixed c base g u.mem ∧
      Inv (Cfg.nafQ c).M base size c.C.p (·∈nafSlots (Cfg.nafQ c)) (winRo (Cfg.nafQ c))
        (tmv c.C c.n base u) u ∧ NafInput (Cfg.nafQ c) c.C base P (sv c base s V) u ∧
      sv c base u PX=sv c base s PX ∧ sv c base u PY=sv c base s PY ∧
      sv c base u EM=c.mont c.C.b ∧ u.gpr .esi=257 := by
  have hn := hs.nowrap
  have hp := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  refine WP.seq (WP.mono (setConst_ok hs (sl_le c hc.n10 (i := EM) (by decide))
    (Nat.lt_trans (hmont _) hc.p_lt)) fun s₁ ⟨v₁, k₁, O₁⟩ => ?_)
  change sv c base s₁ EM = c.mont c.C.b at v₁
  have hs₁ := hs.of_keeps k₁ (by decide)
  have U₁ : Unch base (slW c [EM]) s.mem s₁.mem := O₁.unch
  have F₁ := F.unch hc.n10 hn (fixedOk_slW (by decide)) U₁
  have e₁ : ∀ {i}, i < 45 → i ≠ EM → sv c base s₁ i = sv c base s i :=
    fun hi he => sv_unch U₁ hc.n10 hn hi (apart_slW (by simpa only [List.mem_singleton] using he))
  refine WP.mono (nafPrep_ok hs₁
    (by rw [sl_eq,h4]; decide) (by decide) (by decide)
    (Or.inr (by rw [sl_eq,h4]; decide)) (by decide)) fun s₂ ⟨prep,k₂,O₂⟩ => ?_
  have bits : ∀ t<257,s₂.mem (off base (3580+t))=Naf5.byte (sv c base s V) t := by
    intro t ht
    have hv : val32 s₁.mem base (c.sl V) 8=sv c base s V := by
      have ev := e₁ (i:=V) (by decide) (by decide)
      change wordsVal s₁.mem base (c.sl V) c.n=sv c base s V at ev
      rw [wordsVal_eq_val32,h4] at ev
      exact ev
    rw [prep.digits t ht,hv]
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have U₂ : Unch base (nafPrepWrites 3580 3520) s₁.mem s₂.mem := O₂
  have ap₂ : ∀ {i}, i < 45 → ∀ w ∈ nafPrepWrites 3580 3520,
      c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
    intro i hi w hw
    simp only [nafPrepWrites,List.mem_cons, List.not_mem_nil, or_false] at hw
    left; rw [sl_eq, h4]
    rcases hw with rfl | rfl <;> dsimp only <;> omega
  have e₂ : ∀ {i}, i < 45 → sv c base s₂ i = sv c base s₁ i :=
    fun hi => sv_unch U₂ hc.n10 hn hi (ap₂ hi)
  have F₂ := F₁.unch hc.n10 hn (show FixedOk c (nafPrepWrites 3580 3520) from by
    intro w hw; simp only [nafPrepWrites,List.mem_cons, List.not_mem_nil, or_false] at hw
    right; rw [sl_eq, h4]; rcases hw with rfl | rfl <;> decide) U₂
  have tv : ∀ {i}, i < 45 → i ≠ EM → tmv c.C c.n base s₂ (c.sl i) = tmv c.C c.n base s (c.sl i) := by
    intro i hi he
    change toM _ _ (sv c base s₂ i) = toM _ _ (sv c base s i)
    rw [e₂ hi, e₁ hi he]
  let K := Impl.Ecdsa.Verify.X86.Cfg.nafQ c
  have hL := nafQLay (c:=c) h4
  have hW := nafQWk hc h4
  have hSl : ∀ x∈winRo K,x∈nafSlots K := nafRo_slots K
  have hlt : ∀ x∈winRo K,wordsVal s₂.mem base x K.M.n<c.C.p := by
    intro x hx
    change x ∈ [c.sl AP,c.sl EM,c.sl ZERO,c.sl PX,c.sl PY,c.sl ONEP] at hx
    change wordsVal s₂.mem base x c.n<c.C.p
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl
    · rw [F₂.ap]; exact hmont _
    · change sv c base s₂ EM < _
      rw [e₂ (by decide),v₁]; exact hmont _
    · rw [F₂.zero]; omega
    · change sv c base s₂ PX < _
      rw [e₂ (by decide),e₁ (by decide) (by decide)]; exact hpx
    · change sv c base s₂ PY < _
      rw [e₂ (by decide),e₁ (by decide) (by decide)]; exact hpy
    · rw [F₂.onep]; exact Nat.mod_lt _ (by omega)
  have hI : Inv K.M base size c.C.p (·∈nafSlots K) (winRo K) (tmv c.C c.n base s₂) s₂ :=
    ⟨hs₂,modP_of hc F₂.mp,hSl,hlt,fun _ _ => rfl⟩
  have hone : tmv c.C c.n base s₂ (c.sl ONEP)=1 := by
    unfold tmv
    rw [F₂.onep]
    exact toM_one (unitMod_pow_two hc.p_odd _)
  have hQP : Rep c.C (tmv c.C c.n base s₂ (c.sl PX)) (tmv c.C c.n base s₂ (c.sl PY))
      (tmv c.C c.n base s₂ (c.sl ONEP)) P := by
    rw [tv (by decide) (by decide),tv (by decide) (by decide),tv (by decide) (by decide)]
    exact hQ
  have hJP : InvJ c.C (tmv c.C c.n base s₂ K.P.x) (tmv c.C c.n base s₂ K.P.y)
      (tmv c.C c.n base s₂ K.P.z) P := by
    have hj := InvJ.of_rep hC hQP
    change InvJ c.C (tmv c.C c.n base s₂ (c.sl PX)) (tmv c.C c.n base s₂ (c.sl PY))
      (tmv c.C c.n base s₂ (c.sl ONEP)) P
    rw [hone] at hj ⊢
    simpa only [Lean.Grind.Semiring.mul_one] using hj
  have UW₁ : Unch base (windowW c) s.mem s₁.mem := U₁.mono (by
    intro w hw; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
    exact List.mem_append_left _ (List.mem_map.mpr ⟨i,by rw [List.mem_singleton.mp hi]; decide,rfl⟩))
  have UW₂ : Unch base (windowW c) s₁.mem s₂.mem := U₂.cover (by
    intro w hw; simp only [nafPrepWrites,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl <;>
      exact ⟨(2640,1456),List.mem_append_right _ (by simp),by decide,by decide⟩)
  exact ⟨(k₁.mono (by decide)).trans (k₂.mono (by decide)),
    (fun x hx => (UW₂ x hx).trans (UW₁ x hx)),F₂,hI,⟨hJP,F₂.zero,bits⟩,
    (e₂ (by decide)).trans (e₁ (by decide) (by decide)),
    (e₂ (by decide)).trans (e₁ (by decide) (by decide)),
    (e₂ (by decide)).trans v₁,prep.count⟩

end VG.Proof.Ecdsa.Verify.X86
