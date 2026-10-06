import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacLayout
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowTiming

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (V)
open VG.Impl.Ecdsa.Verify.AArch64.Cfg (jacWinCfg)
variable {c : Cfg}

theorem jacWinPrep_ok (hc : CfgOk c) (hn4 : c.n=4) (hC : Law c.C) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (F : Fixed c base g s.mem) {P : Point c.C}
    (hpx : sv c base s PX < c.C.p) (hpy : sv c base s PY < c.C.p)
    (hrep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P)
 :
    WP isa (Impl.Ecdsa.Verify.AArch64.Cfg.jacWinPrep c) s fun t =>
      Inv (jacWinCfg c).M base size c.C.p (·∈jacWinSlots (jacWinCfg c))
        (winRo (jacWinCfg c)) (tmv c.C c.n base t) t ∧
      JacWindowInput (jacWinCfg c) c.C base P (sv c base s V+16*Window5.geom 52) t ∧
      (∀ x∈winRo (jacWinCfg c),tmv c.C c.n base t x=tmv c.C c.n base s x) ∧
      t.sp=s.sp ∧ Unch base (winX c) s.mem t.mem ∧ t.rd=s.rd ∧ t.wr=s.wr := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hsz : size = 8192 := rfl
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  have hk : wordsVal s.mem base (c.sl V) c.n < 2 ^ (64 * c.n) := wordsVal_lt _ _ _ _
  have hk256 : wordsVal s.mem base (c.sl V) c.n < 2^256 := by simpa only [hn4] using hk
  have hrec := Window5.recode_lt hk256
  have hbound : 32^52 ≤ 2^(64*(c.n+1)) := by
    rw [show (32:Nat)=2^5 from rfl,← Nat.pow_mul]
    apply Nat.pow_le_pow_right
    · decide
    · rw [hn4]; decide
  have hsum := Nat.lt_of_lt_of_le hrec hbound
  have hoff : 16*Window5.geom 52 < 2^(64*(c.n+1)) := by omega
  have hWK : c.sl WK + 16 * c.n ≤ size := by
    have := sl_le' c h7 (i := WK + 1) (by decide)
    rw [sl_eq] at this ⊢; rw [Nat.mul_add] at this; omega
  have hKW := sl_lt c (show V < WK by decide)
  have h16 : (16 : Nat) ^ (16 * c.n + 1) ≤ 2 ^ (64 * (c.n + 1)) := by
    rw [show (16 : Nat) = 2 ^ 4 by rfl, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hJ : (winQ c).J = 16 * c.n + 1 := rfl
  have hK : c.winK = c.sl WK := rfl
  have hB : c.winBits = c.sl WB := rfl
  have e69 : c.sl WK + 16 * c.n = c.sl WB := by rw [sl_eq, sl_eq]; unfold WK WB; omega
  have hB4 : c.sl WB + 8 ≤ 4096 := by
    rw [sl_eq]; unfold WB
    have : 8 * c.n * 55 ≤ 8 * 9 * 55 := Nat.mul_le_mul_right _ (by omega)
    omega
  have hBs : c.sl WB + 64 * (c.n + 1) ≤ c.sl WT := by
    rw [sl_eq, sl_eq]; unfold WB WT
    have : 8 * c.n * 87 = 8 * c.n * 55 + 256 * c.n := by omega
    omega
  have hTs := sl_le' c h7 (i := WT) (by decide)
  rw [Impl.Ecdsa.Verify.AArch64.Cfg.jacWinPrep]
  rw [← hn4, show (40:Nat)=8*(c.n+1) by omega,
    show Impl.Ecdsa.Verify.AArch64.Cfg.jacOffset=16*Window5.geom 52 from Window5.offset_eq.symm]
  refine WP.seq ?_
  rw [hK]
  refine WP.mono (addConst_ok hs (n := c.n) (src := c.sl V) (dst := c.sl WK)
    (c := 16*Window5.geom 52) h0 h7 (sl_le c h7 (show V<45 by decide)) (by omega) (sl_mod8 c _) (sl_mod8 c _)
    (Or.inl (by omega)) hoff hsum) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (x0_not_clob _)
  rw [hB]
  refine WP.mono (bits_ok hs₁ (n := c.n + 1) (src := c.sl WK) (dst := c.sl WB) (by omega) (by omega)
    (by omega) (by omega) (by omega) hB4 (Or.inl (by omega))) fun s₂ ⟨b₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [e₁] at b₂
  have U₂ : Unch base (winX c) s.mem s₂.mem :=
    ((O₁.mono (o' := c.sl WK) (n' := 16 * c.n) (Nat.le_refl _) (by omega)).unch.trans
      ((O₂.mono (o' := c.sl WB) (n' := 64 * (c.n + 1)) (Nat.le_refl _) (by omega)).unch)).mono
      (by intro w hw; simpa [winX, hK, hB] using hw)
  have F₂ := F.unch h7 hn fixedOk_winX U₂
  have e₂ : ∀ {i}, i < 45 → sv c base s₂ i = sv c base s i := fun hi =>
    sv_unch U₂ h7 hn hi (apart_winX hi)
  have hM₂ := modP_of hc F₂.mp
  have tv : ∀ {i}, i < 45 → tmv c.C c.n base s₂ (c.sl i) = tmv c.C c.n base s (c.sl i) := fun hi => by
    show toM _ _ (sv c base s₂ _) = toM _ _ (sv c base s _); rw [e₂ hi]
  have hlt : ∀ x∈winRo (jacWinCfg c),wordsVal s₂.mem base x c.n<c.C.p := by
    intro x hx
    simp only [winRo,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt F₂.ap (hmont _)
    · exact lt_of_eq_of_lt F₂.bm (hmont _)
    · exact lt_of_eq_of_lt F₂.zero (by omega)
    · exact lt_of_eq_of_lt (e₂ (i:=PX) (by decide)) hpx
    · exact lt_of_eq_of_lt (e₂ (i:=PY) (by decide)) hpy
    · exact lt_of_eq_of_lt F₂.onep (Nat.mod_lt _ (by omega))
  have hI : Inv (jacWinCfg c).M base size c.C.p (·∈jacWinSlots (jacWinCfg c))
      (winRo (jacWinCfg c)) (tmv c.C c.n base s₂) s₂ :=
    ⟨hs₂,hM₂,fun _ hx => List.mem_append_left _ (List.mem_append_left _ hx),hlt,fun _ _ => rfl⟩
  have one : tmv c.C c.n base s₂ (c.sl ONEP)=1 := by
    change toM _ _ (wordsVal s₂.mem base (c.sl ONEP) c.n)=1
    rw [F₂.onep]
    have hm1 := toM_cmont hc 1
    have ho : Fin.ofNat c.C.p 1 = (1:Fe c.C) := by rfl
    simpa only [Cfg.mont,Cfg.R,Nat.one_mul,ho] using hm1
  have hp : Rep c.C (tmv c.C c.n base s₂ (c.sl PX)) (tmv c.C c.n base s₂ (c.sl PY))
      (tmv c.C c.n base s₂ (c.sl ONEP)) P := by
    rw [tv (by decide),tv (by decide),tv (by decide)]; exact hrep
  have hj : InvJ c.C (tmv c.C c.n base s₂ (c.sl PX)) (tmv c.C c.n base s₂ (c.sl PY))
      (tmv c.C c.n base s₂ (c.sl ONEP)) P := by
    have hh := InvJ.of_rep hC hp
    simpa only [one,Lean.Grind.Semiring.mul_one] using hh
  refine ⟨hI,⟨F₂.zero,fun i hi => b₂ i (by rw [hn4]; omega),hj⟩,?_,k₂.sp.trans k₁.sp,U₂,k₂.rd.trans k₁.rd,k₂.wr.trans k₁.wr⟩
  intro x hx
  simp only [winRo,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact tv (by decide)

end VG.Proof.Ecdsa.Verify.AArch64
