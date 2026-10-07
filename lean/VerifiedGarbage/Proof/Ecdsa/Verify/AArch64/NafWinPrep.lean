import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacLayout
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafWindowTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafPrep

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (V)
open VG.Impl.Ecdsa.Verify.AArch64.Cfg (jacWinCfg)
variable {c : Cfg}

theorem nafWinPrep_ok (hc : CfgOk c) (hn4 : c.n=4) (hC : Law c.C) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (F : Fixed c base g s.mem) {P : Point c.C}
    (hpx : sv c base s PX < c.C.p) (hpy : sv c base s PY < c.C.p)
    (hrep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P)
 :
    WP isa (Impl.Ecdsa.Verify.AArch64.Cfg.nafWinPrep c) s fun t =>
      Inv (jacWinCfg c).M base size c.C.p (·∈jacWinSlots (jacWinCfg c))
        (winRo (jacWinCfg c)) (tmv c.C c.n base t) t ∧
      NafWindowInput (jacWinCfg c) c.C base P (sv c base s V) t ∧
      (∀ x∈winRo (jacWinCfg c),tmv c.C c.n base t x=tmv c.C c.n base s x) ∧
      t.sp=s.sp ∧ Unch base (winX c) s.mem t.mem ∧ t.rd=s.rd ∧ t.wr=s.wr := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  have hB : (jacWinCfg c).bits = c.sl WB := rfl
  rw [Impl.Ecdsa.Verify.AArch64.Cfg.nafWinPrep]
  refine WP.mono (nafPrep_ok (jacWinCfg c) hs
    (by simpa only [hn4] using sl_le c h7 (i:=V) (by decide)) (sl_mod8 c _)
    (by rw [hB,sl_eq,hn4]; decide)
    (by rw [hB,sl_eq,hn4]; decide)) fun s₂ ⟨p₂,k₂,O₂⟩ => ?_
  have hs₂ := p₂.scr
  have b₂ := p₂.digits
  rw [←hn4] at b₂
  have U₂ : Unch base (winX c) s.mem s₂.mem := by
    have u := (O₂.mono (o':=c.sl WB) (n':=64*(c.n+1)) (by rw [hB]) (by rw [hB,hn4]; omega)).unch
    exact u.mono (by intro w hw; simp only [List.mem_singleton] at hw; subst hw; change _ ∈ [(c.winK,16*c.n),(c.winBits,64*(c.n+1))]; exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))
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
  refine ⟨hI,⟨F₂.zero,fun i hi => b₂ i hi,hj⟩,?_,k₂.sp,U₂,k₂.rd,k₂.wr⟩
  intro x hx
  simp only [winRo,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact tv (by decide)

end VG.Proof.Ecdsa.Verify.AArch64
