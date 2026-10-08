import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafMulSetup

/-! # The x86 P-256 variable-base product -/

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86 VG.Impl.Ecdsa.Verify.X86
open VG.Impl.Ecdh.X86 (PX PY)
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass
open VG.Proof.Ecdsa.X86 Spec.Weierstrass
variable {c : Impl.Ecdsa.X86.Cfg}

theorem windowMulQ_ok (hc : CfgOk c) (h4 : c.n = 4) (hC : Law c.C) (hM3 : AM3 c.C)
    {s : State} {base : Addr} {g : Reg → BitVec 32} (hs : Scr s base size) (F : Fixed c base g s.mem)
    {P : Point c.C} (hP : onCurve c.C P = true)
    (hpx : sv c base s PX < c.C.p) (hpy : sv c base s PY < c.C.p)
    (hQ : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P) :
    WP isa (Impl.Ecdsa.Verify.X86.Cfg.windowMulQ c) s fun u =>
      Keeps powClob s u ∧ Unch base (windowW c) s.mem u.mem ∧
      ModOkW c.MP' size c.C.p u.mem base ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal u.mem base x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n base u (c.sl RX)) (tmv c.C c.n base u (c.sl RY))
        (tmv c.C c.n base u (c.sl RZ)) (mul (sv c base s V) P) := by
  have hp := hc.p_ge
  have hmont : ∀ x,c.mont x<c.C.p := fun _ => Nat.mod_lt _ (by omega)
  let K := Cfg.nafQ c
  have hL := nafQLay (c:=c) h4
  have hW := nafQWk hc h4
  have hm := unitMod_pow_two hc.p_odd (64*c.n)
  have hk : sv c base s V<2^256 := by
    change wordsVal s.mem base (c.sl V) c.n<_
    rw [h4]; exact wordsVal_lt ..
  unfold Cfg.windowMulQ
  apply WP.assoc
  apply WP.seq
  refine WP.mono (windowMulQ_setup_ok hc h4 hC hs F hpx hpy hQ)
    fun s₂ ⟨k₂,u₂,_,i₂,p₂,_,_,_,_⟩ => ?_
  refine WP.seq (WP.mono (nafWindow_ok hL rfl hW (by change 3580+260≤Mont.own c.n; rw [h4]; decide)
    hm hC hM3 (hmont 1) hk hP i₂ p₂.point p₂.zero p₂.bits) fun s₃ ⟨k₃,u₃,c₃⟩ => ?_)
  refine WP.mono (nafFinish_ok hL hW hm hC (hmont 1)
    (by change toM c.C.p (2^(64*c.n)) (c.mont 1)=1; rw [toM_cmont hc]; rfl) c₃)
    fun u ⟨ku,Mu,Lu,qu⟩ => ?_
  have UW₃ := u₃.cover (nafQ_cover h4)
  have UW₄ := (nafTable_progUnch ku (fun _ hx => List.mem_append_left _ hx)).cover (nafQ_cover h4)
  exact ⟨k₂.trans ((k₃.mono (by change ∀ r∈clob++[Reg.esi],r∈powClob; decide)).trans
      (Keeps.mono ⟨ku.gpr,ku.rd,ku.wr⟩ (by decide))),
    fun x hx => (UW₄ x hx).trans ((UW₃ x hx).trans (u₂ x hx)),Mu,Lu,qu⟩

end VG.Proof.Ecdsa.Verify.X86
