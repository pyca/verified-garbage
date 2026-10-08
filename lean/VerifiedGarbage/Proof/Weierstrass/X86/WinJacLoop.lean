import VerifiedGarbage.Proof.Weierstrass.X86.WinJacStep
import VerifiedGarbage.Proof.Weierstrass.X86.WinJacFirst
import VerifiedGarbage.Proof.Weierstrass.X86.WinJacFinish

/-! The complete constant-time signed-window multiplier. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem loop_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk k : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {P : Point C} (hP : onCurve C P=true) (hP0 : P≠.infinity) (hn17 : C.n%32=17) (hn64 : 64≤C.n)
    {s₀ s : State} (h : Accum K C base size wk P k s₀
      (Window5.winE (k+16*Window5.geom K.J) K.J (K.J-1)) s)
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p)
    (hz : tmv C K.M.n base s₀ K.zero=0) (hc : s.gpr .esi=BitVec.ofNat 32 (K.J-1))
    (hb : ∀ i<260,s₀.mem (off base (K.bits+i))=if (k+16*Window5.geom K.J).testBit i then 1 else 0) :
    WP isa (.loop K.step .ne) s (Accum K C base size wk P k s₀ k) := by
  refine WP.loop (M:=isa)
    (fun j t => 1≤j ∧ j<K.J ∧ Accum K C base size wk P k s₀
      (Window5.winE (k+16*Window5.geom K.J) K.J j) t ∧ t.gpr .esi=BitVec.ofNat 32 j)
    (fun j u ⟨h1,hj,hu,cu⟩ => ?_) (K.J-1) s
    ⟨by have := hL.J; omega,by have := hL.J; omega,h,hc⟩
  have cu' : u.gpr .esi=BitVec.ofNat 32 (j-1+1) := by rw [show j-1+1=j by omega]; exact cu
  have hu' : Accum K C base size wk P k s₀ (Window5.winE (k+16*Window5.geom K.J) K.J (j-1+1)) u := by
    rw [show j-1+1=j by omega]; exact hu
  refine WP.mono (step_ok hL hW hm hC ha hO hP hP0 hn17 hn64 hu' hro hz (by omega) cu' hb)
    fun t ⟨ht,ct,ft⟩ => ?_
  by_cases he : j=1
  · subst j
    refine Or.inl ⟨?_,?_⟩
    · change Option.map Bool.not t.zf=some false
      rw [ft]; rfl
    · simpa only [Nat.sub_self,Window5.winE_zero,Nat.add_sub_cancel] using ht
  · refine Or.inr ⟨?_,j-1,by omega,by omega,by omega,ht,ct⟩
    change Option.map Bool.not t.zf=some true
    rw [ft,decide_eq_false (by omega)]
    rfl

theorem window_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk k : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {P : Point C} (hP : onCurve C P=true) (hP0 : P≠.infinity) (hn17 : C.n%32=17) (hn64 : 64≤C.n)
    (hOne : K.one<C.p) (hOneM : toM C.p (2^(64*K.M.n)) K.one=1)
    {s : State} (hi : Inv K.M base size C.p (·∈slots K) (ro K) (tmv C K.M.n base s) s)
    (hJ : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y) (tmv C K.M.n base s K.P.z) P)
    (hz : tmv C K.M.n base s K.P.z=1) (h0 : wordsVal s.mem base K.zero K.M.n=0)
    (hb : ∀ i<260,s.mem (off base (K.bits+i))=if (k+16*Window5.geom K.J).testBit i then 1 else 0)
    (hrec : k+16*Window5.geom K.J<32^K.J) :
    WP isa K.window s fun t => Frame K C base size wk s t ∧
      (∀ x∈jacCoords K.R,wordsVal t.mem base x K.M.n<C.p) ∧
      (k<C.n → Rep C (tmv C K.M.n base t K.R.x) (tmv C K.M.n base t K.R.y)
        (tmv C K.M.n base t K.R.z) (mul k P)) := by
  have zero : tmv C K.M.n base s K.zero=0 := by unfold tmv; rw [h0,toM_zero]
  unfold JacWinCfg.window
  apply WP.seq
  refine WP.mono (build_ok hL hW hm hC ha hO (by omega) hP hP0 hi hJ hz) fun a ba => ?_
  apply WP.seq
  refine WP.mono (first_ok (k:=k) hL hW hm hC hP ba.frame ba.table hi.lt zero hb (Nat.le_add_left _ _) hrec)
    fun b ⟨ab,cb⟩ => ?_
  apply WP.seq
  refine WP.mono (loop_ok hL hW hm hC ha hO hP hP0 hn17 hn64 ab hi.lt zero cb hb) fun c ac => ?_
  refine WP.mono (finish_ok hL hW hm hC hOne hOneM ac hi.lt h0) fun t ⟨kt,_,lt,rt⟩ =>
    ⟨ac.frame.field hL hW kt (fun _ hx => hx),lt,rt⟩

end VG.Proof.Weierstrass.X86.JWin
