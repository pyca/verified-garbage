import VerifiedGarbage.Proof.Weierstrass.X86.WinJacCoZState

/-! Preserve the shared-Z invariant through public counters and table stores. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem SharedZ.keeps {K : JacWinCfg} {C : Curve} {base : Addr} {P : Point C} {s t : State}
    (h : SharedZ K C base P s) (hk : CKeeps [.esi] s t) : SharedZ K C base P t := by
  refine ⟨?_,?_⟩
  · intro x hx
    rw [hk.2.1]; exact h.lt x hx
  · simpa only [tmv,hk.2.1] using h.point

theorem co_store_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk m : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    {s₀ s : State} (h : Frame K C base size wk s₀ s) (hm : m<16)
    (hb : s.gpr .esi=BitVec.ofNat 32 (m+1)) {P : Point C}
    (ht : Table K C base P m s)
    (hp : Cached C base s (fun c => K.T+32*c) (mul (m+1) P))
    (hd : SharedZ K C base P s) :
    WP isa (.block K.storeEntry) s (CoBuildInv K C base size wk P s₀ (m+1)) := by
  have hT : K.T+160≤K.tbl := by
    have := hL.low K.z3 (by simp [slots,work])
    simp only [JacWinCfg.z3] at this
    omega
  refine WP.mono (store_table_ok h.scr hm hb hL.table hT ht hp)
    fun t ⟨ht,hu,hk⟩ => ⟨⟨h.store hL hW hm hu hk,ht,hp.store hL h.scr hu,
      (hk.gpr _ (by decide)).trans hb⟩,hd.store hL h.scr hu⟩

end VG.Proof.Weierstrass.X86.JWin
