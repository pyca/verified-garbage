import VerifiedGarbage.Proof.Weierstrass.X86.WinJacEntryState

/-! Read a signed-window magnitude and scan both packed tables. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem read_entry_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk k e v j : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    {P : Point C} {s₀ s : State} (h : Accum K C base size wk P k s₀ e s)
    (hj : j<52) (hc : s.gpr .esi=BitVec.ofNat 32 j)
    (hb : ∀ i<260,s₀.mem (off base (K.bits+i))=if v.testBit i then 1 else 0) :
    WP isa (.block (K.tc.digit++K.select)) s fun t =>
      Accum K C base size wk P k s₀ e t ∧
      Entry K C base (mul (magH 16 (Window5.nib v j)) P) t ∧ t.gpr .esi=BitVec.ofNat 32 j := by
  have hs : K.bits+260≤size := by have := hL.bits; have := hL.table; omega
  have bits : ∀ i<260,s.mem (off base (K.bits+i))=if v.testBit i then 1 else 0 := by
    intro i hi; rw [h.frame.bits hL hi]; exact hb i hi
  rw [WP.block_append_iff]
  refine WP.mono (digit_ok K.tc h.frame.scr (k:=v) (N:=260) (by change 1≤5; decide) (by change 5<9; decide)
    (by change 5*j+5≤260; omega) hs hc bits) fun a ⟨_,ma,ka⟩ => ?_
  have kp : ProgKeep K.M base wk [] s a := keep_of_ckeeps (ka.mono (by decide))
  have ac := h.preserve hL hW kp (by simp) (by simp)
  have ea : a.gpr .ebx=BitVec.ofNat 32 (magH 16 (Window5.nib v j)) := by
    simpa only [JacWinCfg.tc,TCombCfg.H,Window5.combWin_five] using ma
  have mag : magH 16 (Window5.nib v j)≤16 := magH_le (by
    have := Nat.mod_lt (v/32^j) (show 0<32 by decide)
    change Window5.nib v j<2*16
    exact this)
  refine WP.mono (select_entry_ok hL ac.frame.scr mag ea ac.table) fun t ⟨pt,kt⟩ => ?_
  refine ⟨ac.preserve hL hW kt (coords_work K) (fun x hx hy =>
    entry_apart_R hL x hx (List.mem_append_left _ hy)),pt,?_⟩
  exact (kt.gpr _ (by decide)).trans ((ka.1 _ (by decide)).trans hc)

end VG.Proof.Weierstrass.X86.JWin
