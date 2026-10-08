import VerifiedGarbage.Proof.Weierstrass.X86.WinJacEntryState

/-! Read a signed-window magnitude and scan both packed tables. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem read_fields_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk v j : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    {P : Point C} {s₀ s : State} (h : Frame K C base size wk s₀ s)
    (ht : Table K C base P 16 s)
    (hj : j<52) (hc : s.gpr .esi=BitVec.ofNat 32 j)
    (hb : ∀ i<260,s₀.mem (off base (K.bits+i))=if v.testBit i then 1 else 0) :
    WP isa (.block (K.tc.digit++K.select)) s fun t =>
      Entry K C base (mul (magH 16 (Window5.nib v j)) P) t ∧
      ProgKeep K.M base wk (coords K) s t ∧ t.gpr .esi=BitVec.ofNat 32 j := by
  have hs : K.bits+260≤size := by have := hL.bits; have := hL.table; omega
  have bits : ∀ i<260,s.mem (off base (K.bits+i))=if v.testBit i then 1 else 0 := by
    intro i hi; rw [h.bits hL hi]; exact hb i hi
  rw [WP.block_append_iff]
  refine WP.mono (digit_ok K.tc h.scr (k:=v) (N:=260) (by change 1≤5; decide) (by change 5<9; decide)
    (by change 5*j+5≤260; omega) hs hc bits) fun a ⟨_,ma,ka⟩ => ?_
  have kp : ProgKeep K.M base wk [] s a := keep_of_ckeeps (ka.mono (by decide))
  have ac := h.field hL hW kp (by simp)
  have ea : a.gpr .ebx=BitVec.ofNat 32 (magH 16 (Window5.nib v j)) := by
    simpa only [JacWinCfg.tc,TCombCfg.H,Window5.combWin_five] using ma
  have mag : magH 16 (Window5.nib v j)≤16 := magH_le (by
    have := Nat.mod_lt (v/32^j) (show 0<32 by decide)
    change Window5.nib v j<2*16
    exact this)
  refine WP.mono (select_entry_ok hL ac.scr mag ea (ht.field_keep hL h.scr kp (by simp) (by decide))) fun t ⟨pt,kt⟩ => ?_
  refine ⟨pt,(kp.mono (by simp)).trans kt,?_⟩
  exact (kt.gpr _ (by decide)).trans ((ka.1 _ (by decide)).trans hc)

end VG.Proof.Weierstrass.X86.JWin
