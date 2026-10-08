import VerifiedGarbage.Proof.Weierstrass.X86.WinJacScan

/-! Selection of a complete cached Jacobian entry with two SSE2 scans. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

theorem select_ok {K : JacWinCfg} {s : State} {base : Addr} {size a : Nat}
    (hs : Scr s base size) (ha : a≤16) (hb : s.gpr .ebx=BitVec.ofNat 32 a)
    (ht : K.tbl+2560≤size) (ho : K.T+160≤size) (hsep : K.T+160≤K.tbl) :
    WP isa (.block K.select) s fun t =>
      (∀ c<5,wordsVal t.mem base (K.T+32*c) 4=
        if 1≤a then wordsVal s.mem base (K.entry (a-1) c) 4 else 0) ∧
      Outside base K.T 160 s.mem t.mem ∧ KeepRegs [.ecx,.edx] s t := by
  rw [JacWinCfg.select,WP.block_append_iff]
  refine WP.mono (selectPart_ok false hs ha hb ht ho) fun u ⟨eu,ou,ku⟩ => ?_
  simp only [Bool.false_eq_true,ite_false,Nat.add_zero] at eu ou
  have hu := hs.of_keepRegs ku (by decide)
  refine WP.mono (selectPart_ok true hu ha ((ku.gpr _ (by decide)).trans hb) ht ho)
    fun t ⟨et,ot,kt⟩ => ?_
  simp only [ite_true] at et ot
  have hn := hs.nowrap
  refine ⟨fun c hc => ?_,
    (ou.mono (Nat.le_refl _) (by omega)).trans (ot.mono (by omega) (by omega)),
    ⟨fun r hr => (kt.gpr r hr).trans (ku.gpr r hr),kt.rd.trans ku.rd,kt.wr.trans ku.wr⟩⟩
  by_cases h3 : c<3
  · rw [ot.wordsVal (by omega) (by omega),eu c h3]
    simp only [JacWinCfg.entry,h3,ite_true]
  · have e := et (c-3) (by omega)
    rw [show K.T+96+32*(c-3)=K.T+32*c by omega] at e
    rw [e]
    by_cases h1 : 1≤a
    · simp only [h1,ite_true,JacWinCfg.entry,h3,ite_false]
      exact ou.wordsVal (by omega) (by omega)
    · simp only [h1,ite_false]

end VG.Proof.Weierstrass.X86.JWin
