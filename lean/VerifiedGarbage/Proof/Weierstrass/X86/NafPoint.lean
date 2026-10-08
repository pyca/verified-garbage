import VerifiedGarbage.Proof.Weierstrass.X86.NafTableIO
import VerifiedGarbage.Proof.Weierstrass.X86.NafState

/-! Public table transfers preserve the selected Jacobian point. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont Spec.Weierstrass

theorem Inv.transferPoint {F : Spec.Weierstrass.Mont.Modulus} {M : Mod} {base : Addr} {size wk : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAcc : WkOk F M C.p size wk Sl) (hn : M.n=4)
    {o q : Pt} (hy : o.y=o.x+32) (hz : o.z=o.x+64)
    {V : List Nat} {E : Nat → Fe C} {s t : State}
    (hI : Inv M base size C.p Sl V E s)
    (hD : ∀ x∈jacCoords o, Sl x) (hQ : ∀ x∈jacCoords q, x∈V)
    (vx : wordsVal t.mem base o.x M.n=wordsVal s.mem base q.x M.n)
    (vy : wordsVal t.mem base o.y M.n=wordsVal s.mem base q.y M.n)
    (vz : wordsVal t.mem base o.z M.n=wordsVal s.mem base q.z M.n)
    (hk : KeepRegs [.eax,.ecx,.edx] s t) (ho : Outside base o.x 96 s.mem t.mem)
    {P : Point C} (hJ : InvJ C (E q.x) (E q.y) (E q.z) P) :
    ProgKeep M base wk (jacCoords o) s t ∧
    Inv M base size C.p Sl (jacCoords o++V) (tmv C M.n base t) t ∧
    InvJ C (tmv C M.n base t o.x) (tmv C M.n base t o.y) (tmv C M.n base t o.z) P := by
  have kp : ProgKeep M base wk (jacCoords o) s t := by
    refine ⟨fun r hr => hk.gpr r (fun hh => hr ?_),hk.rd,hk.wr,fun x hx => ho x ?_⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
      rcases hh with rfl | rfl | rfl <;> simp [clob]
    · have hx₀ := hx (o.x,8*M.n) (by simp [progW,jacCoords])
      have hx₁ := hx (o.y,8*M.n) (by simp [progW,jacCoords])
      have hx₂ := hx (o.z,8*M.n) (by simp [progW,jacCoords])
      simp only [hn] at hx₀ hx₁ hx₂
      rw [hy] at hx₁
      rw [hz] at hx₂
      omega
  have hlt : ∀ x∈jacCoords o, wordsVal t.mem base x M.n<C.p := by
    intro x hx
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [vx]; exact hI.lt _ (hQ _ (by simp [jacCoords]))
    · rw [vy]; exact hI.lt _ (hQ _ (by simp [jacCoords]))
    · rw [vz]; exact hI.lt _ (hQ _ (by simp [jacCoords]))
  refine ⟨kp,hI.of_progKeep hL hAcc kp hD hlt,?_⟩
  unfold tmv
  rw [vx,vy,vz,hI.val _ (hQ _ (by simp [jacCoords])),
    hI.val _ (hQ _ (by simp [jacCoords])),hI.val _ (hQ _ (by simp [jacCoords]))]
  exact hJ

theorem nafPublicPoint_ok {F : Spec.Weierstrass.Mont.Modulus} {K : WinCfg} {base : Addr} {size a wk : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAcc : WkOk F K.M C.p size wk Sl) (hn : K.M.n=4)
    (hy : K.E.y=K.E.x+32) (hz : K.E.z=K.E.x+64)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s)
    (h8 : s.gpr .ebx=BitVec.ofNat 32 a) (ha : 1≤a) (ha' : a≤15)
    (hT : K.tbl+768≤size)
    (hD : ∀ x∈jacCoords K.E, Sl x)
    (hQ : ∀ x∈jacCoords (K.tblPt ((a-1)/2+1)), x∈V)
    (hSep : K.E.x+96≤K.tbl ∨ K.tbl+768≤K.E.x)
    {P : Point C} (hJ : InvJ C (E (K.tblPt ((a-1)/2+1)).x)
      (E (K.tblPt ((a-1)/2+1)).y) (E (K.tblPt ((a-1)/2+1)).z) P) :
    WP isa (.block (Naf.publicEntry K)) s fun t =>
      ProgKeep K.M base wk (jacCoords K.E) s t ∧
      Inv K.M base size C.p Sl (jacCoords K.E++V) (tmv C K.M.n base t) t ∧
      InvJ C (tmv C K.M.n base t K.E.x) (tmv C K.M.n base t K.E.y)
        (tmv C K.M.n base t K.E.z) P := by
  have hdz := hL.le K.E.z (hD _ (by simp [jacCoords]))
  rw [hn,hz] at hdz
  refine WP.mono (nafPublicEntry_ok hI.scr ha ha' h8 hT (by omega) hSep)
    fun t ⟨hv,hk,ho⟩ => hI.transferPoint hL hAcc hn hy hz hD hQ ?_ ?_ ?_ hk ho hJ
  · simpa only [hn,WinCfg.tblPt,Nat.add_sub_cancel,Nat.mul_zero,Nat.add_zero,
      show 24*4=96 from rfl] using hv 0 (by decide)
  · simpa only [hn,hy,WinCfg.tblPt,Nat.add_sub_cancel,Nat.mul_one,
      show 24*4=96 from rfl,show 8*4=32 from rfl] using hv 1 (by decide)
  · simpa only [hn,hz,WinCfg.tblPt,Nat.add_sub_cancel,
      show 24*4=96 from rfl,show 16*4=64 from rfl,show 32*2=64 from rfl] using hv 2 (by decide)

theorem nafTablePoint_ok {F : Spec.Weierstrass.Mont.Modulus} {K : WinCfg} {base : Addr} {size j wk : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAcc : WkOk F K.M C.p size wk Sl) (hn : K.M.n=4)
    (hy : K.R.y=K.R.x+32) (hz : K.R.z=K.R.x+64)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s)
    (hj : j<8) (hc : s.gpr .esi=BitVec.ofNat 32 j)
    (hT : K.tbl+768≤size)
    (hD : ∀ x∈jacCoords (K.tblPt (j+1)), Sl x)
    (hQ : ∀ x∈jacCoords K.R, x∈V)
    (hSep : K.R.x+96≤K.tbl ∨ K.tbl+768≤K.R.x)
    {P : Point C} (hJ : InvJ C (E K.R.x) (E K.R.y) (E K.R.z) P) :
    WP isa (.block (Naf.tableStore K)) s fun t =>
      ProgKeep K.M base wk (jacCoords (K.tblPt (j+1))) s t ∧
      Inv K.M base size C.p Sl (jacCoords (K.tblPt (j+1))++V) (tmv C K.M.n base t) t ∧
      InvJ C (tmv C K.M.n base t (K.tblPt (j+1)).x)
        (tmv C K.M.n base t (K.tblPt (j+1)).y) (tmv C K.M.n base t (K.tblPt (j+1)).z) P := by
  have hrz := hL.le K.R.z (hI.sl _ (hQ _ (by simp [jacCoords])))
  rw [hn,hz] at hrz
  refine WP.mono (nafTableStore_ok hI.scr hj hc hT (by omega) hSep)
    fun t ⟨hv,hk,ho⟩ => hI.transferPoint hL hAcc hn ?_ ?_ hD hQ ?_ ?_ ?_ hk ?_ hJ
  · simp only [WinCfg.tblPt,hn]
  · simp only [WinCfg.tblPt,hn]
  · simpa only [hn,WinCfg.tblPt,Nat.add_sub_cancel,Nat.mul_zero,Nat.add_zero,
      show 24*4=96 from rfl] using hv 0 (by decide)
  · simpa only [hn,hy,WinCfg.tblPt,Nat.add_sub_cancel,Nat.mul_one,
      show 24*4=96 from rfl,show 8*4=32 from rfl] using hv 1 (by decide)
  · simpa only [hn,hz,WinCfg.tblPt,Nat.add_sub_cancel,
      show 24*4=96 from rfl,show 16*4=64 from rfl,show 32*2=64 from rfl] using hv 2 (by decide)
  · simpa only [WinCfg.tblPt,hn,Nat.add_sub_cancel,show 24*4=96 from rfl] using ho

end VG.Proof.Weierstrass.X86
