import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableIO
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafState

/-! Public table transfers preserve the selected Jacobian point. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont Spec.Weierstrass

theorem Inv.transferPoint {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay M size Sl)
    {o q : Pt} (hy : o.y=o.x+8*M.n) (hz : o.z=o.x+16*M.n)
    {V : List Nat} {E : Nat → Fe C} {s t : State}
    (hI : Inv M base size C.p Sl V E s)
    (hD : ∀ x∈jacCoords o, Sl x) (hQ : ∀ x∈jacCoords q, x∈V)
    (vx : wordsVal t.mem base o.x M.n=wordsVal s.mem base q.x M.n)
    (vy : wordsVal t.mem base o.y M.n=wordsVal s.mem base q.y M.n)
    (vz : wordsVal t.mem base o.z M.n=wordsVal s.mem base q.z M.n)
    (hk : KeepRegs [.rax,.rcx,.rdx] s t) (ho : Outside base o.x (24*M.n) s.mem t.mem)
    {P : Point C} (hJ : InvJ C (E q.x) (E q.y) (E q.z) P) :
    ProgKeep M base (jacCoords o) s t ∧
    Inv M base size C.p Sl (jacCoords o++V) (tmv C M.n base t) t ∧
    InvJ C (tmv C M.n base t o.x) (tmv C M.n base t o.y) (tmv C M.n base t o.z) P := by
  have kp : ProgKeep M base (jacCoords o) s t := by
    refine ⟨fun r hr => hk.gpr r (fun hh => hr ?_),hk.rd,hk.wr,fun x hx _ => ho x ?_⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
      rcases hh with rfl | rfl | rfl <;> simp [clob]
    · have hx₀ := hx o.x (by simp [jacCoords])
      have hx₁ := hx o.y (by simp [jacCoords])
      have hx₂ := hx o.z (by simp [jacCoords])
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
  refine ⟨kp,hI.of_progKeep hL kp hD hlt,?_⟩
  unfold tmv
  rw [vx,vy,vz,hI.val _ (hQ _ (by simp [jacCoords])),
    hI.val _ (hQ _ (by simp [jacCoords])),hI.val _ (hQ _ (by simp [jacCoords]))]
  exact hJ

theorem nafPublicPoint_ok {K : WinCfg} {base : Addr} {size a : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hn : K.M.n=4 ∨ K.M.n=6)
    (hy : K.E.y=K.E.x+8*K.M.n) (hz : K.E.z=K.E.x+16*K.M.n)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s)
    (h8 : s.gpr .r8=BitVec.ofNat 64 a) (ha : 1≤a) (ha' : a≤15)
    (ht : K.tbl<2^31) (hT : K.tbl+192*K.M.n≤size)
    (hD : ∀ x∈jacCoords K.E, Sl x)
    (hQ : ∀ x∈jacCoords (K.tblPt ((a-1)/2+1)), x∈V)
    (hSep : K.E.x+24*K.M.n≤K.tbl ∨ K.tbl+192*K.M.n≤K.E.x)
    {P : Point C} (hJ : InvJ C (E (K.tblPt ((a-1)/2+1)).x)
      (E (K.tblPt ((a-1)/2+1)).y) (E (K.tblPt ((a-1)/2+1)).z) P) :
    WP isa (.block (Naf.publicEntry K)) s fun t =>
      ProgKeep K.M base (jacCoords K.E) s t ∧
      Inv K.M base size C.p Sl (jacCoords K.E++V) (tmv C K.M.n base t) t ∧
      InvJ C (tmv C K.M.n base t K.E.x) (tmv C K.M.n base t K.E.y)
        (tmv C K.M.n base t K.E.z) P := by
  have hdz := hL.le K.E.z (hD _ (by simp [jacCoords]))
  rw [hz] at hdz
  refine WP.mono (nafPublicEntry_ok hI.scr ha ha' h8 hn ht hT (by omega) hSep)
    fun t ⟨hv,hk,ho⟩ => hI.transferPoint hL hy hz hD hQ ?_ ?_ ?_ hk ho hJ
  · simpa only [WinCfg.tblPt,Nat.add_sub_cancel,Nat.mul_zero,Nat.add_zero] using hv 0 (by decide)
  · simpa only [hy,WinCfg.tblPt,Nat.add_sub_cancel,Nat.mul_one] using hv 1 (by decide)
  · simpa only [hz,WinCfg.tblPt,Nat.add_sub_cancel,show 8*K.M.n*2=16*K.M.n by omega]
      using hv 2 (by decide)

theorem nafTablePoint_ok {K : WinCfg} {base : Addr} {size j : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hn : K.M.n=4 ∨ K.M.n=6)
    (hy : K.R.y=K.R.x+8*K.M.n) (hz : K.R.z=K.R.x+16*K.M.n)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s)
    (hj : j<8) (hc : s.gpr .rbx=BitVec.ofNat 64 j)
    (ht : K.tbl<2^31) (hT : K.tbl+192*K.M.n≤size)
    (hD : ∀ x∈jacCoords (K.tblPt (j+1)), Sl x)
    (hQ : ∀ x∈jacCoords K.R, x∈V)
    (hSep : K.R.x+24*K.M.n≤K.tbl ∨ K.tbl+192*K.M.n≤K.R.x)
    {P : Point C} (hJ : InvJ C (E K.R.x) (E K.R.y) (E K.R.z) P) :
    WP isa (.block (Naf.tableStore K)) s fun t =>
      ProgKeep K.M base (jacCoords (K.tblPt (j+1))) s t ∧
      Inv K.M base size C.p Sl (jacCoords (K.tblPt (j+1))++V) (tmv C K.M.n base t) t ∧
      InvJ C (tmv C K.M.n base t (K.tblPt (j+1)).x)
        (tmv C K.M.n base t (K.tblPt (j+1)).y) (tmv C K.M.n base t (K.tblPt (j+1)).z) P := by
  have hrz := hL.le K.R.z (hI.sl _ (hQ _ (by simp [jacCoords])))
  rw [hz] at hrz
  refine WP.mono (nafTableStore_ok hI.scr hj hc hn ht hT (by omega) hSep)
    fun t ⟨hv,hk,ho⟩ => hI.transferPoint hL ?_ ?_ hD hQ ?_ ?_ ?_ hk ?_ hJ
  · simp only [WinCfg.tblPt]
  · simp only [WinCfg.tblPt]
  · simpa only [WinCfg.tblPt,Nat.add_sub_cancel,Nat.mul_zero,Nat.add_zero] using hv 0 (by decide)
  · simpa only [hy,WinCfg.tblPt,Nat.add_sub_cancel,Nat.mul_one] using hv 1 (by decide)
  · simpa only [hz,WinCfg.tblPt,Nat.add_sub_cancel,show 8*K.M.n*2=16*K.M.n by omega]
      using hv 2 (by decide)
  · simpa only [WinCfg.tblPt,Nat.add_sub_cancel] using ho

end VG.Proof.Weierstrass.X86_64
