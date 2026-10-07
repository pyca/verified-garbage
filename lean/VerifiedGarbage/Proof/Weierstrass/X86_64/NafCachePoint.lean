import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCache
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafPoint

/-! A public cache lookup preserves the point and its Z²/Z³ relationships. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64
open VG.Impl.Weierstrass VG.Proof.Mont.X86_64 VG.Proof.Mont Spec.Weierstrass

def cachedSlots (n : Nat) (p : Pt) (dst : Nat) : List Nat := jacCoords p++[dst,dst+8*n]

theorem Inv.transferCachedPoint {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay M size Sl)
    {o q : Pt} {dst src : Nat} (hy : o.y=o.x+8*M.n) (hz : o.z=o.x+16*M.n)
    {V : List Nat} {E : Nat → Fe C} {s t : State}
    (hI : Inv M base size C.p Sl V E s)
    (hD : ∀ x∈cachedSlots M.n o dst,Sl x) (hQ : ∀ x∈cachedSlots M.n q src,x∈V)
    (vx : wordsVal t.mem base o.x M.n=wordsVal s.mem base q.x M.n)
    (vy : wordsVal t.mem base o.y M.n=wordsVal s.mem base q.y M.n)
    (vz : wordsVal t.mem base o.z M.n=wordsVal s.mem base q.z M.n)
    (v2 : wordsVal t.mem base dst M.n=wordsVal s.mem base src M.n)
    (v3 : wordsVal t.mem base (dst+8*M.n) M.n=wordsVal s.mem base (src+8*M.n) M.n)
    (hk : KeepRegs [.rax,.rcx,.rdx] s t)
    (ho : ∀ x,(ofs base x<o.x ∨ o.x+24*M.n≤ofs base x) →
      (ofs base x<dst ∨ dst+16*M.n≤ofs base x) → t.mem x=s.mem x)
    {P : Point C} (hJ : InvJ C (E q.x) (E q.y) (E q.z) P)
    (h2 : E src=E q.z*E q.z) (h3 : E (src+8*M.n)=E src*E q.z) :
    ProgKeep M base (cachedSlots M.n o dst) s t ∧
    Inv M base size C.p Sl (cachedSlots M.n o dst++V) (tmv C M.n base t) t ∧
    InvJ C (tmv C M.n base t o.x) (tmv C M.n base t o.y) (tmv C M.n base t o.z) P ∧
    tmv C M.n base t dst=tmv C M.n base t o.z*tmv C M.n base t o.z ∧
    tmv C M.n base t (dst+8*M.n)=tmv C M.n base t dst*tmv C M.n base t o.z := by
  have kp : ProgKeep M base (cachedSlots M.n o dst) s t := by
    refine ⟨fun r hr => hk.gpr r (fun hh => hr ?_),hk.rd,hk.wr,fun x hx _ => ho x ?_ ?_⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
      rcases hh with rfl|rfl|rfl <;> simp [clob]
    · have hx0 := hx o.x (by simp [cachedSlots,jacCoords])
      have hx1 := hx o.y (by simp [cachedSlots,jacCoords])
      have hx2 := hx o.z (by simp [cachedSlots,jacCoords])
      rw [hy] at hx1
      rw [hz] at hx2
      omega
    · have hx0 := hx dst (by simp [cachedSlots])
      have hx1 := hx (dst+8*M.n) (by simp [cachedSlots])
      omega
  have hlt : ∀ x∈cachedSlots M.n o dst,wordsVal t.mem base x M.n<C.p := by
    intro x hx
    simp only [cachedSlots,jacCoords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with (rfl|rfl|rfl)|(rfl|rfl)
    · rw [vx]; exact hI.lt _ (hQ _ (by simp [cachedSlots,jacCoords]))
    · rw [vy]; exact hI.lt _ (hQ _ (by simp [cachedSlots,jacCoords]))
    · rw [vz]; exact hI.lt _ (hQ _ (by simp [cachedSlots,jacCoords]))
    · rw [v2]; exact hI.lt _ (hQ _ (by simp [cachedSlots]))
    · rw [v3]; exact hI.lt _ (hQ _ (by simp [cachedSlots]))
  refine ⟨kp,hI.of_progKeep hL kp hD hlt,?_⟩
  unfold tmv
  rw [vx,vy,vz,v2,v3,hI.val _ (hQ _ (by simp [cachedSlots,jacCoords])),
    hI.val _ (hQ _ (by simp [cachedSlots,jacCoords])),
    hI.val _ (hQ _ (by simp [cachedSlots,jacCoords])),
    hI.val _ (hQ _ (by simp [cachedSlots])),hI.val _ (hQ _ (by simp [cachedSlots]))]
  exact ⟨hJ,h2,h3⟩

theorem nafCachedPoint_ok {K : WinCfg} {base : Addr} {size tbl dst a : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hn : K.M.n=4 ∨ K.M.n=6)
    (hy : K.E.y=K.E.x+8*K.M.n) (hz : K.E.z=K.E.x+16*K.M.n)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s)
    (h8 : s.gpr .r8=BitVec.ofNat 64 a) (ha : 1≤a) (ha' : a≤15) (hodd : a%2=1)
    (hp : K.tbl<2^31) (hc : tbl<2^31)
    (hP : K.tbl+192*K.M.n≤size) (hC : tbl+128*K.M.n≤size)
    (hD : ∀ x∈cachedSlots K.M.n K.E dst,Sl x)
    (hQ : ∀ x∈cachedSlots K.M.n (K.tblPt ((a-1)/2+1)) (tbl+16*K.M.n*((a-1)/2)),x∈V)
    (hEP : K.E.x+24*K.M.n≤K.tbl ∨ K.tbl+192*K.M.n≤K.E.x)
    (hEC : K.E.x+24*K.M.n≤tbl ∨ tbl+128*K.M.n≤K.E.x)
    (hDC : dst+16*K.M.n≤tbl ∨ tbl+128*K.M.n≤dst)
    (hDE : dst+16*K.M.n≤K.E.x ∨ K.E.x+24*K.M.n≤dst)
    {P : Point C} (hJ : InvJ C (E (K.tblPt ((a-1)/2+1)).x)
      (E (K.tblPt ((a-1)/2+1)).y) (E (K.tblPt ((a-1)/2+1)).z) P)
    (h2 : E (tbl+16*K.M.n*((a-1)/2))=
      E (K.tblPt ((a-1)/2+1)).z*E (K.tblPt ((a-1)/2+1)).z)
    (h3 : E (tbl+16*K.M.n*((a-1)/2)+8*K.M.n)=
      E (tbl+16*K.M.n*((a-1)/2))*E (K.tblPt ((a-1)/2+1)).z) :
    WP isa (.block (Naf.cachedEntry K tbl dst)) s fun t =>
      ProgKeep K.M base (cachedSlots K.M.n K.E dst) s t ∧
      Inv K.M base size C.p Sl (cachedSlots K.M.n K.E dst++V) (tmv C K.M.n base t) t ∧
      InvJ C (tmv C K.M.n base t K.E.x) (tmv C K.M.n base t K.E.y)
        (tmv C K.M.n base t K.E.z) P ∧
      tmv C K.M.n base t dst=tmv C K.M.n base t K.E.z*tmv C K.M.n base t K.E.z ∧
      tmv C K.M.n base t (dst+8*K.M.n)=tmv C K.M.n base t dst*tmv C K.M.n base t K.E.z := by
  have hez := hL.le K.E.z (hD _ (by simp [cachedSlots,jacCoords]))
  have hd3 := hL.le (dst+8*K.M.n) (hD _ (by simp [cachedSlots]))
  rw [hz] at hez
  refine WP.mono (nafCachedEntry_ok hI.scr h8 ha ha' hodd hn hp hc hP hC
    (by omega) (by omega) hEP hEC hDC hDE) fun t ⟨vp,vc,hk,ho⟩ =>
      hI.transferCachedPoint hL hy hz hD hQ ?_ ?_ ?_ ?_ ?_ hk ho hJ h2 h3
  · simpa only [WinCfg.tblPt,Nat.add_sub_cancel,Nat.mul_zero,Nat.add_zero] using vp 0 (by decide)
  · simpa only [hy,WinCfg.tblPt,Nat.add_sub_cancel,Nat.mul_one] using vp 1 (by decide)
  · simpa only [hz,WinCfg.tblPt,Nat.add_sub_cancel,show 8*K.M.n*2=16*K.M.n by omega]
      using vp 2 (by decide)
  · simpa only [Nat.mul_zero,Nat.add_zero] using vc 0 (by decide)
  · simpa only [Nat.mul_one] using vc 1 (by decide)

end VG.Proof.Weierstrass.X86_64
