import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCache
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCachePoint

/-! Exact field values after a public lookup of a point and its cached powers. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64
open VG.Impl.Weierstrass VG.Proof.Mont.X86_64 VG.Proof.Mont Spec.Weierstrass

def cachedTransferEnv {F : Type _} (n : Nat) (E : Nat → F) (o q : Pt) (dst src x : Nat) : F :=
  if x=o.x then E q.x else if x=o.y then E q.y else if x=o.z then E q.z
  else if x=dst then E src else if x=dst+8*n then E (src+8*n) else E x

theorem Inv.transferCachedFields {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl)
    {o q : Pt} {dst src : Nat} (hy : o.y=o.x+8*M.n) (hz : o.z=o.x+16*M.n)
    {V : List Nat} {E : Nat → Fin m} {s t : State}
    (hI : Inv M base size m Sl V E s)
    (hD : ∀ x∈cachedSlots M.n o dst,Sl x) (hQ : ∀ x∈cachedSlots M.n q src,x∈V)
    (vx : wordsVal t.mem base o.x M.n=wordsVal s.mem base q.x M.n)
    (vy : wordsVal t.mem base o.y M.n=wordsVal s.mem base q.y M.n)
    (vz : wordsVal t.mem base o.z M.n=wordsVal s.mem base q.z M.n)
    (v2 : wordsVal t.mem base dst M.n=wordsVal s.mem base src M.n)
    (v3 : wordsVal t.mem base (dst+8*M.n) M.n=wordsVal s.mem base (src+8*M.n) M.n)
    (hk : KeepRegs [.rax,.rcx,.rdx] s t)
    (ho : ∀ x,(ofs base x<o.x ∨ o.x+24*M.n≤ofs base x) →
      (ofs base x<dst ∨ dst+16*M.n≤ofs base x) → t.mem x=s.mem x)
    : ProgKeep M base (cachedSlots M.n o dst) s t ∧
    Inv M base size m Sl (cachedSlots M.n o dst++V) (cachedTransferEnv M.n E o q dst src) t := by
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
  have hlt : ∀ x∈cachedSlots M.n o dst,wordsVal t.mem base x M.n<m := by
    intro x hx
    simp only [cachedSlots,jacCoords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with (rfl|rfl|rfl)|(rfl|rfl)
    · rw [vx]; exact hI.lt _ (hQ _ (by simp [cachedSlots,jacCoords]))
    · rw [vy]; exact hI.lt _ (hQ _ (by simp [cachedSlots,jacCoords]))
    · rw [vz]; exact hI.lt _ (hQ _ (by simp [cachedSlots,jacCoords]))
    · rw [v2]; exact hI.lt _ (hQ _ (by simp [cachedSlots]))
    · rw [v3]; exact hI.lt _ (hQ _ (by simp [cachedSlots]))
  have hi := hI.of_progKeep hL kp hD hlt
  refine ⟨kp,{hi with val := ?_}⟩
  intro x hx
  simp only [cachedTransferEnv]
  split
  · subst x
    rw [vx,hI.val _ (hQ _ (by simp [cachedSlots,jacCoords]))]
  · split
    · subst x
      rw [vy,hI.val _ (hQ _ (by simp [cachedSlots,jacCoords]))]
    · split
      · subst x
        rw [vz,hI.val _ (hQ _ (by simp [cachedSlots,jacCoords]))]
      · split
        · subst x
          rw [v2,hI.val _ (hQ _ (by simp [cachedSlots]))]
        · split
          · subst x
            rw [v3,hI.val _ (hQ _ (by simp [cachedSlots]))]
          · have hnot : x∉cachedSlots M.n o dst := by
              simp_all only [cachedSlots,jacCoords,List.mem_append,List.mem_cons,
                List.not_mem_nil,or_false,not_false_eq_true,false_or]
            have hv : x∈V := (List.mem_append.mp hx).resolve_left hnot
            rw [kp.slot hL hI.scr hD (hI.sl x hv) hnot,hI.val x hv]

theorem nafCachedFields_ok {K : WinCfg} {base : Addr} {size tbl dst a m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hn : K.M.n=4 ∨ K.M.n=6)
    (hy : K.E.y=K.E.x+8*K.M.n) (hz : K.E.z=K.E.x+16*K.M.n)
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv K.M base size m Sl V E s)
    (h8 : s.gpr .r8=BitVec.ofNat 64 a) (ha : 1≤a) (ha' : a≤15) (hodd : a%2=1)
    (hp : K.tbl<2^31) (hc : tbl<2^31)
    (hP : K.tbl+192*K.M.n≤size) (hC : tbl+128*K.M.n≤size)
    (hD : ∀ x∈cachedSlots K.M.n K.E dst,Sl x)
    (hQ : ∀ x∈cachedSlots K.M.n (K.tblPt ((a-1)/2+1)) (tbl+16*K.M.n*((a-1)/2)),x∈V)
    (hEP : K.E.x+24*K.M.n≤K.tbl ∨ K.tbl+192*K.M.n≤K.E.x)
    (hEC : K.E.x+24*K.M.n≤tbl ∨ tbl+128*K.M.n≤K.E.x)
    (hDC : dst+16*K.M.n≤tbl ∨ tbl+128*K.M.n≤dst)
    (hDE : dst+16*K.M.n≤K.E.x ∨ K.E.x+24*K.M.n≤dst)
    : WP isa (.block (Naf.cachedEntry K tbl dst)) s fun t =>
      ProgKeep K.M base (cachedSlots K.M.n K.E dst) s t ∧
      Inv K.M base size m Sl (cachedSlots K.M.n K.E dst++V)
        (cachedTransferEnv K.M.n E K.E (K.tblPt ((a-1)/2+1)) dst (tbl+16*K.M.n*((a-1)/2))) t := by
  have hez := hL.le K.E.z (hD _ (by simp [cachedSlots,jacCoords]))
  have hd3 := hL.le (dst+8*K.M.n) (hD _ (by simp [cachedSlots]))
  rw [hz] at hez
  refine WP.mono (nafCachedEntry_ok hI.scr h8 ha ha' hodd hn hp hc hP hC
    (by omega) (by omega) hEP hEC hDC hDE) fun t ⟨vp,vc,hk,ho⟩ =>
      hI.transferCachedFields hL hy hz hD hQ ?_ ?_ ?_ ?_ ?_ hk ho
  · simpa only [WinCfg.tblPt,Nat.add_sub_cancel,Nat.mul_zero,Nat.add_zero] using vp 0 (by decide)
  · simpa only [hy,WinCfg.tblPt,Nat.add_sub_cancel,Nat.mul_one] using vp 1 (by decide)
  · simpa only [hz,WinCfg.tblPt,Nat.add_sub_cancel,show 8*K.M.n*2=16*K.M.n by omega]
      using vp 2 (by decide)
  · simpa only [Nat.mul_zero,Nat.add_zero] using vc 0 (by decide)
  · simpa only [Nat.mul_one] using vc 1 (by decide)

end VG.Proof.Weierstrass.X86_64
