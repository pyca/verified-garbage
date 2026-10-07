import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCacheFields
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafDigitRead
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacZero

/-! Signed peer lookup keeps exact point coordinates and cached powers. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps)

def cachedEntryEnv (K : WinCfg) {m : Nat} [NeZero m] (E : Nat → Fin m)
    (tbl dst : Nat) (b : BitVec 8) : Nat → Fin m :=
  let e := cachedTransferEnv K.M.n E K.E (K.tblPt ((nafMagnitude b-1)/2+1))
    dst (tbl+16*K.M.n*((nafMagnitude b-1)/2))
  if b.toNat<128 then e else Function.update e K.E.y (-e K.E.y)

private theorem prefix_keep {M : Mod} {base : Addr} {W : List Nat} {s t : State}
    {rs : List Reg} (hk : Keeps rs s t) (hr : ∀ r∈rs,r∈clob M.n) :
    ProgKeep M base W s t :=
  ⟨fun r h => hk.1 r (fun h' => h (hr r h')),hk.2.2.1,hk.2.2.2,
    fun x _ _ => congrFun hk.2.1 x⟩

theorem nafSignedCachedFields_ok {K : WinCfg} {s : State} {base : Addr} {size tbl dst m : Nat}
    [NeZero m] {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fin m}
    (hL : Lay K.M size Sl) (hn : K.M.n=4 ∨ K.M.n=6 ∨ K.M.n=9) (hm : UnitMod m (2^(64*K.M.n)))
    (hi : Inv K.M base size m Sl V E s) {b : BitVec 8}
    (ha : 1≤nafMagnitude b) (ha' : nafMagnitude b≤15) (hodd : nafMagnitude b%2=1)
    (h8 : s.gpr .r8=b.setWidth 64)
    (hy : K.E.y=K.E.x+8*K.M.n) (hz : K.E.z=K.E.x+16*K.M.n)
    (hp : K.tbl<2^31) (hc : tbl<2^31)
    (hP : K.tbl+192*K.M.n≤size) (hC : tbl+128*K.M.n≤size)
    (hD : ∀ x∈cachedSlots K.M.n K.E dst,Sl x)
    (hQ : ∀ x∈cachedSlots K.M.n (K.tblPt ((nafMagnitude b-1)/2+1))
      (tbl+16*K.M.n*((nafMagnitude b-1)/2)),x∈V)
    (hEP : K.E.x+24*K.M.n≤K.tbl ∨ K.tbl+192*K.M.n≤K.E.x)
    (hEC : K.E.x+24*K.M.n≤tbl ∨ tbl+128*K.M.n≤K.E.x)
    (hDC : dst+16*K.M.n≤tbl ∨ tbl+128*K.M.n≤dst)
    (hDE : dst+16*K.M.n≤K.E.x ∨ K.E.x+24*K.M.n≤dst)
    (hZero : K.zero∈V) (heZero : E K.zero=0) (hApart : K.zero∉cachedSlots K.M.n K.E dst) :
    WP isa (Naf.signedCachedEntry K tbl dst) s fun t =>
      ProgKeep K.M base (cachedSlots K.M.n K.E dst) s t ∧
      Inv K.M base size m Sl (cachedSlots K.M.n K.E dst++V) (cachedEntryEnv K E tbl dst b) t := by
  rw [Naf.signedCachedEntry]
  apply WP.seq
  refine WP.mono (nafSign_ok s h8) fun u ⟨hu,ku⟩ => ?_
  have iu := hi.of_keeps ku (by decide)
  have pu : ProgKeep K.M base (cachedSlots K.M.n K.E dst) s u := prefix_keep ku (by simp)
  have hu8 : u.gpr .r8=b.setWidth 64 := (ku.1 .r8 (by simp)).trans h8
  refine WP.ite (decide (b.toNat<128)) hu (fun hb => ?_) (fun hb => ?_)
  · have hpos := of_decide_eq_true hb
    have hmag : u.gpr .r8=BitVec.ofNat 64 (nafMagnitude b) := by
      rw [hu8,nafMagnitude,ite_eq_left hpos]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    refine WP.mono (nafCachedFields_ok hL hn hy hz iu hmag ha ha' hodd hp hc hP hC hD hQ hEP hEC hDC hDE)
      fun t ⟨kt,it⟩ => ⟨pu.trans kt,?_⟩
    simpa only [cachedEntryEnv,ite_eq_left hpos] using it
  · have hneg := of_decide_eq_false hb
    rw [List.append_assoc,WP.block_append_iff]
    refine WP.mono (nafAbs_ok u hu8) fun v ⟨hv,kv⟩ => ?_
    have iv := iu.of_keeps kv (by decide)
    have pv : ProgKeep K.M base (cachedSlots K.M.n K.E dst) u v := prefix_keep kv (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl <;> simp [clob,acc])
    rw [WP.block_append_iff]
    refine WP.mono (nafCachedFields_ok hL hn hy hz iv
      (by rw [nafMagnitude,ite_eq_right hneg]; exact hv) ha ha' hodd hp hc hP hC hD hQ hEP hEC hDC hDE)
      fun w ⟨kw,iw⟩ => ?_
    have hz0 : cachedTransferEnv K.M.n E K.E (K.tblPt ((nafMagnitude b-1)/2+1)) dst (tbl+16*K.M.n*((nafMagnitude b-1)/2)) K.zero=0 := by
      simp only [cachedSlots,jacCoords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] at hApart
      simp only [cachedTransferEnv,hApart.1.1,hApart.1.2.1,hApart.1.2.2,
        hApart.2.1,hApart.2.2,ite_false,heZero]
    have sy : K.E.y∈cachedSlots K.M.n K.E dst++V := by simp [cachedSlots,jacCoords]
    have sz : K.zero∈cachedSlots K.M.n K.E dst++V := List.mem_append_right _ hZero
    have hs : ∀ v∈(FOp.sub K.E.y K.zero K.E.y).out::(FOp.sub K.E.y K.zero K.E.y).ins,Sl v := by
      intro v hv
      simp only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl|rfl|rfl
      · exact iw.sl _ sy
      · exact iw.sl _ sz
      · exact iw.sl _ sy
    have hr : ∀ v∈(FOp.sub K.E.y K.zero K.E.y).ins,v∈cachedSlots K.M.n K.E dst++V := by
      intro v hv
      simp only [FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl|rfl
      · exact sz
      · exact sy
    refine WP.mono (fop_ok hL hm iw hs hr) fun t ⟨kt,it⟩ => ?_
    refine ⟨(pu.trans pv).trans (kw.trans (progKeep_of_op kt (by simp [cachedSlots,jacCoords,FOp.out]))),?_⟩
    have ie := it.sub (fun v hv => List.mem_cons_of_mem _ hv)
    simpa only [cachedEntryEnv,ite_eq_right hneg,FOp.run,hz0,
      show (0 : Fin m)-cachedTransferEnv K.M.n E K.E (K.tblPt ((nafMagnitude b-1)/2+1)) dst (tbl+16*K.M.n*((nafMagnitude b-1)/2)) K.E.y = -cachedTransferEnv K.M.n E K.E (K.tblPt ((nafMagnitude b-1)/2+1)) dst (tbl+16*K.M.n*((nafMagnitude b-1)/2)) K.E.y from by grind] using ie

end VG.Proof.Weierstrass.X86_64
