import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCacheNeg

/-! Sign dispatch for a cached public NAF entry. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps)

private theorem prefix_keep {M : Mod} {base : Addr} {W : List Nat} {s t : State}
    {rs : List Reg} (hk : Keeps rs s t) (hr : ∀ r∈rs,r∈clob M.n) :
    ProgKeep M base W s t :=
  ⟨fun r h => hk.1 r (fun h' => h (hr r h')),hk.2.2.1,hk.2.2.2,
    fun x _ _ => congrFun hk.2.1 x⟩

/-- The magnitude lookup is used in both branches; only Y changes for a negative digit. -/
theorem nafSignedCachedEntry_of_lookup {K : WinCfg} {base : Addr} {size tbl dst : Nat}
    {C : Curve} {Sl : Nat → Prop} (hn : 0<K.M.n) (hL : Lay K.M size Sl)
    (hm : UnitMod C.p (2^(64*K.M.n)))
    (hy : K.E.y=K.E.x+8*K.M.n) (hz : K.E.z=K.E.x+16*K.M.n)
    (hDE : dst+16*K.M.n≤K.E.x ∨ K.E.x+24*K.M.n≤dst)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s)
    (hZero : K.zero∈V) (heZero : E K.zero=0) (hZeroApart : K.zero∉cachedSlots K.M.n K.E dst)
    {b : BitVec 8} (h8 : s.gpr .r8=b.setWidth 64) {P : Point C}
    (hLookup : ∀ u,Inv K.M base size C.p Sl V E u →
      u.gpr .r8=BitVec.ofNat 64 (nafMagnitude b) →
      WP isa (.block (Naf.cachedEntry K tbl dst)) u
        (CachedPost K.M base size C Sl V K.E dst P u)) :
    WP isa (Naf.signedCachedEntry K tbl dst) s
      (CachedPost K.M base size C Sl V K.E dst (if b.toNat<128 then P else negPt P) s) := by
  rw [Naf.signedCachedEntry]
  apply WP.seq
  refine WP.mono (nafSign_ok s h8) fun u ⟨hu,ku⟩ => ?_
  have iu := hI.of_keeps ku (by decide)
  have pu : ProgKeep K.M base (cachedSlots K.M.n K.E dst) s u := prefix_keep ku (by simp)
  have hu8 : u.gpr .r8=b.setWidth 64 := (ku.1 .r8 (by simp)).trans h8
  refine WP.ite (decide (b.toNat<128)) hu (fun hb => ?_) (fun hb => ?_)
  · have hp := of_decide_eq_true hb
    rw [ite_eq_left hp]
    apply WP.mono (hLookup u iu ?_)
    · intro t ht; exact ht.prefix pu
    · rw [hu8,nafMagnitude,ite_eq_left hp]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
  · have hp := of_decide_eq_false hb
    rw [ite_eq_right hp,List.append_assoc,WP.block_append_iff]
    refine WP.mono (nafAbs_ok u hu8) fun v ⟨hv,kv⟩ => ?_
    have iv := iu.of_keeps kv (by decide)
    have pv : ProgKeep K.M base (cachedSlots K.M.n K.E dst) u v := prefix_keep kv (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl <;> simp [clob,acc])
    rw [WP.block_append_iff]
    refine WP.mono (hLookup v iv (by rw [nafMagnitude,ite_eq_right hp]; exact hv))
      fun w ⟨kw,iw,pw⟩ => ?_
    have hz0 : tmv C K.M.n base w K.zero=0 := by
      unfold tmv
      rw [kw.slot hL iv.scr (fun x hx => iw.sl x (List.mem_append_left _ hx))
        (iv.sl _ hZero) hZeroApart,iv.val _ hZero,heZero]
    refine WP.mono (negCachedPoint_ok hL hm (by omega) (by omega) (by omega) (by omega)
      iw (List.mem_append_right _ hZero) hz0 pw) fun t ht => ?_
    exact (ht.prefix kw).prefix (pu.trans pv)

theorem nafSignedCachedPoint_ok {K : WinCfg} {base : Addr} {size tbl dst : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hn : K.M.n=4 ∨ K.M.n=6)
    (hm : UnitMod C.p (2^(64*K.M.n)))
    (hy : K.E.y=K.E.x+8*K.M.n) (hz : K.E.z=K.E.x+16*K.M.n)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s)
    (hZero : K.zero∈V) (heZero : E K.zero=0) (hZeroApart : K.zero∉cachedSlots K.M.n K.E dst)
    {b : BitVec 8} (h8 : s.gpr .r8=b.setWidth 64)
    (ha : 1≤nafMagnitude b) (ha' : nafMagnitude b≤15) (hodd : nafMagnitude b%2=1)
    (hp : K.tbl<2^31) (hc : tbl<2^31)
    (hP : K.tbl+192*K.M.n≤size) (hC : tbl+128*K.M.n≤size)
    (hD : ∀ x∈cachedSlots K.M.n K.E dst,Sl x)
    (hQ : ∀ x∈cachedSlots K.M.n (K.tblPt ((nafMagnitude b-1)/2+1))
      (tbl+16*K.M.n*((nafMagnitude b-1)/2)),x∈V)
    (hEP : K.E.x+24*K.M.n≤K.tbl ∨ K.tbl+192*K.M.n≤K.E.x)
    (hEC : K.E.x+24*K.M.n≤tbl ∨ tbl+128*K.M.n≤K.E.x)
    (hDC : dst+16*K.M.n≤tbl ∨ tbl+128*K.M.n≤dst)
    (hDE : dst+16*K.M.n≤K.E.x ∨ K.E.x+24*K.M.n≤dst)
    {P : Point C} (hJ : InvJ C (E (K.tblPt ((nafMagnitude b-1)/2+1)).x)
      (E (K.tblPt ((nafMagnitude b-1)/2+1)).y) (E (K.tblPt ((nafMagnitude b-1)/2+1)).z) P)
    (h2 : E (tbl+16*K.M.n*((nafMagnitude b-1)/2))=
      E (K.tblPt ((nafMagnitude b-1)/2+1)).z*E (K.tblPt ((nafMagnitude b-1)/2+1)).z)
    (h3 : E (tbl+16*K.M.n*((nafMagnitude b-1)/2)+8*K.M.n)=
      E (tbl+16*K.M.n*((nafMagnitude b-1)/2))*E (K.tblPt ((nafMagnitude b-1)/2+1)).z) :
    WP isa (Naf.signedCachedEntry K tbl dst) s
      (CachedPost K.M base size C Sl V K.E dst (if b.toNat<128 then P else negPt P) s) := by
  apply nafSignedCachedEntry_of_lookup (by omega) hL hm hy hz hDE hI hZero heZero hZeroApart h8
  intro u iu hu8
  exact nafCachedPoint_ok hL hn hy hz iu hu8 ha ha' hodd hp hc hP hC hD hQ hEP hEC hDC hDE hJ h2 h3

end VG.Proof.Weierstrass.X86_64
