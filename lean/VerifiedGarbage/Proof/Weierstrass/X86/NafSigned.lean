import VerifiedGarbage.Proof.Weierstrass.X86.NafNeg

/-! Public sign dispatch around an odd-multiple lookup. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
  VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

def NafPointPost (M : Mod) (base : Addr) (size wk : Nat) (C : Curve) (Sl : Nat → Prop)
    (V : List Nat) (p : Pt) (P : Point C) (s t : State) : Prop :=
  ProgKeep M base wk (jacCoords p) s t ∧
  Inv M base size C.p Sl (jacCoords p++V) (tmv C M.n base t) t ∧
  InvJ C (tmv C M.n base t p.x) (tmv C M.n base t p.y) (tmv C M.n base t p.z) P

theorem NafPointPost.prefix {M : Mod} {base : Addr} {size wk : Nat} {C : Curve}
    {Sl : Nat → Prop} {V : List Nat} {p : Pt} {P : Point C} {s t u : State}
    (h : NafPointPost M base size wk C Sl V p P t u)
    (hk : ProgKeep M base wk (jacCoords p) s t) :
    NafPointPost M base size wk C Sl V p P s u := ⟨hk.trans h.1,h.2⟩

theorem nafPrefix_keep {M : Mod} {base : Addr} {wk : Nat} {W : List Nat} {s t : State}
    {rs : List Reg} (hk : CKeeps rs s t) (hr : ∀ r∈rs,r∈clob) :
    ProgKeep M base wk W s t :=
  ⟨fun r h => hk.1 r (fun h' => h (hr r h')),hk.2.2.1,hk.2.2.2,
    fun x _ => congrFun hk.2.1 x⟩

theorem nafSignedEntry_of_lookup {F : Spec.Weierstrass.Mont.Modulus} {K : WinCfg} {base : Addr} {size wk : Nat}
    {C : Curve} {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAcc : WkOk F K.M C.p size wk Sl)
    (hm : UnitMod C.p (2^(64*K.M.n)))
    (hy : K.E.y=K.E.x+32) (hz : K.E.z=K.E.x+64)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s)
    (hZero : K.zero∈V) (heZero : E K.zero=0) (hZeroApart : K.zero∉jacCoords K.E)
    {b : BitVec 8} (h8 : s.gpr .ebx=b.setWidth 32) {P : Point C}
    (hLookup : ∀ u,Inv K.M base size C.p Sl V E u →
      u.gpr .ebx=BitVec.ofNat 32 (nafMagnitude b) →
      WP isa (.block (Naf.publicEntry K)) u
        (NafPointPost K.M base size wk C Sl V K.E P u)) :
    WP isa (Naf.signedEntry K F) s
      (NafPointPost K.M base size wk C Sl V K.E (if b.toNat<128 then P else negPt P) s) := by
  rw [Naf.signedEntry]
  apply WP.seq
  refine WP.mono (nafDigitSign_ok s h8) fun u ⟨hu,ku⟩ => ?_
  have iu := hI.of_keeps ku (by decide)
  have pu : ProgKeep K.M base wk (jacCoords K.E) s u := nafPrefix_keep ku (by simp)
  have hu8 : u.gpr .ebx=b.setWidth 32 := (ku.1 .ebx (by simp)).trans h8
  refine WP.ite (decide (b.toNat<128)) hu (fun hb => ?_) (fun hb => ?_)
  · have hp := of_decide_eq_true hb
    rw [ite_eq_left hp]
    apply WP.mono (hLookup u iu ?_)
    · intro t ht; exact ht.prefix pu
    · rw [hu8,nafMagnitude,ite_eq_left hp]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
  · have hp := of_decide_eq_false hb
    rw [ite_eq_right hp]
    apply WP.seq
    rw [WP.block_append_iff]
    refine WP.mono (nafAbs_ok u hu8) fun v ⟨hv,kv⟩ => ?_
    have iv := iu.of_keeps kv (by decide)
    have pv : ProgKeep K.M base wk (jacCoords K.E) u v := nafPrefix_keep kv (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl <;> simp [clob])
    refine WP.mono (hLookup v iv (by rw [nafMagnitude,ite_eq_right hp]; exact hv))
      fun w ⟨kw,iw,pw⟩ => ?_
    have hz0 : tmv C K.M.n base w K.zero=0 := by
      unfold tmv
      rw [kw.slot hL hAcc iv.scr (fun x hx => iw.sl x (List.mem_append_left _ hx))
        (iv.sl _ hZero) hZeroApart,iv.val _ hZero,heZero]
    refine WP.mono (nafNeg_ok hL hAcc hm iw (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl
      · exact List.mem_append_left _ (by simp [jacCoords])
      · exact List.mem_append_left _ (by simp [jacCoords])
      · exact List.mem_append_left _ (by simp [jacCoords])
      · exact List.mem_append_right _ hZero)
      (by omega) (by omega) hz0 pw) fun t ⟨kt,it,jt⟩ => ?_
    have post : NafPointPost K.M base size wk C Sl V K.E (negPt P) w t :=
      ⟨kt.mono (by simp [jacCoords]),it.to_tmv,it.point_tmv
        (fun _ hx => List.mem_append_left _ hx) jt⟩
    exact (post.prefix kw).prefix (pu.trans pv)

end VG.Proof.Weierstrass.X86
