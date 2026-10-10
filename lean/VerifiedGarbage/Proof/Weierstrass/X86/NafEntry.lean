import VerifiedGarbage.Proof.Weierstrass.X86.NafTable
import VerifiedGarbage.Proof.Weierstrass.X86.NafDigitRead

/-! ## `NafInvariant` -/

section

/-! Stable table entries and scalar digits across the public multiplication loop. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
  VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

def nafLive (K : WinCfg) : List Nat := nafTableLive K 8

structure NafStable (K : WinCfg) (C : Curve) (base : Addr)
    (P : Point C) (β : Nat → BitVec 8) (s : State) : Prop where
  zero : wordsVal s.mem base K.zero K.M.n=0
  table : ∀ a,1≤a → a≤8 → InvJ C (tmv C K.M.n base s (K.tblPt a).x)
    (tmv C K.M.n base s (K.tblPt a).y) (tmv C K.M.n base s (K.tblPt a).z) (mul (2*a-1) P)
  bits : ∀ i<257,s.mem (off base (K.bits+i))=β i

theorem nafLive_R (K : WinCfg) : ∀ x∈jacCoords K.R,x∈nafLive K := by
  intro x hx
  simp only [nafLive,nafTableLive,List.mem_append]
  grind

theorem nafOther_slots (K : WinCfg) : ∀ x∈winOther K,x∈nafSlots K :=
  fun _ hx => List.mem_append_left _ (List.mem_append_right _ hx)

theorem nafRo_slots (K : WinCfg) : ∀ x∈winRo K,x∈nafSlots K :=
  fun _ hx => List.mem_append_left _ (List.mem_append_left _ hx)

theorem NafStable.keep {F : Spec.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    {P : Point C} {β : Nat → BitVec 8} {s t : State}
    (hL : NafLay K size) (hAcc : WkOk F K.M C.p size wk (·∈nafSlots K))
    (hBitsWk : K.bits+260≤wk) (hs : Scr s base size)
    (h : NafStable K C base P β s) (hk : ProgKeep K.M base wk (winOther K) s t) :
    NafStable K C base P β t := by
  have hn := hs.nowrap
  refine ⟨?_,fun a ha h8 => ?_,fun i hi => ?_⟩
  · rw [hk.slot hL.lay hAcc hs (nafOther_slots K)
      (nafRo_slots K _ (by simp [winRo])) (hL.ro _ (by simp [winRo])),h.zero]
  · have hv (x : Nat) (hx : x∈jacCoords (K.tblPt a)) :
        tmv C K.M.n base t x=tmv C K.M.n base s x := by
      unfold tmv
      rw [hk.slot hL.lay hAcc hs (nafOther_slots K) (nafTblPt_mem K hL.n ha (by omega) x hx) ?_]
      intro ho
      have sep := hL.tbl x (List.mem_append_right _ ho)
      simp only [jacCoords,WinCfg.tblPt,hL.n,List.mem_cons,List.not_mem_nil,or_false] at hx
      omega
    rw [hv _ (by simp [jacCoords]),hv _ (by simp [jacCoords]),hv _ (by simp [jacCoords])]
    exact h.table a ha h8
  · rw [hk.unch.byte (fun w hw => ?_) (by have := hL.bits; omega),h.bits i hi]
    simp only [progW,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with ⟨x,hx,rfl⟩ | rfl | rfl | rfl
    · have hb := hL.bits_w x (List.mem_append_left _ hx)
      dsimp only; rw [hL.n]; omega
    · have hb := hL.bits_tmp
      dsimp only; rw [hL.n]; omega
    · dsimp only; omega
    · have := hL.bits; have := hL.size_le
      dsimp only [Mont.outW]; omega

structure NafCore (K : WinCfg) (C : Curve) (base : Addr) (size : Nat)
    (P : Point C) (β : Nat → BitVec 8) (e : Nat) (s : State) : Prop where
  field : Inv K.M base size C.p (·∈nafSlots K) (nafLive K) (tmv C K.M.n base s) s
  stable : NafStable K C base P β s
  point : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y)
    (tmv C K.M.n base s K.R.z) (mul e P)

theorem NafCore.next {F : Spec.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    {P : Point C} {β : Nat → BitVec 8} {e e' : Nat} {s t : State}
    (hL : NafLay K size) (hAcc : WkOk F K.M C.p size wk (·∈nafSlots K)) (hBitsWk : K.bits+260≤wk)
    (h : NafCore K C base size P β e s) {E : Nat → Fe C}
    (hk : ProgKeep K.M base wk (winOther K) s t)
    (hi : Inv K.M base size C.p (·∈nafSlots K) (nafLive K) E t)
    (hp : InvJ C (E K.R.x) (E K.R.y) (E K.R.z) (mul e' P)) :
    NafCore K C base size P β e' t :=
  ⟨hi.to_tmv,h.stable.keep hL hAcc hBitsWk h.field.scr hk,hi.point_tmv (nafLive_R K) hp⟩

theorem NafCore.of_keeps {K : WinCfg} {C : Curve} {base : Addr} {size e : Nat}
    {β : Nat → BitVec 8} {P : Point C} {s t : State} {rs : List Reg}
    (h : NafCore K C base size P β e s) (hk : CKeeps rs s t) (h0 : Reg.edi∉rs) (hsp : Reg.esp∉rs := by decide) :
    NafCore K C base size P β e t := by
  have hm : tmv C K.M.n base t=tmv C K.M.n base s := by
    funext x; unfold tmv; rw [hk.2.1]
  refine ⟨?_,?_,?_⟩
  · rw [hm]; exact h.field.of_keeps hk h0 hsp
  · refine ⟨?_,fun a ha h8 => ?_,fun i hi => ?_⟩
    · rw [hk.2.1]; exact h.stable.zero
    · rw [hm]; exact h.stable.table a ha h8
    · rw [hk.2.1]; exact h.stable.bits i hi
  · rw [hm]; exact h.point

end VG.Proof.Weierstrass.X86

end

/-! ## `NafDouble` -/

section

/-! A Jacobian doubling with no intermediate homogeneous conversion. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
  VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem nafDoubleCore_ok {F : Spec.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk e : Nat}
    {β : Nat → BitVec 8} (hL : NafLay K size)
    (hAcc : WkOk F K.M C.p size wk (·∈nafSlots K)) (hBitsWk : K.bits+260≤wk) (hJ : K.J=65)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    {P : Point C} (hP : onCurve C P=true) {s : State} (h : NafCore K C base size P β e s) :
    WP isa (.seq (fprog F (dblJMul K.S K.R K.D)) (.block (copyPt 4 K.R K.D))) s fun t =>
      ProgKeep K.M base wk (winOther K) s t ∧ NafCore K C base size P β (2*e) t := by
  have old := hL.toWinLay hJ
  have sl (p o : Pt) (hp : p=K.R ∨ p=K.D) (ho : o=K.R ∨ o=K.D) :
      ∀ x∈rcbW K.S o++rcbR K.S p p,x∈nafSlots K := by
    intro x hx; apply hL.old_slots x
    rcases hp with rfl | rfl <;> rcases ho with rfl | rfl <;>
      simp only [rcbW,rcbR,winSlots,winRo,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢ <;> grind
  have vr : ∀ x∈rcbR K.S K.R K.R,x∈nafLive K := by
    intro x hx
    simp only [rcbR,nafLive,nafTableLive,jacCoords,winRo,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have vd : ∀ x∈rcbR K.S K.D K.D,x∈jacCoords K.D++nafLive K := by
    intro x hx
    simp only [rcbR,nafLive,nafTableLive,jacCoords,winRo,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have ww (o : Pt) (ho : o=K.R ∨ o=K.D) : ∀ x∈rcbW K.S o,x∈winOther K := by
    intro x hx
    rcases ho with rfl | rfl <;>
      simp only [rcbW,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢ <;> grind
  apply WP.seq
  refine WP.mono (jacDouble_ok hL.lay hAcc hm hC ha (old.rcbApart_D (Or.inl rfl))
    (sl _ _ (Or.inl rfl) (Or.inr rfl)) h.field vr (hC.onCurve_mul hP _) h.point)
    fun t ⟨kt,it,jt⟩ => ?_
  rw [←hL.n]
  refine WP.mono (copyPoint_ok hL.lay hAcc hL.rcbApart_DR
    (sl _ _ (Or.inr rfl) (Or.inl rfl)) it vd) fun u ⟨E',ku,iu,hu⟩ => ?_
  have kp := (kt.mono (ww _ (Or.inr rfl))).trans (ku.mono (ww _ (Or.inl rfl)))
  refine ⟨kp,h.next hL hAcc hBitsWk kp
    (iu.sub (fun _ hx => List.mem_append_right _ (List.mem_append_right _ hx))) ?_⟩
  simp only [Prod.mk.injEq] at hu
  rw [hu.1,hu.2.1,hu.2.2]
  rw [hC.add_mul_mul hP,show e+e=2*e by omega] at jt
  exact jt

end VG.Proof.Weierstrass.X86

end

/-! ## `NafNeg` -/

section

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont Spec.Weierstrass

theorem nafNeg_ok {F : Spec.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAcc : WkOk F K.M C.p size wk Sl)
    (hm : UnitMod C.p (2^(64*K.M.n))) {V : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv K.M base size C.p Sl V E s)
    (hV : ∀ x∈[K.E.x,K.E.y,K.E.z,K.zero],x∈V)
    (hxy : K.E.x≠K.E.y) (hzy : K.E.z≠K.E.y) (hz : E K.zero=0)
    {P : Point C} (hp : InvJ C (E K.E.x) (E K.E.y) (E K.E.z) P) :
    WP isa (opCode F (.sub K.E.y K.zero K.E.y)) s fun t =>
      ProgKeep K.M base wk [K.E.y] s t ∧
      Inv K.M base size C.p Sl V (Function.update E K.E.y (-E K.E.y)) t ∧
      InvJ C ((Function.update E K.E.y (-E K.E.y)) K.E.x)
        ((Function.update E K.E.y (-E K.E.y)) K.E.y)
        ((Function.update E K.E.y (-E K.E.y)) K.E.z) (negPt P) := by
  have hs : ∀ x∈(FOp.sub K.E.y K.zero K.E.y).out::(FOp.sub K.E.y K.zero K.E.y).ins,Sl x := by
    intro x hx; apply hi.sl x; apply hV x
    simp only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have hv : ∀ x∈(FOp.sub K.E.y K.zero K.E.y).ins,x∈V := by
    intro x hx; apply hV x
    simp only [FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  refine WP.mono (fop_ok hL hAcc hm hi hs hv) fun t ⟨kt,it⟩ => ?_
  have he : FOp.run (.sub K.E.y K.zero K.E.y) E=Function.update E K.E.y (-E K.E.y) := by
    simp only [FOp.run,hz]
    apply congrArg (Function.update E K.E.y)
    grind
  rw [he] at it
  refine ⟨kt,it.sub (fun _ hx => List.mem_cons_of_mem _ hx),?_⟩
  simpa only [Function.update_of_ne hxy,Function.update_of_ne hzy,Function.update_self] using hp.negY

end VG.Proof.Weierstrass.X86

end

/-! ## `NafSigned` -/

section

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

end

/-! ## `NafEntry` -/

section

/-! A signed odd-multiple lookup preserves the running accumulator. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
  VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem nafLive_table (K : WinCfg) (hn : K.M.n=4) {a : Nat} (ha : 1≤a) (h8 : a≤8) :
    ∀ x∈jacCoords (K.tblPt a),x∈nafLive K := by
  intro x hx
  apply List.mem_append_right
  simp only [jacCoords,WinCfg.tblPt,hn,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl
  · exact List.mem_map.mpr ⟨3*(a-1),List.mem_range.mpr (by omega),by omega⟩
  · exact List.mem_map.mpr ⟨3*(a-1)+1,List.mem_range.mpr (by omega),by omega⟩
  · exact List.mem_map.mpr ⟨3*(a-1)+2,List.mem_range.mpr (by omega),by omega⟩

theorem NafCore.of_write {F : Spec.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk e : Nat}
    {β : Nat → BitVec 8} {P : Point C} {s t : State} {W : List Nat}
    (hL : NafLay K size) (hAcc : WkOk F K.M C.p size wk (·∈nafSlots K)) (hBitsWk : K.bits+260≤wk)
    (h : NafCore K C base size P β e s) (hk : ProgKeep K.M base wk W s t)
    (hw : ∀ x∈W,x∈winOther K) (hn : ∀ x∈jacCoords K.R,x∉W)
    (hi : Inv K.M base size C.p (·∈nafSlots K) (nafLive K) (tmv C K.M.n base t) t) :
    NafCore K C base size P β e t :=
  ⟨hi,h.stable.keep hL hAcc hBitsWk h.field.scr (hk.mono hw),
    hk.invJ hL.lay hAcc h.field.scr (fun x hx => nafOther_slots K x (hw x hx))
      (fun x hx => h.field.sl x (nafLive_R K x hx)) hn h.point⟩

theorem nafEntry_ok {F : Spec.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk e : Nat}
    {β : Nat → BitVec 8} {b : BitVec 8} (hL : NafLay K size)
    (hAcc : WkOk F K.M C.p size wk (·∈nafSlots K)) (hBitsWk : K.bits+260≤wk)
    (hm : UnitMod C.p (2^(64*K.M.n)))
    (hmag : 1≤nafMagnitude b) (hmag15 : nafMagnitude b≤15) (hodd : nafMagnitude b%2=1)
    {P : Point C} {s : State} (h : NafCore K C base size P β e s)
    (h8 : s.gpr .ebx=b.setWidth 32) :
    WP isa (Naf.signedEntry K F) s fun t =>
      ProgKeep K.M base wk (winOther K) s t ∧ NafCore K C base size P β e t ∧
      Inv K.M base size C.p (·∈nafSlots K) (jacCoords K.E++nafLive K) (tmv C K.M.n base t) t ∧
      InvJ C (tmv C K.M.n base t K.E.x) (tmv C K.M.n base t K.E.y) (tmv C K.M.n base t K.E.z)
        (if nafNegative b then negPt (mul (nafMagnitude b) P) else mul (nafMagnitude b) P) := by
  let a := (nafMagnitude b-1)/2+1
  have ha : 1≤a := by dsimp [a]; omega
  have ha8 : a≤8 := by dsimp [a]; omega
  have he : 2*a-1=nafMagnitude b := by dsimp [a]; omega
  have hw : ∀ x∈jacCoords K.E,x∈winOther K := by
    intro x hx
    simp only [jacCoords,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have hd : ∀ x∈jacCoords K.E,x∈nafSlots K := fun x hx => nafOther_slots K x (hw x hx)
  have hn := hL.nodup
  simp only [winOther,rcbW,List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,
    List.not_mem_nil,or_false,not_or] at hn
  have hr : ∀ x∈jacCoords K.R,x∉jacCoords K.E := by
    intro x hx hy
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx hy
    grind
  have h0 : K.zero∈nafLive K := by
    simp [nafLive,nafTableLive,winRo]
  have hz : tmv C K.M.n base s K.zero=0 := by unfold tmv; rw [h.stable.zero,toM_zero]
  have h0E : K.zero∉jacCoords K.E := fun he => hL.ro _ (by simp [winRo]) (hw _ he)
  have sep : K.E.x+96≤K.tbl ∨ K.tbl+768≤K.E.x := by
    have hx := hL.tbl K.E.x (List.mem_append_right _ (hw _ (by simp [jacCoords])))
    have hz := hL.tbl K.E.z (List.mem_append_right _ (hw _ (by simp [jacCoords])))
    rw [hL.exz] at hz
    omega
  refine WP.mono (nafSignedEntry_of_lookup hL.lay hAcc hm hL.exy hL.exz h.field h0 hz h0E h8
    (P := mul (nafMagnitude b) P) (fun u iu hu => ?_)) fun t ⟨kt,it,jt⟩ => ?_
  · have jp := h.stable.table a ha ha8
    rw [he] at jp
    exact nafPublicPoint_ok hL.lay hAcc hL.n hL.exy hL.exz iu hu hmag hmag15
      (by have := hL.table_le; omega) hd (nafLive_table K hL.n ha ha8) sep jp
  · refine ⟨kt.mono hw,h.of_write hL hAcc hBitsWk kt hw hr
      (it.sub (fun _ hx => List.mem_append_right _ hx)),it,?_⟩
    by_cases hb : b.toNat<128
    · simpa only [nafNegative,show ¬128≤b.toNat from by omega,decide_false,Bool.false_eq_true,ite_true,ite_false,hb] using jt
    · simpa only [nafNegative,show 128≤b.toNat from by omega,decide_true,ite_false,ite_true,hb] using jt

end VG.Proof.Weierstrass.X86

end
