import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedFields
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafDigitRead
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacZero
import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-! Signed generator lookup keeps an exact field environment and affine Z. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps)

def fixedEntryEnv (K : WinCfg) (m : Nat) [NeZero m] (E : Nat → Fin m) (b : BitVec 8) (x y : Nat) : Nat → Fin m :=
  let e := fixedLoadEnv K m E x y
  if b.toNat<128 then e else Function.update e K.E.y (-e K.E.y)

private theorem prefix_keep {M : Mod} {base : Addr} {W : List Nat} {s t : State}
    {rs : List Reg} (hk : Keeps rs s t) (hr : ∀ r∈rs,r∈clob M.n) :
    ProgKeep M base W s t :=
  ⟨fun r h => hk.1 r (fun h' => h (hr r h')),hk.2.2.1,hk.2.2.2,
    fun x _ _ => congrFun hk.2.1 x⟩

theorem jointFixedEntry_fields_ok {K : WinCfg} {s : State} {base T : Addr} {size x y m : Nat}
    [NeZero m] {tsym : String} {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fin m}
    (hL : Lay K.M size Sl) (hn : K.M.n=4 ∨ K.M.n=6) (hm : UnitMod m (2^(64*K.M.n)))
    (hi : Inv K.M base size m Sl V E s) {b : BitVec 8}
    (ha : 1≤nafMagnitude b) (h8 : s.gpr .r8=b.setWidth 64)
    (hS : FixedSource K.M.n base T tsym size (nafMagnitude b) x y s)
    (hy : K.E.y=K.E.x+8*K.M.n) (hz : K.E.z=K.E.x+16*K.M.n)
    (hD : ∀ v∈jacCoords K.E,Sl v) (hx : x<m) (hyy : y<m) (hOne : K.one<m)
    (hZero : K.zero∈V) (heZero : E K.zero=0) (hApart : K.zero∉jacCoords K.E) :
    WP isa (Joint.fixedEntry K tsym) s fun t =>
      ProgKeep K.M base (jacCoords K.E) s t ∧
      Inv K.M base size m Sl (jacCoords K.E++V) (fixedEntryEnv K m E b x y) t := by
  have ha' : nafMagnitude b≤2^31 := by
    have := b.isLt
    unfold nafMagnitude
    split <;> omega
  rw [Joint.fixedEntry]
  apply WP.seq
  refine WP.mono_syms (nafSign_ok s h8) fun u ⟨hu,ku⟩ su => ?_
  have iu := hi.of_keeps ku (by decide)
  have pu : ProgKeep K.M base (jacCoords K.E) s u := prefix_keep ku (by simp)
  have us := hS.of_keeps ku su
  have hu8 : u.gpr .r8=b.setWidth 64 := (ku.1 .r8 (by simp)).trans h8
  refine WP.ite (decide (b.toNat<128)) hu (fun hb => ?_) (fun hb => ?_)
  · have hp := of_decide_eq_true hb
    have hmag : u.gpr .r8=BitVec.ofNat 64 (nafMagnitude b) := by
      rw [hu8,nafMagnitude,ite_eq_left hp]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    refine WP.mono (jointFixedFields_ok hL hn iu ha ha' hmag us hy hz hD hx hyy hOne)
      fun t ⟨kt,it⟩ => ⟨pu.trans kt,?_⟩
    simpa only [fixedEntryEnv,ite_eq_left hp] using it
  · have hp := of_decide_eq_false hb
    rw [List.append_assoc,WP.block_append_iff]
    refine WP.mono_syms (nafAbs_ok u hu8) fun v ⟨hv,kv⟩ sv => ?_
    have iv := iu.of_keeps kv (by decide)
    have pv : ProgKeep K.M base (jacCoords K.E) u v := prefix_keep kv (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl <;> simp [clob,acc])
    rw [WP.block_append_iff]
    refine WP.mono (jointFixedFields_ok hL hn iv ha ha'
      (by rw [nafMagnitude,ite_eq_right hp]; exact hv) (us.of_keeps kv sv) hy hz hD hx hyy hOne)
      fun w ⟨kw,iw⟩ => ?_
    have hz0 : fixedLoadEnv K m E x y K.zero=0 := by
      simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false,not_or] at hApart
      simp only [fixedLoadEnv,hApart.1,hApart.2.1,hApart.2.2,ite_false,heZero]
    have sy : K.E.y∈jacCoords K.E++V := by simp [jacCoords]
    have sz : K.zero∈jacCoords K.E++V := List.mem_append_right _ hZero
    have hs : ∀ v∈(FOp.sub K.E.y K.zero K.E.y).out::(FOp.sub K.E.y K.zero K.E.y).ins,Sl v := by
      intro v hv
      simp only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl|rfl|rfl
      · exact iw.sl _ sy
      · exact iw.sl _ sz
      · exact iw.sl _ sy
    have hr : ∀ v∈(FOp.sub K.E.y K.zero K.E.y).ins,v∈jacCoords K.E++V := by
      intro v hv
      simp only [FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl|rfl
      · exact sz
      · exact sy
    refine WP.mono (fop_ok hL hm iw hs hr) fun t ⟨kt,it⟩ => ?_
    refine ⟨(pu.trans pv).trans (kw.trans (progKeep_of_op kt (by simp [jacCoords,FOp.out]))),?_⟩
    have ie := it.sub (fun v hv => List.mem_cons_of_mem _ hv)
    simpa only [fixedEntryEnv,ite_eq_right hp,FOp.run,hz0,
      show (0 : Fin m)-fixedLoadEnv K m E x y K.E.y = -fixedLoadEnv K m E x y K.E.y from by grind] using ie

theorem fixedEntryEnv_point {K : WinCfg} {C : Curve} {E : Nat → Fe C} {x y : Nat} {b : BitVec 8}
    (hn : 0<K.M.n) (hy : K.E.y=K.E.x+8*K.M.n) (hz : K.E.z=K.E.x+16*K.M.n)
    (hOne : toM C.p (2^(64*K.M.n)) K.one=1) {P : Point C}
    (hp : InvJ C (toM C.p (2^(64*K.M.n)) x) (toM C.p (2^(64*K.M.n)) y) 1 P) :
    InvJ C (fixedEntryEnv K C.p E b x y K.E.x) (fixedEntryEnv K C.p E b x y K.E.y)
      (fixedEntryEnv K C.p E b x y K.E.z) (if b.toNat<128 then P else negPt P) ∧
      fixedEntryEnv K C.p E b x y K.E.z=1 := by
  have h := fixedLoadEnv_point (E:=E) hn hy hz hOne hp
  have hxy : K.E.x≠K.E.y := by omega
  have hzy : K.E.z≠K.E.y := by omega
  unfold fixedEntryEnv
  split
  · exact h
  · simp only [Function.update_self,Function.update_of_ne hxy,Function.update_of_ne hzy]
    exact ⟨h.1.negY,h.2⟩

end VG.Proof.Weierstrass.X86_64
