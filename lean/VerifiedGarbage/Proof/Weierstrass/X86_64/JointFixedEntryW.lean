module

import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedEntry
public import VerifiedGarbage.Proof.Weierstrass.FastNaf
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacZero
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState
import VerifiedGarbage.Proof.Weierstrass.JacAdd
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedFields

/-! The signed lookup of a width-nine generator digit, stored in sixteen bits (`fixedEntryW`). -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps)

/-- The magnitude of a digit of `±1 … ±255` in sixteen bits. -/
def nafMagnitudeW (d : BitVec 16) : Nat := if d.toNat<256 then d.toNat else 65536-d.toNat

def fixedEntryEnvW (K : WinCfg) (m : Nat) [NeZero m] (E : Nat → Fin m) (d : BitVec 16) (x y : Nat) :
    Nat → Fin m :=
  let e := fixedLoadEnv K m E x y
  if d.toNat<256 then e else Function.update e K.E.y (-e K.E.y)

theorem nafSignW_ok (s : State) {d : BitVec 16} (hb : s.gpr .r8=d.setWidth 64) :
    WP isa (.block [.alu .cmp .r8 (.imm 256)]) s fun t =>
      t.cf=some (decide (d.toNat<256)) ∧ Keeps [] s t := by
  have hd : (d.setWidth 64).toNat=d.toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := d.isLt; omega)
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.bind_some,RegUpd.cf_arithFlags,hb,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun _ _ => rfl,rfl,rfl,rfl⟩
  congr 1

theorem nafAbsW_ok (s : State) {d : BitVec 16} (hb : s.gpr .r8=d.setWidth 64) :
    WP isa (.block [.mov32 .rax (.imm 65536),.alu .sub .rax (.reg .r8),.mov .r8 (.reg .rax)]) s
      fun t => t.gpr .r8=BitVec.ofNat 64 (65536-d.toNat) ∧ Keeps [.rax,.r8] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,readSrc32,State.setReg32,
    Option.map_some,Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,hb,
    ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · apply BitVec.eq_of_toNat_eq
    have hl := d.isLt
    have h6 : (65536 : BitVec 32).toNat=65536 := rfl
    simp only [BitVec.toNat_sub,BitVec.toNat_setWidth,BitVec.toNat_ofNat,h6]
    omega
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,hr.1,hr.2,ite_false]

private theorem prefix_keepW {M : Mod} {base : Addr} {W : List Nat} {s t : State}
    {rs : List Reg} (hk : Keeps rs s t) (hr : ∀ r∈rs,r∈clob M.n) :
    ProgKeep M base W s t :=
  ⟨fun r h => hk.1 r (fun h' => h (hr r h')),hk.2.2.1,hk.2.2.2,
    fun x _ _ => congrFun hk.2.1 x⟩

theorem jointFixedEntryW_fields_ok {K : WinCfg} {s : State} {base T : Addr} {size x y m : Nat}
    [NeZero m] {tsym : String} {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fin m}
    (hL : Lay K.M size Sl) (hn : K.M.n=4 ∨ K.M.n=6 ∨ K.M.n=9) (hm : UnitMod m (2^(64*K.M.n)))
    (hi : Inv K.M base size m Sl V E s) {d : BitVec 16}
    (ha : 1≤nafMagnitudeW d) (h8 : s.gpr .r8=d.setWidth 64)
    (hS : FixedSource K.M.n base T tsym size (nafMagnitudeW d) x y s)
    (hy : K.E.y=K.E.x+8*K.M.n) (hz : K.E.z=K.E.x+16*K.M.n)
    (hD : ∀ v∈jacCoords K.E,Sl v) (hx : x<m) (hyy : y<m) (hOne : K.one<m)
    (hZero : K.zero∈V) (heZero : E K.zero=0) (hApart : K.zero∉jacCoords K.E) :
    WP isa (Joint.fixedEntryW K tsym) s fun t =>
      ProgKeep K.M base (jacCoords K.E) s t ∧
      Inv K.M base size m Sl (jacCoords K.E++V) (fixedEntryEnvW K m E d x y) t := by
  have hl := d.isLt
  have ha' : nafMagnitudeW d≤2^31 := by
    unfold nafMagnitudeW
    split <;> omega
  rw [Joint.fixedEntryW]
  apply WP.seq
  refine WP.mono_syms (nafSignW_ok s h8) fun u ⟨hu,ku⟩ su => ?_
  have iu := hi.of_keeps ku (by decide)
  have pu : ProgKeep K.M base (jacCoords K.E) s u := prefix_keepW ku (by simp)
  have us := hS.of_keeps ku su
  have hu8 : u.gpr .r8=d.setWidth 64 := (ku.1 .r8 (by simp)).trans h8
  refine WP.ite (decide (d.toNat<256)) hu (fun hb => ?_) (fun hb => ?_)
  · have hp := of_decide_eq_true hb
    have hmag : u.gpr .r8=BitVec.ofNat 64 (nafMagnitudeW d) := by
      rw [hu8,nafMagnitudeW,ite_eq_left hp]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    refine WP.mono (jointFixedFields_ok hL hn iu ha ha' hmag us hy hz hD hx hyy hOne)
      fun t ⟨kt,it⟩ => ⟨pu.trans kt,?_⟩
    simpa only [fixedEntryEnvW,ite_eq_left hp] using it
  · have hp := of_decide_eq_false hb
    rw [List.append_assoc,WP.block_append_iff]
    refine WP.mono_syms (nafAbsW_ok u hu8) fun v ⟨hv,kv⟩ sv => ?_
    have iv := iu.of_keeps kv (by decide)
    have pv : ProgKeep K.M base (jacCoords K.E) u v := prefix_keepW kv (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl <;> simp [clob,acc])
    rw [WP.block_append_iff]
    refine WP.mono (jointFixedFields_ok hL hn iv ha ha'
      (by rw [nafMagnitudeW,ite_eq_right hp]; exact hv) (us.of_keeps kv sv) hy hz hD hx hyy hOne)
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
    simpa only [fixedEntryEnvW,ite_eq_right hp,FOp.run,hz0,
      show (0 : Fin m)-fixedLoadEnv K m E x y K.E.y = -fixedLoadEnv K m E x y K.E.y from by grind] using ie

theorem fixedEntryEnvW_point {K : WinCfg} {C : Curve} {E : Nat → Fe C} {x y : Nat} {d : BitVec 16}
    (hn : 0<K.M.n) (hy : K.E.y=K.E.x+8*K.M.n) (hz : K.E.z=K.E.x+16*K.M.n)
    (hOne : toM C.p (2^(64*K.M.n)) K.one=1) {P : Point C}
    (hp : InvJ C (toM C.p (2^(64*K.M.n)) x) (toM C.p (2^(64*K.M.n)) y) 1 P) :
    InvJ C (fixedEntryEnvW K C.p E d x y K.E.x) (fixedEntryEnvW K C.p E d x y K.E.y)
      (fixedEntryEnvW K C.p E d x y K.E.z) (if d.toNat<256 then P else negPt P) ∧
      fixedEntryEnvW K C.p E d x y K.E.z=1 := by
  have h := fixedLoadEnv_point (E:=E) hn hy hz hOne hp
  have hxy : K.E.x≠K.E.y := by omega
  have hzy : K.E.z≠K.E.y := by omega
  unfold fixedEntryEnvW
  split
  · exact h
  · simp only [Function.update_self,Function.update_of_ne hxy,Function.update_of_ne hzy]
    exact ⟨h.1.negY,h.2⟩

theorem word_magnitudeW (u j : Nat) : nafMagnitudeW (FastNaf.word u j)=FastNaf.magnitude 9 u j := by
  have h : FastNaf.magnitude 9 u j=FastNaf9.magnitude u j := by
    simp only [FastNaf.magnitude,FastNaf.ne_9_7,ite_true,ite_false]
  rw [h,← FastNaf9.word_magnitude u j]
  rfl

theorem word_negativeW (u j : Nat) :
    decide (256≤(FastNaf.word u j).toNat)=FastNaf.negative 9 u j := by
  have h : FastNaf.negative 9 u j=FastNaf9.negative u j := by
    simp only [FastNaf.negative,FastNaf.ne_9_7,ite_true,ite_false]
  rw [h,← FastNaf9.word_negative u j]
  rfl

/-- `jointFixedFast_ok` for width nine. -/
theorem jointFixedFastW_ok {K : WinCfg} {s : State} {base T : Addr} {size x y u j : Nat}
    {C : Curve} {G : Point C} {tsym : String} {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fe C}
    (hL : Lay K.M size Sl) (hn : K.M.n=4 ∨ K.M.n=6 ∨ K.M.n=9) (hm : UnitMod C.p (2^(64*K.M.n)))
    (hi : Inv K.M base size C.p Sl V E s) (hmag : FastNaf.magnitude 9 u j≠0)
    (h8 : s.gpr .r8=(FastNaf.word u j).setWidth 64)
    (hS : FixedSource K.M.n base T tsym size (FastNaf.magnitude 9 u j) x y s)
    (hy : K.E.y=K.E.x+8*K.M.n) (hz : K.E.z=K.E.x+16*K.M.n)
    (hD : ∀ v∈jacCoords K.E,Sl v) (hx : x<C.p) (hyy : y<C.p) (hOne : K.one<C.p)
    (hOneVal : toM C.p (2^(64*K.M.n)) K.one=1)
    (hZero : K.zero∈V) (heZero : E K.zero=0) (hApart : K.zero∉jacCoords K.E)
    (hPoint : InvJ C (toM C.p (2^(64*K.M.n)) x) (toM C.p (2^(64*K.M.n)) y) 1 (mul (FastNaf.magnitude 9 u j) G)) :
    WP isa (Joint.fixedEntryW K tsym) s fun t =>
      ProgKeep K.M base (jacCoords K.E) s t ∧
      Inv K.M base size C.p Sl (jacCoords K.E++V) (fixedEntryEnvW K C.p E (FastNaf.word u j) x y) t ∧
      InvJ C (fixedEntryEnvW K C.p E (FastNaf.word u j) x y K.E.x)
        (fixedEntryEnvW K C.p E (FastNaf.word u j) x y K.E.y)
        (fixedEntryEnvW K C.p E (FastNaf.word u j) x y K.E.z) (FastNaf.point C G 9 u j) ∧
      fixedEntryEnvW K C.p E (FastNaf.word u j) x y K.E.z=1 := by
  have he := word_magnitudeW u j
  refine WP.mono (jointFixedEntryW_fields_ok hL hn hm hi (by rw [he]; omega) h8
    (by rw [he]; exact hS) hy hz hD hx hyy hOne hZero heZero hApart) fun t ⟨kt,it⟩ => ?_
  have hp := fixedEntryEnvW_point (E:=E) (d:=FastNaf.word u j) (by omega) hy hz hOneVal hPoint
  have ep : (if (FastNaf.word u j).toNat<256 then mul (FastNaf.magnitude 9 u j) G
      else negPt (mul (FastNaf.magnitude 9 u j) G))=FastNaf.point C G 9 u j := by
    rw [FastNaf.point,←word_negativeW u j]
    by_cases h : (FastNaf.word u j).toNat<256
    · simp only [h,ite_true,show ¬256≤(FastNaf.word u j).toNat from by omega,decide_false,ite_false,Bool.false_eq_true]
    · simp only [h,ite_false,show 256≤(FastNaf.word u j).toNat from by omega,decide_true,ite_true]
  rw [ep] at hp
  exact ⟨kt,it,hp⟩

end VG.Proof.Weierstrass.X86_64
