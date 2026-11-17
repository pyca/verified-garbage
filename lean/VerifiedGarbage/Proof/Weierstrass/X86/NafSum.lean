module

import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Weierstrass.X86.JacAdd
public import VerifiedGarbage.Proof.Weierstrass.X86.WinFinish
import VerifiedGarbage.Proof.X25519.X86.Column
import VerifiedGarbage.Proof.Weierstrass.X86.JacState
public import VerifiedGarbage.Impl.Mont.Mod
public import VerifiedGarbage.Impl.Weierstrass.X86.Jacobian
public import VerifiedGarbage.Impl.Weierstrass.X86.TComb
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Weierstrass.Jac
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.WinLay
public import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import VerifiedGarbage.Proof.Weierstrass.X86.Ladder
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.Proof.Weierstrass.X86.NafTable
public import VerifiedGarbage.Impl.Weierstrass.X86.Naf
public import VerifiedGarbage.Proof.Weierstrass.X86.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Weierstrass.X86.NafPoint
import VerifiedGarbage.Proof.Weierstrass.X86.TComb

/-! ### `Weierstrass.X86.NafEntry`, which this module and modules that import it used -/

section

/-! ### `Weierstrass.X86.NafDigitRead`, which only this module used -/

section

/-! Read public signed digits and test their sign and zero case. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont

def nafMagnitude (b : BitVec 8) : Nat := if b.toNat<128 then b.toNat else 256-b.toNat

def nafNegative (b : BitVec 8) : Bool := decide (128≤b.toNat)

private theorem nafRead_zero : ∀ b : BitVec 8, (b.setWidth 32==0)=decide (b=0) := by decide

theorem nafRead_ok {K : WinCfg} {s : State} {base : Addr} {size j : Nat} {b : BitVec 8}
    (hs : Scr s base size) (hj : K.bits+j<size)
    (hc : s.gpr .esi=BitVec.ofNat 32 j) (hm : s.mem (off base (K.bits+j))=b) :
    WP isa (.block (Naf.digitRead K)) s fun t =>
      t.gpr .ebx=b.setWidth 32 ∧ t.zf=some (decide (b=0)) ∧ CKeeps [.ecx,.ebx] s t := by
  unfold Naf.digitRead
  refine wp_movS rfl fun a ua _ => ?_
  refine wp_addS rfl fun c uc _ => ?_
  have kc := ua.keeps.trans uc.keeps
  have sc := hs.of_keeps kc (by decide)
  have ea : c.gpr .ecx=c.gpr .edi+BitVec.ofNat 32 j := by
    rw [uc.gpr,ua.gpr,ua.other _ (by decide),hc,kc.1 .edi (by decide)]
  refine wp_load8 (ea_winByte sc ea hj) (sc.read (by omega_using [hj])) fun d ud => ?_
  refine wp_test fun t ut zt => WP.block_nil ?_
  have vd : d.gpr .ebx=b.setWidth 32 := by rw [ud.gpr,uc.mem,ua.mem,hm]
  refine ⟨(congrFun ut.gpr .ebx).trans vd,?_,?_,?_,?_,?_⟩
  · rw [zt,vd,BitVec.and_self,nafRead_zero]
  · intro r hr
    have hx : r≠.ecx := fun h => hr (h ▸ (by simp))
    have hb : r≠.ebx := fun h => hr (h ▸ (by simp))
    rw [ut.gpr,ud.other _ hb,uc.other _ hx,ua.other _ hx]
  · rw [ut.mem,ud.mem,uc.mem,ua.mem]
  · rw [ut.rd,ud.rd,uc.rd,ua.rd]
  · rw [ut.wr,ud.wr,uc.wr,ua.wr]

theorem nafDigitSign_ok (s : State) {b : BitVec 8} (hb : s.gpr .ebx=b.setWidth 32) :
    WP isa (.block [.alu .cmp .ebx (.imm 128)]) s fun t =>
      t.cf=some (decide (b.toNat<128)) ∧ CKeeps [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.bind_some,RegUpd.cf_arithFlags,hb,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun _ _ => rfl,rfl,rfl,rfl⟩
  simp only [BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (show b.toNat<2^32 from by have:=b.isLt; omega_using [])]
  rfl

theorem nafAbs_ok (s : State) {b : BitVec 8} (hb : s.gpr .ebx=b.setWidth 32) :
    WP isa (.block [.mov .eax (.imm 256),.alu .sub .eax (.reg .ebx),.mov .ebx (.reg .eax)]) s
      fun t => t.gpr .ebx=BitVec.ofNat 32 (256-b.toNat) ∧ CKeeps [.eax,.ebx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.map_some,Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,hb,
    ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · have h : ∀ b : BitVec 8, (256 : BitVec 32)-b.setWidth 32=BitVec.ofNat 32 (256-b.toNat) := by decide
    exact h b
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,hr.1,hr.2,ite_false]

end VG.Proof.Weierstrass.X86

end

end


/-! ## `NafInvariant` -/

@[expose] public section

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

theorem NafStable.keep {F : Impl.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk : Nat}
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
      rw [hk.slot hL.lay hAcc hs (nafOther_slots K) (nafTblPt_mem K hL.n ha (by omega_arith) x hx) ?_]
      intro ho
      have sep := hL.tbl x (List.mem_append_right _ ho)
      simp only [jacCoords,WinCfg.tblPt,hL.n,List.mem_cons,List.not_mem_nil,or_false] at hx
      omega_arith
    rw [hv _ (by simp [jacCoords]),hv _ (by simp [jacCoords]),hv _ (by simp [jacCoords])]
    exact h.table a ha h8
  · rw [hk.unch.byte (fun w hw => ?_) (by have := hL.bits; omega_arith),h.bits i hi]
    simp only [progW,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with ⟨x,hx,rfl⟩ | rfl | rfl | rfl
    · have hb := hL.bits_w x (List.mem_append_left _ hx)
      dsimp only; rw [hL.n]; omega_arith
    · have hb := hL.bits_tmp
      dsimp only; rw [hL.n]; omega_arith
    · dsimp only; omega_arith
    · have := hL.bits; have := hL.size_le
      dsimp only [Mont.outW]; omega_arith

structure NafCore (K : WinCfg) (C : Curve) (base : Addr) (size : Nat)
    (P : Point C) (β : Nat → BitVec 8) (e : Nat) (s : State) : Prop where
  field : Inv K.M base size C.p (·∈nafSlots K) (nafLive K) (tmv C K.M.n base s) s
  stable : NafStable K C base P β s
  point : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y)
    (tmv C K.M.n base s K.R.z) (mul e P)

theorem NafCore.next {F : Impl.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk : Nat}
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

theorem nafDoubleCore_ok {F : Impl.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk e : Nat}
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
  rw [hC.add_mul_mul hP,show e+e=2*e by omega_arith] at jt
  exact jt

end VG.Proof.Weierstrass.X86

end

/-! ## `NafNeg` -/

section

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont Spec.Weierstrass

theorem nafNeg_ok {F : Impl.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk : Nat}
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

theorem nafSignedEntry_of_lookup {F : Impl.Weierstrass.Mont.Modulus} {K : WinCfg} {base : Addr} {size wk : Nat}
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
      (by omega_arith) (by omega_arith) hz0 pw) fun t ⟨kt,it,jt⟩ => ?_
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
  · exact List.mem_map.mpr ⟨3*(a-1),List.mem_range.mpr (by omega_arith),by omega_arith⟩
  · exact List.mem_map.mpr ⟨3*(a-1)+1,List.mem_range.mpr (by omega_arith),by omega_arith⟩
  · exact List.mem_map.mpr ⟨3*(a-1)+2,List.mem_range.mpr (by omega_arith),by omega_arith⟩

theorem NafCore.of_write {F : Impl.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk e : Nat}
    {β : Nat → BitVec 8} {P : Point C} {s t : State} {W : List Nat}
    (hL : NafLay K size) (hAcc : WkOk F K.M C.p size wk (·∈nafSlots K)) (hBitsWk : K.bits+260≤wk)
    (h : NafCore K C base size P β e s) (hk : ProgKeep K.M base wk W s t)
    (hw : ∀ x∈W,x∈winOther K) (hn : ∀ x∈jacCoords K.R,x∉W)
    (hi : Inv K.M base size C.p (·∈nafSlots K) (nafLive K) (tmv C K.M.n base t) t) :
    NafCore K C base size P β e t :=
  ⟨hi,h.stable.keep hL hAcc hBitsWk h.field.scr (hk.mono hw),
    hk.invJ hL.lay hAcc h.field.scr (fun x hx => nafOther_slots K x (hw x hx))
      (fun x hx => h.field.sl x (nafLive_R K x hx)) hn h.point⟩

theorem nafEntry_ok {F : Impl.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk e : Nat}
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
  have ha : 1≤a := by dsimp [a]; omega_arith
  have ha8 : a≤8 := by dsimp [a]; omega_arith
  have he : 2*a-1=nafMagnitude b := by dsimp [a]; omega_arith
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
    omega_arith
  refine WP.mono (nafSignedEntry_of_lookup hL.lay hAcc hm hL.exy hL.exz h.field h0 hz h0E h8
    (P := mul (nafMagnitude b) P) (fun u iu hu => ?_)) fun t ⟨kt,it,jt⟩ => ?_
  · have jp := h.stable.table a ha ha8
    rw [he] at jp
    exact nafPublicPoint_ok hL.lay hAcc hL.n hL.exy hL.exz iu hu hmag hmag15
      (by have := hL.table_le; omega_arith) hd (nafLive_table K hL.n ha ha8) sep jp
  · refine ⟨kt.mono hw,h.of_write hL hAcc hBitsWk kt hw hr
      (it.sub (fun _ hx => List.mem_append_right _ hx)),it,?_⟩
    by_cases hb : b.toNat<128
    · simpa only [nafNegative,show ¬128≤b.toNat from by omega_arith,decide_false,Bool.false_eq_true,ite_true,ite_false,hb] using jt
    · simpa only [nafNegative,show 128≤b.toNat from by omega_arith,decide_true,ite_false,ite_true,hb] using jt

end VG.Proof.Weierstrass.X86

end

end

end

/-! Adding a signed digit to the doubled accumulator. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont Spec.Weierstrass

local macro "jmem" : tactic => `(tactic| plain_simp_names simp only [nafLive,nafTableLive,jacCoords,nafSlots,nafWrites,
                   winRo,winOther,rcbR,rcbW,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,true_or,or_true])

/-- Complete Jacobian addition followed by copying the result into R. -/
theorem nafAdd_ok {F : Impl.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk e e' : Nat}
    {β : Nat → BitVec 8}
    (hL : NafLay K size) (hJ : K.J=65) (hAcc : WkOk F K.M C.p size wk (·∈nafSlots K)) (hBitsWk : K.bits+260≤wk)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    {P Q : Point C} (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (heq : add (mul e P) Q=mul e' P) {s : State}
    (h : NafCore K C base size P β e s)
    (hI : Inv K.M base size C.p (·∈nafSlots K) ([K.E.x,K.E.y,K.E.z]++nafLive K) (tmv C K.M.n base s) s)
    (hE : InvJ C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y)
      (tmv C K.M.n base s K.E.z) Q) :
    WP isa (.seq (Jacobian.jacAdd K F K.R K.E K.D) (.block (copyPt 4 K.R K.D))) s fun t =>
      ProgKeep K.M base wk (winOther K) s t ∧ NafCore K C base size P β e' t := by
  have old := hL.toWinLay hJ
  have sl : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.R K.E, x ∈ nafSlots K := by
    intro x hx
    simp only [rcbW,rcbR,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with h | h
    all_goals simp_all only [nafSlots,winRo,winOther,rcbW,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    all_goals grind
  have vr : ∀ x ∈ rcbR K.S K.R K.E, x ∈ [K.E.x,K.E.y,K.E.z]++nafLive K := by
    intro x hx
    simp only [rcbR,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> jmem
  apply WP.seq
  refine WP.mono (jacAdd_ok hL.lay hAcc hm hC ha (old.rcbApart_D (Or.inr rfl)) sl hI vr hOne
    (hC.onCurve_mul hP _) hQ h.point hE)
    fun s₁ ⟨E₁,k₁,i₁,j₁⟩ => ?_
  have sd : ∀ x ∈ rcbW K.S K.R ++ rcbR K.S K.D K.D, x ∈ nafSlots K := by
    intro x hx
    simp only [rcbW,rcbR,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with h | h
    all_goals simp_all only [nafSlots,winRo,winOther,rcbW,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    all_goals grind
  have vd : ∀ x ∈ rcbR K.S K.D K.D, x ∈ [K.D.x,K.D.y,K.D.z]++([K.E.x,K.E.y,K.E.z]++nafLive K) := by
    intro x hx
    simp only [rcbR,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> jmem
  rw [← hL.n]
  refine WP.mono (copyPoint_ok hL.lay hAcc hL.rcbApart_DR sd i₁ vd)
    fun t ⟨E₂,k₂,i₂,hv⟩ => ?_
  have kp : ProgKeep K.M base wk (winOther K) s t := (k₁.mono (by
    intro x hx; simp only [rcbW,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> jmem)).trans
    (k₂.mono (by
      intro x hx; simp only [rcbW,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> jmem))
  have ip := i₂.sub (fun x (hx : x ∈ nafLive K) => List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ hx)))
  refine ⟨kp,h.next hL hAcc hBitsWk kp ip ?_⟩
  simp only [Prod.mk.injEq] at hv
  rw [hv.1,hv.2.1,hv.2.2]
  rw [heq] at j₁
  exact j₁

end VG.Proof.Weierstrass.X86
