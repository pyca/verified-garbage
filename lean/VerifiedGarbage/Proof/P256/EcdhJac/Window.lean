module

import VerifiedGarbage.Proof.P256.EcdhJac.Frame
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedRaw
import VerifiedGarbage.Proof.P256.EcdhDouble.Verified
public import VerifiedGarbage.Proof.P256.EcdhJac.First
public import VerifiedGarbage.Proof.P256.EcdhJac.Masks
public import VerifiedGarbage.Proof.P256.EcdhJac.Finish
public import VerifiedGarbage.Proof.P256.EcdhDouble.Certificate
public import VerifiedGarbage.Proof.P256.Linear.WeakCertificate
public import VerifiedGarbage.Proof.P256.VerifyAllocated.CachedHead
public import VerifiedGarbage.Proof.P256.VerifyAllocated.JacTail
public import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedHead
public import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedAddField
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticRR
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
import VerifiedGarbage.Proof.Weierstrass.WinJacPoint
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Proof.Weierstrass.AArch64.Chain
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
public import VerifiedGarbage.Proof.Framework.AArch64.Interleave
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombDigit

/-! ## `HotField` -/

@[expose] public section

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.P256.VerifyArithmetic Spec.Weierstrass

private theorem slots_joint : ∀ x,Sl x → Ecdsa.Verify.AArch64.Allocated.Sl x := by decide +kernel

 theorem hotField_ok {k : Kind} (cert : VerifyAllocated.Case k)
    {base : Addr} {V Out : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv M base 8192 C.p Sl V E s)
    (hslots : ∀ op∈operations k,∀x∈op.out::op.ins,Sl x)
    (hreads : readsOk (operations k) V=true)
    (hout : ∀x∈Out,x∈validAfter (operations k) V)
    (hobs : ∀x∈Out,∀i<4,VerifyAllocated.observe k (x+8*i)) :
    WP isa (Impl.P256.VerifyAllocated.program k) s fun t =>
      AllocatedFrame allocatedRegs base work s t ∧ Inv M base 8192 C.p Sl Out (runOps (operations k) E) t := by
  have hi' : Inv M base 8192 C.p Ecdsa.Verify.AArch64.Allocated.Sl V E s :=
    ⟨hi.scr,hi.mod,fun x hx => slots_joint x (hi.sl x hx),hi.lt,hi.val⟩
  refine WP.mono (Ecdsa.Verify.AArch64.Allocated.field_ok
    Ecdsa.Verify.AArch64.Allocated.raw_correct cert hi'
    (fun op hop x hx => slots_joint x (hslots op hop x hx)) hreads hout hobs)
    fun t ⟨hk,it⟩ => ⟨hk.mono (fun _ h => h) (by decide +kernel),?_,?_,?_,?_,?_⟩
  · exact it.scr
  · exact it.mod
  · intro x hx
    rcases (mem_validAfter _ _).mp (hout x hx) with hh|hh
    · exact hi.sl x hh
    · obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hh
      exact hslots op hop op.out (by simp)
  · exact it.lt
  · exact it.val


theorem hotField_all_ok {k : Kind} (cert : VerifyAllocated.Case k) (hk : k≠.doubleRR)
    {base : Addr} {V : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv M base 8192 C.p Sl V E s)
    (hslots : ∀op∈operations k,∀x∈op.out::op.ins,Sl x)
    (hreads : readsOk (operations k) V=true) :
    WP isa (Impl.P256.VerifyAllocated.program k) s fun t =>
      AllocatedFrame allocatedRegs base work s t ∧
      Inv M base 8192 C.p Sl (validAfter (operations k) V) (runOps (operations k) E) t := by
  apply hotField_ok cert hi hslots hreads (fun _ h => h)
  intro x hx i hi4
  have hs : Sl x := by
    rcases (mem_validAfter _ _).mp hx with hv|hv
    · exact hi.sl x hv
    · obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hv
      exact hslots op hop op.out (by simp)
  have hb := (show ∀ x,Sl x → x+32≤5464 from by decide +kernel) x hs
  exact ⟨Or.inl hk,Or.inl (by omega)⟩

 theorem add_ok {base : Addr} {V : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv M base 8192 C.p Sl V E s) (hv : ∀x∈CachedField.inputs,x∈V)
    (h2 : E 5400=E 768*E 768) (h3 : E 5432=E 768*(E 768*E 768)) :
    WP isa Impl.P256.EcdhJac.add s fun t =>
      AllocatedFrame allocatedRegs base work s t ∧
      Inv M base 8192 C.p Sl ([K.D.x,K.D.y,K.D.z]++V)
        (runOps (CachedField.head++CachedField.tail) E) t ∧
      (runOps (CachedField.head++CachedField.tail) E K.D.x,
       runOps (CachedField.head++CachedField.tail) E K.D.y,
       runOps (CachedField.head++CachedField.tail) E K.D.z)=
        jacAddF (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y) (E K.E.z) := by
  have hr := readsOk_mono CachedField.reads_full hv
  rw [readsOk_append,Bool.and_eq_true] at hr
  refine WP.seq (WP.mono (hotField_all_ok VerifyAllocated.CachedHead.caseProof (by decide)
    hi (by decide +kernel) hr.1) fun a ⟨ka,ia⟩ => ?_)
  refine WP.mono (hotField_all_ok VerifyAllocated.JacTail.caseProof (by decide)
    ia (by decide +kernel) hr.2) fun t ⟨kt,it⟩ => ⟨ka.trans kt,?_,CachedField.full_values E h2 h3⟩
  rw [runOps_append]
  apply it.sub
  intro x hx
  rw [mem_validAfter]
  rcases List.mem_append.mp hx with hx|hx
  · exact Or.inr (CachedField.out_tail x hx)
  · exact Or.inl ((mem_validAfter _ _).mpr (Or.inl hx))

 theorem double_ok (hC : Law C) (ha : AM3 C) {base : Addr} {E : Nat → Fe C} {s : State}
    (hi : Inv M base 8192 C.p Sl live E s) {P : Point C}
    (hp : onCurve C P=true) (hj : InvJ C (E K.R.x) (E K.R.y) (E K.R.z) P) :
    WP isa Impl.P256.EcdhJac.double s fun t =>
      AllocatedFrame allocatedRegs base work s t ∧ Inv M base 8192 C.p Sl live (runOps (operations .doubleRR) E) t ∧
      InvJ C (runOps (operations .doubleRR) E K.R.x) (runOps (operations .doubleRR) E K.R.y)
        (runOps (operations .doubleRR) E K.R.z) (add P P) := by
  exact EcdhDouble.Verified.double_ok hC ha hi hp hj

end VG.Proof.P256.EcdhJac

end

/-! ## `AddState` -/

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

def addLive : List Nat := [608,640,672]++selected++live

 theorem EntryPost.rstate {base : Addr} {P Q : Point C} {k j : Nat} {s t : State}
    (h : EntryPost base P k j live s t) (hs : RState base P Q k s) : RState base P Q k t := by
  have hp : ∀x∈live,tmv C 4 base t x=tmv C 4 base s x := by
    intro x hx; unfold tmv; rw [h.same x hx]
  refine ⟨hs.fixed.keep (frame_build h.frame),hs.table.keep h.frame,
    h.field.sub (fun _ hx => List.mem_append_right _ hx),?_⟩
  rw [hp _ (by decide),hp _ (by decide),hp _ (by decide)]
  exact hs.point

structure AddPost (base : Addr) (P Q : Point C) (k : Nat) (s t : State) : Prop where
  frame : AllocatedFrame allocatedRegs base work s t
  state : RState base P Q k t
  field : Inv M base 8192 C.p Sl addLive (tmv C 4 base t) t
  same : ∀x∈selected++live,tmv C 4 base t x=tmv C 4 base s x
  point : (tmv C 4 base t K.D.x,tmv C 4 base t K.D.y,tmv C 4 base t K.D.z)=
    jacAddF (tmv C 4 base t K.R.x) (tmv C 4 base t K.R.y) (tmv C 4 base t K.R.z)
      (tmv C 4 base t K.E.x) (tmv C 4 base t K.E.y) (tmv C 4 base t K.E.z)

theorem add_state {base : Addr} {P Q : Point C} {k : Nat} {s : State}
    (hs : RState base P Q k s)
    (hi : Inv M base 8192 C.p Sl (selected++live) (tmv C 4 base s) s)
    (h2 : tmv C 4 base s 5400=tmv C 4 base s 768*tmv C 4 base s 768)
    (h3 : tmv C 4 base s 5432=tmv C 4 base s 768*(tmv C 4 base s 768*tmv C 4 base s 768)) :
    WP isa Impl.P256.EcdhJac.add s (AddPost base P Q k s) := by
  refine WP.mono (add_ok hi (by decide) h2 h3) fun t ⟨kt,it,hp⟩ => ?_
  have same : ∀x∈selected++live,tmv C 4 base t x=tmv C 4 base s x := by
    intro x hx
    have hv := it.val x (List.mem_append_right _ hx)
    change tmv C 4 base t x=_ at hv
    rw [hv]
    apply runOps_of_not_out
    have hn : ∀op∈CachedField.head++CachedField.tail,∀x∈selected++live,op.out≠x := by decide
    exact fun op hop => hn op hop x hx
  have state : RState base P Q k t := by
    refine ⟨hs.fixed.keep (frame_build (kt.widenRegs allocated_regs)),
      hs.table.keep (kt.widenRegs allocated_regs),it.to_tmv.sub (by decide),?_⟩
    rw [same _ (by decide),same _ (by decide),same _ (by decide)]
    exact hs.point
  refine ⟨kt,state,it.to_tmv,same,?_⟩
  have vx := it.val K.D.x (by decide)
  have vy := it.val K.D.y (by decide)
  have vz := it.val K.D.z (by decide)
  change tmv C 4 base t K.D.x=_ at vx
  change tmv C 4 base t K.D.y=_ at vy
  change tmv C 4 base t K.D.z=_ at vz
  rw [vx,vy,vz,hp,same _ (by decide),same _ (by decide),same _ (by decide),
    same _ (by decide),same _ (by decide),same _ (by decide)]

end VG.Proof.P256.EcdhJac

end

/-! ## `Doubles` -/

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

theorem double_state (hC : Law C) (ha : AM3 C) {base : Addr} {P Q : Point C} {k : Nat}
    (hQ : onCurve C Q=true) {s : State} (hs : RState base P Q k s) :
    WP isa Impl.P256.EcdhJac.double s fun t =>
      AllocatedFrame allocatedRegs base work s t ∧ RState base P (add Q Q) k t := by
  exact WP.mono (double_ok hC ha hs.field hQ hs.point) fun t ⟨kt,hi,hp⟩ =>
    ⟨kt,hs.next (kt.widenRegs allocated_regs) hi hp⟩

theorem doubles_ok (hC : Law C) (ha : AM3 C) {base : Addr} {P Q : Point C} {k j : Nat}
    (hQ : onCurve C Q=true) (hj : j<52) {s : State} (hs : RState base P Q k s)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa Impl.P256.EcdhJac.dbls s fun t =>
      Frame base work s t ∧ RState base P (mul 16 Q) k t ∧ t.gpr .x19=BitVec.ofNat 64 j := by
  unfold Impl.P256.EcdhJac.dbls
  apply WP.seq
  refine WP.mono (doubleCounter_start s h19) fun a ⟨a19,ka⟩ => ?_
  have fa : Frame base work s a := (AllocatedFrame.of_keeps ka).widenRegs (by decide)
  have ca := hs.of_keeps ka (by decide)
  let I := fun q t => Frame base work s t ∧ RState base P (mul (2^(4-q)) Q) k t ∧
    t.gpr .x19=BitVec.ofNat 64 (2048*q+j)
  apply countRegLoop_ok .x4 (Inv:=I) (n:=4) (by decide)
  · intro q b hq hq5 hi
    obtain ⟨fb,cb,b19⟩ := hi
    unfold Impl.P256.EcdhJac.dblStep
    apply WP.seq
    refine WP.mono (double_state hC ha (hC.onCurve_mul hQ _) cb) fun d ⟨fd,cd⟩ => ?_
    have d19 := (fd.regs.gpr .x19 allocatedRegs_x19).trans b19
    refine WP.mono (doubleCounter_ok d hq (by omega) hj d19) fun t ⟨t19,t4,kt⟩ => ?_
    have ft : Frame base work d t := (AllocatedFrame.of_keeps kt).widenRegs (by decide)
    have ct := cd.of_keeps kt (by decide)
    have ep : add (mul (2^(4-q)) Q) (mul (2^(4-q)) Q)=mul (2^(4-(q-1))) Q := by
      rw [hC.add_mul_mul hQ,show 4-(q-1)=(4-q)+1 by omega,Nat.pow_succ]
      congr 1
      omega
    rw [ep] at ct
    exact ⟨⟨(fb.trans (fd.widenRegs allocated_regs)).trans ft,ct,t19⟩,t4⟩
  · intro t ht
    obtain ⟨ft,ct,t19⟩ := ht
    exact ⟨ft,ct,by simpa only [Nat.mul_zero,Nat.zero_add] using t19⟩
  · decide
  · refine ⟨fa,?_,a19⟩
    simpa only [Nat.sub_self,Nat.pow_zero,mul_one_pt] using ca

end VG.Proof.P256.EcdhJac

end

/-! ## `Masked` -/

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

theorem Fixed.peer_ne (hC : Law C) {base : Addr} {P : Point C} {k : Nat} {s : State}
    (h : Fixed base P k s) : P≠.infinity := by
  intro he
  have hp := h.peer
  rw [he] at hp
  exact hC.one_ne_zero (h.one.symm.trans hp.2.2)

theorem masked_ok (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {base : Addr} {P Q : Point C} {k j : Nat} (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (hq : k<C.n→Q=mul (32*Window5.winE (k+offset) 52 (j+1)) P)
    {s : State} (hs : RState base P Q k s) (hj : j<52)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j)
    (hi : Inv M base 8192 C.p Sl addLive (tmv C 4 base s) s)
    (he : 1≤digitMagnitude k j→
      InvJ C (tmv C 4 base s K.E.x) (tmv C 4 base s K.E.y) (tmv C 4 base s K.E.z)
        (Window5.winPt C P (k+offset) j) ∧ tmv C 4 base s K.E.z≠0)
    (hd : (tmv C 4 base s K.D.x,tmv C 4 base s K.D.y,tmv C 4 base s K.D.z)=
      jacAddF (tmv C 4 base s K.R.x) (tmv C 4 base s K.R.y) (tmv C 4 base s K.R.z)
        (tmv C 4 base s K.E.x) (tmv C 4 base s K.E.y) (tmv C 4 base s K.E.z)) :
    WP isa (.block maskCode) s fun t => Frame base work s t ∧ LoopInv base P k j t := by
  have hq' : k<C.n→Q=mul (32*Window5.winE (k+16*Window5.geom 52) 52 (j+1)) P := by
    simpa only [offset_eq] using hq
  have he' : 1≤magH 16 (Window5.nib (k+16*Window5.geom 52) j)→
      InvJ C (tmv C 4 base s K.E.x) (tmv C 4 base s K.E.y) (tmv C 4 base s K.E.z)
        (Window5.winPt C P (k+16*Window5.geom 52) j) ∧ tmv C 4 base s K.E.z≠0 := by
    simpa only [digitMagnitude,offset_eq] using he
  obtain ⟨Q',hQ',hq',hj'⟩ := Window5.jstep_pt hC ha hO hP (hs.fixed.peer_ne hC)
    (by decide) (by decide) hj hQ hq' hs.point he'
  rw [←offset_eq] at hq' hj'
  refine WP.mono (masks_ok hs.fixed hj h19) fun t ⟨kt,hv⟩ => ?_
  have fw := kt.widenRegs allocated_regs
  have fixed := hs.fixed.keep (frame_build fw)
  have hziff : wordsVal s.mem base 576 4=0 ↔ tmv C 4 base s 576=0 :=
    (toM_eq_zero_iff (unitMod_pow_two (by decide) _) (hi.lt _ (by decide))).symm
  have values : ∀ i<3,tmv C 4 base t (512+32*i)=
      if digitMagnitude k j=0 then tmv C 4 base s (512+32*i)
      else if tmv C 4 base s 576=0 then tmv C 4 base s (704+32*i)
      else tmv C 4 base s (608+32*i) := by
    intro i hi'
    unfold tmv
    rw [hv i hi']
    split
    · rfl
    · rw [if_congr hziff rfl rfl]
      split <;> rfl
  have ilt : ∀ x∈live,wordsVal t.mem base x 4<C.p := by
    intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · have hh : ∀ x∈[K.R.x,K.R.y,K.R.z],∃ i<3,x=512+32*i := by decide
      obtain ⟨i,hi',rfl⟩ := hh x hx
      rw [hv i hi']
      split
      · exact hi.lt _ (by
          have hh : ∀ i<3,512+32*i∈addLive := by decide
          exact hh i hi')
      · split
        · exact hi.lt _ (by
            have hh : ∀ i<3,704+32*i∈addLive := by decide
            exact hh i hi')
        · exact hi.lt _ (by
            have hh : ∀ i<3,608+32*i∈addLive := by decide
            exact hh i hi')
    · exact fixed.field.lt x hx
  have it : Inv M base 8192 C.p Sl live (tmv C 4 base t) t :=
    ⟨fixed.field.scr,fixed.field.mod,by decide,ilt,fun _ _ => rfl⟩
  refine ⟨fw,⟨⟨Q',hQ',hq',fixed,hs.table.keep fw,it,?_⟩,
    (kt.regs.gpr _ allocatedRegs_x19).trans h19⟩⟩
  have v0 := values 0 (by decide)
  have v1 := values 1 (by decide)
  have v2 := values 2 (by decide)
  change tmv C 4 base t K.R.x=_ at v0
  change tmv C 4 base t K.R.y=_ at v1
  change tmv C 4 base t K.R.z=_ at v2
  rw [v0,v1,v2]
  have dx := congrArg Prod.fst hd
  have dy := congrArg (fun p => p.2.1) hd
  have dz := congrArg (fun p => p.2.2) hd
  dsimp only at dx dy dz
  change InvJ C (if digitMagnitude k j=0 then tmv C 4 base s K.R.x else
      if tmv C 4 base s K.R.z=0 then tmv C 4 base s K.E.x else tmv C 4 base s K.D.x)
    (if digitMagnitude k j=0 then tmv C 4 base s K.R.y else
      if tmv C 4 base s K.R.z=0 then tmv C 4 base s K.E.y else tmv C 4 base s K.D.y)
    (if digitMagnitude k j=0 then tmv C 4 base s K.R.z else
      if tmv C 4 base s K.R.z=0 then tmv C 4 base s K.E.z else tmv C 4 base s K.D.z) Q'
  rw [dx,dy,dz]
  exact hj'

end VG.Proof.P256.EcdhJac

end

/-! ## `Step` -/

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

/-- A block of the interleaving's class whose footprint writes no vector
register keeps them all. -/
theorem runBlock_keepsV {a : List Instr}
    (H : ∀ x∈a,∃ F,Interleave.fp .x0 x=some F ∧ ∀ i,F.vw.testBit i=false) :
    ∀ {s s' : State},runBlock isa a s=some s'→s'.v=s.v := by
  induction a with
  | nil => intro s s' h; cases h; rfl
  | cons i is ih =>
    intro s s' h
    have h' : (exec i s).bind (runBlock isa is)=some s' := h
    cases he : exec i s with
    | none => rw [he] at h'; cases h'
    | some s₁ =>
      rw [he] at h'
      obtain ⟨F,hf,hv⟩ := H i (List.mem_cons_self ..)
      have fr := Interleave.frame hf he
      rw [ih (fun x hx => H x (List.mem_cons_of_mem _ hx)) h']
      funext r
      exact fr.v r (hv _)

theorem keepsV_of_blockFp {a : List Instr} (h : (Interleave.blockFp .x0 a).map Interleave.Fp.vw=some 0) :
    ∀ x∈a,∃ F,Interleave.fp .x0 x=some F ∧ ∀ i,F.vw.testBit i=false := by
  cases ha : Interleave.blockFp .x0 a with
  | none => rw [ha] at h; cases h
  | some A =>
    rw [ha,Option.map_some,Option.some.injEq] at h
    intro x hx
    obtain ⟨F,hf,hs⟩ := Interleave.blockFp_sub ha x hx
    refine ⟨F,hf,fun i=>?_⟩
    cases hb : F.vw.testBit i
    · rfl
    · have := hs.vw i hb; rw [h,Nat.zero_testBit] at this; cases this

theorem double_keepsV :
    ∀ x∈Impl.P256.EcdhDouble.code,∃ F,Interleave.fp .x0 x=some F ∧ ∀ i,F.vw.testBit i=false :=
  keepsV_of_blockFp (by decide +kernel)

theorem doubleSel_indeps :
    Interleave.Indeps .x0 Impl.P256.EcdhDouble.code (Impl.P256.EcdhSelect.neonScan 2816 16) :=
  Interleave.indeps_of_check (by decide +kernel)

/-- The doubling, with the vector registers it keeps. -/
theorem double_stateV (hC : Law C) (ha : AM3 C) {base : Addr} {P Q : Point C} {k : Nat}
    (hQ : onCurve C Q=true) {s : State} (hs : RState base P Q k s) :
    WP isa (.block Impl.P256.EcdhDouble.code) s fun t =>
      AllocatedFrame allocatedRegs base work s t ∧ RState base P (add Q Q) k t ∧ t.v=s.v := by
  obtain ⟨t,hr,hq⟩ := Interleave.runBlock_of_WP (double_state hC ha hQ hs)
  exact WP.of_runBlock ⟨t,hr,hq.1,hq.2,runBlock_keepsV double_keepsV hr⟩

theorem step_split : tc.digit ++ Impl.P256.EcdhSelect.neonSetup ++ Impl.P256.EcdhJac.doubleSel ++
    Impl.P256.EcdhSelect.neonStore Impl.P256.EcdhJac.K.E.x Impl.P256.EcdhJac.z2 ++
    negYW M 5 K.neg K.zero K.E.y K.bits =
    tc.digit ++ (Select.setup ++ (Impl.AArch64Weave.weave Impl.P256.EcdhDouble.code
      (Impl.P256.EcdhSelect.neonScan 2816 16) ++ (Select.store ++ negYW M 5 K.neg K.zero K.E.y K.bits))) := by
  simp only [List.append_assoc]; rfl

theorem step_ok (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {base : Addr} {P : Point C} {k j : Nat} (hP : onCurve C P=true)
    (hj : 1≤j) (hj52 : j≤51) {s : State} (hs : LoopInv base P k j s) :
    WP isa Impl.P256.EcdhJac.step s fun t => Frame base work s t ∧ LoopInv base P k (j-1) t := by
  obtain ⟨⟨Q,hQ,hq,rs⟩,s19⟩ := hs
  unfold Impl.P256.EcdhJac.step
  apply WP.seq
  refine WP.mono (decCounter_ok s hj (by omega) s19) fun a ⟨a19,ka⟩ => ?_
  have fa : Frame base work s a := (AllocatedFrame.of_keeps ka).widenRegs (by decide)
  have ra := rs.of_keeps ka (by decide)
  apply WP.seq
  refine WP.mono (doubles_ok hC ha hQ (by omega) ra a19) fun b ⟨fb,rb,b19⟩ => ?_
  have qb : k<C.n → mul 32 Q=mul (32*Window5.winE (k+offset) 52 ((j-1)+1)) P := by
    intro hk
    rw [hq hk,Window5.mul_mul hC hP,show j-1+1=j by omega]
  apply WP.seq
  -- The digit, the selection's setup, the fifth doubling with the selection's
  -- rows, the store and the negation.
  rw [step_split,WP.block_append_iff]
  refine WP.mono (digitW_ok tc rb.field.scr (k:=k+offset) (j:=j-1) (N:=260)
    (by decide) (by decide) (by change 5*(j-1)+5≤260; omega) (by decide) (by decide) b19 rb.fixed.bits)
    fun u ⟨hu,ku⟩=>?_
  have fu : Frame base work b u := (AllocatedFrame.of_keeps ku).widenRegs (by decide)
  have ru := rb.of_keeps ku (by decide)
  have hmag : u.gpr .x2=BitVec.ofNat 64 (magH 16 (Window5.nib (k+offset) (j-1))) := by
    change u.gpr .x2=BitVec.ofNat 64 (magH 16 (combWin 5 (k+offset) (j-1))) at hu
    simpa only [Window5.combWin_five] using hu
  rw [WP.block_append_iff]
  refine WP.mono (Select.setup_ok u) fun s₁ ⟨idx₁,inc₁,mag₁,z₁,k₁⟩=>?_
  have f₁ : Frame base work u s₁ := (AllocatedFrame.of_keeps k₁.keeps).widenRegs (by decide)
  have r₁ := ru.of_keeps k₁.keeps (by decide)
  rw [WP.block_append_iff]
  refine Interleave.WP.weave doubleSel_indeps ?_
  have h16 : onCurve C (mul 16 Q)=true := hC.onCurve_mul hQ _
  refine WP.mono (double_stateV hC ha h16 r₁) fun s₂ ⟨fd,r₂,v₂⟩=>?_
  have e32 : add (mul 16 Q) (mul 16 Q)=mul 32 Q := by
    rw [hC.add_mul_mul hQ]
  rw [e32] at r₂
  have f₂ : Frame base work s₁ s₂ := fd.widenRegs allocated_regs
  have s₂19 : s₂.gpr .x19=BitVec.ofNat 64 (j-1) := by
    rw [fd.regs.gpr _ allocatedRegs_x19,k₁.gpr _ (by decide),ku.gpr _ (by decide),b19]
  rw [← WP.block_append_iff,← List.append_assoc]
  refine WP.mono (signedEntryV_ok (fun _ h => h) (by decide) r₂.field r₂.fixed r₂.table (by omega) s₂19
    (by rw [v₂]; exact idx₁) (by rw [v₂]; exact inc₁)
    (by rw [v₂,mag₁,hmag]) (fun i hi=>by rw [v₂]; exact z₁ i hi)) fun e he => ?_
  have re := he.rstate r₂
  have e19 := he.counter.trans s₂19
  apply WP.seq
  refine WP.mono (add_state re he.field he.cache2 (by
    rw [he.cache3,he.cache2]; exact Lean.Grind.CommSemiring.mul_comm _ _)) fun d hd => ?_
  have d19 := (hd.frame.regs.gpr _ allocatedRegs_x19).trans e19
  have ep : 1≤digitMagnitude k (j-1) →
      InvJ C (tmv C 4 base d K.E.x) (tmv C 4 base d K.E.y) (tmv C 4 base d K.E.z)
        (Window5.winPt C P (k+offset) (j-1)) ∧ tmv C 4 base d K.E.z≠0 := by
    intro hn
    have hp := he.point hn
    rw [hd.same _ (by decide),hd.same _ (by decide),hd.same _ (by decide)]
    exact ⟨hp.jac,hp.z⟩
  refine WP.mono (masked_ok hC ha hO hP (hC.onCurve_mul hQ _) qb hd.state
    (by omega) d19 hd.field ep hd.point) fun t ⟨ft,ht⟩ => ?_
  exact ⟨((((((fa.trans fb).trans fu).trans f₁).trans f₂).trans he.frame).trans
    (hd.frame.widenRegs allocated_regs)).trans ft,ht⟩

theorem loop_ok (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {base : Addr} {P : Point C} {k : Nat} (hP : onCurve C P=true)
    {s : State} (hs : LoopInv base P k 51 s) :
    WP isa (.loop Impl.P256.EcdhJac.step (.nonzero .x .x19)) s fun t =>
      Frame base work s t ∧ LoopInv base P k 0 t := by
  apply countLoop_ok (Inv:=fun j t => Frame base work s t ∧ LoopInv base P k j t)
    (n:=51) (by decide)
  · intro j t hj hj51 ⟨fr,hi⟩
    exact WP.mono (step_ok hC ha hO hP hj hj51 hi) fun u ⟨fu,hu⟩ =>
      ⟨⟨fr.trans fu,hu⟩,hu.counter⟩
  · exact fun _ h => h
  · decide
  · exact ⟨AllocatedFrame.refl _ _ _ _,hs⟩

end VG.Proof.P256.EcdhJac

end

/-! ## `Window` -/

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

theorem window_ok (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {base : Addr} {P : Point C} {k : Nat} {s : State}
    (hP : onCurve C P=true) (hk : k<2^256) (hf : Fixed base P k s) :
    WP isa Impl.P256.EcdhJac.window s (WindowPost base P k s) := by
  unfold Impl.P256.EcdhJac.window
  refine WP.seq (WP.mono (build_ok hC ha hO hP hf) fun a ⟨fa,hfa,ta⟩=>?_)
  refine WP.seq (WP.mono (first_ok hC hP hk hfa ta) fun b ⟨fb,hb⟩=>?_)
  refine WP.seq (WP.mono (loop_ok hC ha hO hP hb) fun d ⟨fd,hd⟩=>?_)
  refine WP.mono (finish_ok hC hd) fun t ht=>?_
  exact ⟨fa.trans ((frame_build fb).trans ((frame_build fd).trans ht.frame)),ht.field,ht.point⟩

end VG.Proof.P256.EcdhJac

end
