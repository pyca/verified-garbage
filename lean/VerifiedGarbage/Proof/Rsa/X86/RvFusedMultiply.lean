module

import VerifiedGarbage.Proof.Rsa.X86.RvFusedState
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.MulMod
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Word
import VerifiedGarbage.Proof.Rsa.X86.RvOps
import VerifiedGarbage.Proof.Rsa.X86.RvWrite
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Cold
public import VerifiedGarbage.Proof.Rsa.X86.RvFusedSmall
import VerifiedGarbage.Proof.Rsa.X86.RvSlots
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass

/-! Bounded multiplication by later public candidates. -/
@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Impl.Rsa.X86.RecoverRt (nar)
open VG.Proof.Rsa.X86.Keys

 theorem fusedSetG_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat}
    (h : KS g s0 A fusedLive AW [wRc,wR] V fusedSlots s)
    (zero : A aZ = 0) (candidate : V sCand < 100) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.fusedSetG s fun t =>
      KS g s0 (upd A mG (V sCand+2)) (mG::fusedLive) AW [wRc,wR] V fusedSlots t := by
  unfold VG.Impl.Rsa.X86.RecoverRt.fusedSetG
  refine WP.seq (WP.mono (h.copy_w (o := mG) (a := aZ) (by decide) (by decide)
    (by decide) (by decide)) fun u ⟨hu,_,_⟩ => ?_)
  rw [zero] at hu
  refine wp_movS (hu.readSlot (by decide)) fun v U _ => ?_
  have hv := hu.of_rest U.keeps (by decide) U.mem
  refine wp_addS rfl fun w D _ => ?_
  have hw := hv.of_rest D.keeps (by decide) D.mem
  have count : (w.gpr .ecx).toNat=V sCand+2 := by
    rw [D.gpr,U.gpr,BitVec.toNat_add,BitVec.toNat_ofNat]
    change (V sCand % 2^32+2)%2^32=V sCand+2
    omega
  refine VG.Proof.Rsa.X86.KeyRt.lowPtr_ok hw.rt (j := mG) (by decide) fun v hv K mem ptr => ?_
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.storeLow_ok hv (j := mG) (by decide) ptr)
    fun t ⟨_,keep,val,rest,_⟩ => ?_
  rw [mem,kw_nar] at keep val
  rw [K.1 _ (by decide)] at val
  have regs : Keeps opRegs w t := (K.mono (by decide)).trans (rest.mono (by decide))
  have ht := hw.write_w keep (by decide) (by simp) regs val (by decide) (by simp)
  rw [count,hw.arrs mG (by simp),upd_self] at ht
  simp only [Nat.zero_div,Nat.mul_zero,Nat.add_zero,upd_twice] at ht
  exact ht.mono (fun j hj => ⟨List.mem_cons_of_mem _ hj,rfl⟩) (fun j hj => ⟨hj,rfl⟩) (fun d hd => ⟨hd,rfl⟩)

 theorem fusedSmall7_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {n x : Nat}
    (h : KS g s0 A fusedLive AW [wRc,wR] V fusedSlots s)
    (modulus : A aN=n) (zero : A aZ=0) (bound : n<2^(64*g.n))
    (positive : 0<n) (vx : A mX=x) (xl : x<n) (candidate : V sCand<100) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.fusedSmall7 s fun t =>
      ∃ y, KS g s0 (upd (upd A mY y) mXm ((V sCand+2)*x%n)) fusedLive
        AW [wRc,wR] V fusedSlots t := by
  unfold VG.Impl.Rsa.X86.RecoverRt.fusedSmall7
  simp only [seqs]
  refine WP.seq (WP.mono (fusedSetG_ok h zero candidate) fun u1 h1 => ?_)
  refine WP.seq (WP.mono (h1.copy_w (o := mY) (a := mX) (by decide) (by decide)
    (by decide) (by decide)) fun u2 ⟨h2,_,_⟩ => ?_)
  refine WP.seq (WP.mono (h2.copy_w (o := mXm) (a := aZ) (by decide) (by decide)
    (by decide) (by decide)) fun u3 ⟨h3,_,_⟩ => ?_)
  refine WP.seq (wp_movS rfl fun u4 U _ => WP.block_nil ?_)
  have h4 := h3.of_rest U.keeps (by decide) U.mem
  have big : 2*n ≤ 2^(32*g.w) := by
    have pw := Nat.pow_le_pow_right (n := 2) (by decide) (show 64*g.n+1 ≤ 32*g.w by
      simp only [Geo.w,width]; omega)
    rw [Nat.pow_succ] at pw
    omega
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.mulMod_ok h4.rt
    (z := aZ) (y := mG) (x := mY) (a := mXm) (m := aN) (t := aW)
    (k := 7) (by decide) (by decide) (by decide) U.gpr) fun t ⟨_,keep,regs,result⟩ => ?_
  rw [kw_nar] at keep result
  have vz : num u4.mem g.B g.w aZ=0 := by rw [h4.arrs aZ (by decide)]; exact zero
  have vm : num u4.mem g.B g.w aN=n := by rw [h4.arrs aN (by decide)]; exact modulus
  have va : num u4.mem g.B g.w mXm=0 := by rw [h4.arrs mXm (by decide)]; exact zero
  have vy : num u4.mem g.B g.w mG=V sCand+2 := by rw [h4.arrs mG (by decide)]; rfl
  have vmul : num u4.mem g.B g.w mY=x := by rw [h4.arrs mY (by decide)]; exact vx
  have value : num t.mem g.B g.w mXm=(V sCand+2)*x%n := by
    have r := result vz (by rw [va,vm]; exact positive) (by rw [vmul,vm]; exact xl)
      (by rw [vm]; exact big)
    rw [va,vy,vmul,vm,Nat.zero_add,Nat.mod_eq_of_lt (show V sCand+2<2^7 by omega)] at r
    exact r
  let keepLive : List Nat := [0,mX,mXm]++liveM
  have pre := h4.mono (live' := keepLive) (fun j hj => ⟨by revert j; decide,rfl⟩)
    (fun j hj => ⟨hj,rfl⟩) (fun d hd => ⟨hd,rfl⟩)
  have post := pre.writeK keep (by decide : mXm<nArr) (by decide) (by decide)
    (regs.mono (by decide)) value (by decide) (by decide) (by decide)
  have observed := post.observe_w mY (by decide)
  refine ⟨num t.mem g.B g.w mY, observed.mono
    (fun j hj => ⟨by revert j; decide,?_⟩) (fun j hj => ⟨hj,rfl⟩) (fun d hd => ⟨hd,rfl⟩)⟩
  simp only [fusedLive,liveM,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with (rfl|rfl|rfl|rfl) | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem fusedMultiply_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {n x : Nat}
    (h : KS g s0 A fusedLive AW [wRc,wR] V fusedSlots s)
    (value : A mBase=n) (modulus : A aN=n) (zero : A aZ=0)
    (bound : n<2^(64*g.n)) (inverse : (n*V sInv+1)%2^32=0)
    (positive : 0<n) (vx : A mX=x) (xl : x<n) (candidate : V sCand<100) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.fusedMultiply s fun t =>
      ∃ y, KS g s0 (upd (upd A mY y) mXm ((V sCand+2)*x%n)) fusedLive
        AW [wRc,wR] V fusedSlots t := by
  unfold VG.Impl.Rsa.X86.RecoverRt.fusedMultiply
  refine WP.seq (wp_movS (h.readSlot (by decide)) fun u U _ => ?_)
  have hu := h.of_rest U.keeps (by decide) U.mem
  refine wp_subS rfl fun v D cf => WP.block_nil ?_
  have hv := hu.of_rest D.keeps (by decide) D.mem
  have test : v.cf=some (decide (V sCand<14)) := by
    rw [cf,U.gpr,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show V sCand<2^32 by omega)]
    rfl
  rw [WP.iteCold_iff]
  refine WP.ite (!decide (V sCand<14)) (by change v.cf.map (!·)=_; rw [test]; rfl) ?_ ?_
  · intro _
    exact fusedSmall7_ok hv modulus zero bound positive vx xl candidate
  · intro _
    refine WP.mono (fusedSmall_ok hv value modulus zero bound inverse positive vx xl candidate)
      fun t ht => ⟨A mY,?_⟩
    refine ht.mono (fun j hj => ⟨hj,?_⟩) (fun j hj => ⟨hj,rfl⟩) (fun d hd => ⟨hd,rfl⟩)
    simp only [fusedLive,liveM,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with (rfl|rfl|rfl|rfl) | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end VG.Proof.Rsa.X86.Recover
