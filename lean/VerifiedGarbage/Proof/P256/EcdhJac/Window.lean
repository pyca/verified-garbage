module

import VerifiedGarbage.Proof.P256.EcdhJac.Frame
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedRaw
import VerifiedGarbage.Proof.P256.EcdhDouble.Verified
public import VerifiedGarbage.Impl.P256.EcdhJac
public import VerifiedGarbage.Proof.P256.EcdhJac.State
public import VerifiedGarbage.Proof.P256.EcdhJac.Select
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowNeg
import VerifiedGarbage.Proof.Weierstrass.AArch64.Zero
import VerifiedGarbage.Proof.Weierstrass.JacMadd
import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowInvariant
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.P256.EcdhJac.Masks
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
public import VerifiedGarbage.Proof.Weierstrass.JacAdd
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Weierstrass.Window5
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
public import VerifiedGarbage.Proof.Framework.AArch64.Interleave
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddCall
import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract
public import VerifiedGarbage.Proof.P256.EcdhJac.OutCertificate
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJOut

/-! ### `P256.EcdhJac.Finish`, which this module and modules that import it used -/

section

/-! ### `P256.EcdhJac.Extra`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Impl.P256.EcdhJac (extra)
open VG.Proof.Weierstrass.AArch64
open VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open Spec.Weierstrass
def saveExtra : List Instr := extra.map fun (r,d) => VG.Impl.Mont.AArch64.st r d
def restoreExtra : List Instr := extra.map fun (r,d) => VG.Impl.Mont.AArch64.ld r d
open VG.Proof.Ed25519.AArch64 (Keeps)

/-- The additional ABI registers and live output pointer. -/
def extraRegs : List Reg := extra.map Prod.fst

theorem saveExtra_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hsize : 7840≤size) : WP isa (.block saveExtra) s fun t =>
      KeepRegs [] s t ∧ Outside base 7800 40 s.mem t.mem ∧ Spill.Saved base s.gpr extra t.mem := by
  refine WP.mono (Spill.save_wp (b:=.x0) (l:=extra) (by decide) (fun p hp => hs.st (by
    have h : ∀ p∈extra,p.2+8≤7840 := by decide
    exact Nat.le_trans (h p hp) hsize))) fun t h => ⟨⟨?_,h.rd,h.wr,h.sp⟩,?_,?_⟩
  · intro r _; exact congrFun h.gpr r
  · rw [h.mem,hs.x0]
    intro x hx
    change ((((s.mem.writeW (off base 7800) (s.gpr .x26)).writeW (off base 7808) (s.gpr .x27)).writeW
      (off base 7816) (s.gpr .x28)).writeW (off base 7824) (s.gpr .x30)).writeW (off base 7832) (s.gpr .x20) x=s.mem x
    rw [(writeW_outside _ base (d:=7832) _ (by decide)) x (by omega_using [hx]),
      (writeW_outside _ base (d:=7824) _ (by decide)) x (by omega_using [hx]),
      (writeW_outside _ base (d:=7816) _ (by decide)) x (by omega_using [hx]),
      (writeW_outside _ base (d:=7808) _ (by decide)) x (by omega_using [hx]),
      (writeW_outside _ base (d:=7800) _ (by decide)) x (by omega_using [hx])]
  · rw [h.mem,hs.x0]; exact Spill.saveMem_saved (by decide) _ _ _

/-- A body's write frame preserves the saved extra registers. -/
theorem savedExtra_keep {base : Addr} {g : Reg → BitVec 64} {s t : State}
    {W : List (Nat × Nat)} (h : Spill.Saved base g extra s.mem)
    (hu : Unch base W s.mem t.mem)
    (hw : ∀ w∈W,w.1+w.2≤7800 ∨ 7840≤w.1) : Spill.Saved base g extra t.mem := by
  intro p hp
  have hb : ∀ p∈extra,7800≤p.2 ∧ p.2+8≤7840 := by decide
  change word t.mem base p.2=_
  rw [hu.word (fun w hm => by have := hw w hm; have := hb p hp; omega_arith) (by have := hb p hp; omega_using [this])]
  exact h p hp

 theorem restoreExtra_ok {s : State} {base : Addr} {size : Nat} {g : Reg → BitVec 64}
    (hs : Scr s base size) (hsize : 7840≤size) (hsv : Spill.Saved base g extra s.mem) :
    WP isa (.block restoreExtra) s fun t =>
      VG.Proof.Ed25519.AArch64.Keeps extraRegs s t ∧ ∀ r∈extraRegs,t.gpr r=g r := by
  refine WP.mono (Spill.restore_wp hs.x0 (l:=extra) (by decide) (by decide)
    (fun p hp => by
      rw [←hs.x0]
      apply hs.ld
      have hh : ∀ p∈extra,p.2+8≤7840 := by decide
      exact Nat.le_trans (hh p hp) hsize) hsv) fun t h => ⟨⟨h.other,h.mem,h.rd,h.wr,h.sp⟩,?_⟩
  intro r hr
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
  exact h.gpr p hp

/-- Restoring the saved registers removes them from the enclosing register frame. -/
theorem restoreExtra_frame {s a b t : State} {rs : List Reg}
    (hs : KeepRegs [] s a) (hb : KeepRegs rs a b)
    (ht : Keeps extraRegs b t) (hv : ∀ r∈extraRegs,t.gpr r=s.gpr r) :
    KeepRegs (rs.filter fun r => r∉extraRegs) s t := by
  refine ⟨?_,ht.rd.trans (hb.rd.trans hs.rd),ht.wr.trans (hb.wr.trans hs.wr),ht.sp.trans (hb.sp.trans hs.sp)⟩
  intro r hr
  by_cases he : r∈extraRegs
  · exact hv r he
  · have hnot : r∉rs := by simpa only [List.mem_filter,decide_eq_true_eq,he,not_false_eq_true,and_true] using hr
    rw [ht.gpr r he,hb.gpr r hnot,hs.gpr r (by simp)]

theorem Fixed.keep_save {base : Addr} {P : Point C} {k : Nat} {s t : State}
    (h : Fixed base P k s) (hk : AllocatedFrame [] base [(7800,40)] s t) : Fixed base P k t := by
  have hw : ∀ x∈ro,wordsVal t.mem base x 4=wordsVal s.mem base x 4 := by
    intro x hx
    exact hk.unch.wordsVal (by
      have hh : ∀ x∈ro,∀ w∈[(7800,40)],x+32≤w.1 ∨ w.1+w.2≤x := by decide +kernel
      exact hh x hx) (by
      have hh : ∀ x∈ro,x+32≤2^64 := by decide +kernel
      exact hh x hx)
  have hf : ∀ x∈ro,tmv C 4 base t x=tmv C 4 base s x := fun x hx => by unfold tmv; rw [hw x hx]
  refine ⟨⟨hk.scr (by decide) h.field.scr,h.field.mod.unch hk.unch (by decide +kernel) h.field.scr.nowrap,
    h.field.sl,fun x hx => by change wordsVal t.mem base x 4<C.p; rw [hw x hx]; exact h.field.lt x hx,fun _ _ => rfl⟩,?_,?_,?_,?_⟩
  · rw [hw _ (by decide)]; exact h.zero
  · rw [hf _ (by decide),hf _ (by decide),hf _ (by decide)]; exact h.peer
  · rw [hf _ (by decide)]; exact h.one
  · intro i hi
    rw [hk.unch.byte (by
      intro w hw
      have hh : ∀ w∈[(7800,40)],K.bits+260≤w.1 ∨ w.1+w.2≤K.bits := by decide +kernel
      have := hh w hw; omega_using [hi, this]) (by change 1824+i+1≤2^64; omega_using [hi])]
    exact h.bits i hi

end VG.Proof.P256.EcdhJac

end

end


/-! ## `WindowPost` -/

@[expose] public section

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass

/-- The window computation writes only its declared work areas. Its output
is the existing project's homogeneous point representation. Invalid scalars
need no multiplication identity because the public API rejects them. -/
structure WindowPost (base : Addr) (P : Point C) (k : Nat) (s t : State) : Prop where
  frame : Frame base buildWork s t
  field : Inv M base 8192 C.p Sl live (tmv C 4 base t) t
  point : 1≤k → k<C.n → Rep C (tmv C 4 base t K.R.x)
    (tmv C 4 base t K.R.y) (tmv C 4 base t K.R.z) (mul k P)

end VG.Proof.P256.EcdhJac

end

/-! ## `Wrapped` -/

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass

def wrappedWrites : List (Nat×Nat) := buildWork++[(7800,40)]
def wrappedRegs : List Reg := regs.filter fun r=>r∉extraRegs

structure WrappedPost (base : Addr) (P : Point C) (k : Nat) (s t : State) : Prop where
  frame : AllocatedFrame wrappedRegs base wrappedWrites s t
  field : Inv M base 8192 C.p Sl live (tmv C 4 base t) t
  point : 1≤k → k<C.n → Rep C (tmv C 4 base t K.R.x)
    (tmv C 4 base t K.R.y) (tmv C 4 base t K.R.z) (mul k P)
  restored : ∀ r∈extraRegs,t.gpr r=s.gpr r

theorem wrapped_ok {base : Addr} {P : Point C} {k : Nat} {s : State}
    (hf : Fixed base P k s)
    (hwin : ∀ u,Fixed base P k u → WP isa Impl.P256.EcdhJac.window u (WindowPost base P k u)) :
    WP isa Impl.P256.EcdhJac.wrappedWindow s (WrappedPost base P k s) := by
  unfold Impl.P256.EcdhJac.wrappedWindow
  refine WP.seq (WP.mono (saveExtra_ok hf.field.scr (by decide)) fun a ⟨ka,oa,sa⟩=>?_)
  have fa : AllocatedFrame [] base [(7800,40)] s a := ⟨ka,oa.unch⟩
  refine WP.seq (WP.mono (hwin a (hf.keep_save fa)) fun b hb=>?_)
  have sb := savedExtra_keep sa hb.frame.unch (by decide)
  refine WP.mono (restoreExtra_ok hb.field.scr (by decide) sb) fun t ⟨kt,rt⟩=>?_
  have hu : Unch base wrappedWrites s.mem b.mem := (oa.unch.trans hb.frame.unch).mono (by decide)
  refine ⟨⟨restoreExtra_frame ka hb.frame.regs kt rt,fun x hx=>
    (congrFun kt.mem x).trans (hu x hx)⟩,
    (hb.field.of_keeps kt (by decide)).to_tmv,?_,rt⟩
  intro hk hn
  have ht : ∀ x,tmv C 4 base t x=tmv C 4 base b x := fun x=>by unfold tmv; rw [kt.mem]
  rw [ht,ht,ht]
  exact hb.point hk hn

end VG.Proof.P256.EcdhJac

end

/-! ## `Finish` -/

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

def windowFinish : Prog isa := .seq (.block tc.outFix) (Impl.P256.EcdhJac.arithmetic tc.outOps)

/-- Final conversion preserves a canonical infinity as well as finite points. -/
theorem finish_point_ok (hC : Law C) {base : Addr} {P Q : Point C} {k : Nat} {s : State}
    (hi : RState base P Q k s) :
    WP isa windowFinish s fun t=>Frame base work s t ∧ Fixed base P k t ∧
      Inv M base 8192 C.p Sl live (tmv C 4 base t) t ∧
      Rep C (tmv C 4 base t K.R.x) (tmv C 4 base t K.R.y) (tmv C 4 base t K.R.z) Q := by
  have hm : UnitMod C.p (2^(64*M.n)) := unitMod_pow_two (by decide) _
  rw [windowFinish]
  refine WP.seq (WP.mono (outFix_ok tc hi.field.scr (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hi.fixed.zero) fun u ⟨ey,ku,ou⟩=>?_)
  have fu : Frame base work s u := ⟨ku.mono (by decide),ou.unch.cover (by decide)⟩
  have fx:=hi.fixed.keep (frame_build fu)
  have ex : wordsVal u.mem base K.R.x 4=wordsVal s.mem base K.R.x 4 := ou.wordsVal (by decide) (by decide)
  have ez : wordsVal u.mem base K.R.z 4=wordsVal s.mem base K.R.z 4 := ou.wordsVal (by decide) (by decide)
  have iu : Inv M base 8192 C.p Sl live (tmv C 4 base u) u := by
    refine ⟨fu.scr regs_x0 hi.field.scr,fx.field.mod,hi.field.sl,?_,fun _ _=>rfl⟩
    intro x hx
    change x∈[K.R.x,K.R.y,K.R.z]++ro at hx
    rcases List.mem_append.mp hx with hx|hx
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl
      · change wordsVal u.mem base K.R.x 4<C.p
        rw [ex]; exact hi.field.lt _ (by decide)
      · change wordsVal u.mem base tc.A.y tc.M.n<C.p
        rw [ey]; split
        · decide
        · exact hi.field.lt _ (by decide)
      · change wordsVal u.mem base K.R.z 4<C.p
        rw [ez]; exact hi.field.lt _ (by decide)
    · exact fx.field.lt x hx
  have hsl : ∀ op∈tc.outOps,∀ x∈op.out::op.ins,Sl x := by decide
  have hlo : ∀ op∈tc.outOps,Low M (op.out::op.ins) := fun _ _=>Low.small (by decide) _
  have hreads : readsOk tc.outOps live=true := by decide
  refine WP.mono (field_ok Out.caseProof layout aligned hm iu hsl hlo hreads)
    fun t ⟨kp,it⟩=>?_
  have ft : Frame base work u t := AllocatedFrame.of_prog kp clob_regs (by decide)
  have fr:=fu.trans ft
  have iv := it.sub (fun x (hx : x∈live)=>(mem_validAfter _ _).mpr (Or.inl hx))
  refine ⟨fr,hi.fixed.keep (frame_build fr),iv.to_tmv,?_⟩
  have hv : ∀x∈live,tmv C 4 base t x=runOps tc.outOps (tmv C 4 base u) x :=
    fun x hx=>iv.val x hx
  rw [hv K.R.x (by decide),hv K.R.y (by decide),hv K.R.z (by decide)]
  have hx : tmv C 4 base u K.R.x=tmv C 4 base s K.R.x := by unfold tmv; rw [ex]
  have hz : tmv C 4 base u K.R.z=tmv C 4 base s K.R.z := by unfold tmv; rw [ez]
  have hy : tmv C 4 base u K.R.y=if tmv C 4 base s K.R.z=0 then 1 else tmv C 4 base s K.R.y := by
    change toM C.p (2^(64*tc.M.n)) (wordsVal u.mem base tc.A.y tc.M.n)=_
    rw [ey]
    have hzero : (tmv C 4 base s K.R.z=0)↔wordsVal s.mem base K.R.z 4=0 :=
      toM_eq_zero_iff hm (hi.field.lt _ (by decide))
    change toM C.p (2^(64*4)) (if wordsVal s.mem base K.R.z 4=0 then K.one else wordsVal s.mem base K.R.y 4)=_
    by_cases hz : wordsVal s.mem base K.R.z 4=0
    · simp only [hz,hzero.mpr hz,ite_true]
      exact toM_one (m:=C.p) (R:=2^(64*4)) hm
    · have hv : tmv C 4 base s K.R.z≠0 := fun h=>hz (hzero.mp h)
      simp only [hz,hv,ite_false]
  have outvals (E : Nat→Fe C) : (runOps tc.outOps E K.R.x,
      runOps tc.outOps E K.R.y,runOps tc.outOps E K.R.z)=
      (E K.R.x*E K.R.z,E K.R.y,E K.R.z*E K.R.z*E K.R.z) := by
    simp only [tc,Impl.P256.EcdhJac.tc,TCombCfg.outOps,runOps,List.foldl_cons,List.foldl_nil,
      FOp.run,Function.update_apply,
      show K.R.x≠K.R.z from by decide,show K.R.x≠K.S.t0 from by decide,
      show K.R.y≠K.R.x from by decide,show K.R.y≠K.R.z from by decide,
      show K.R.y≠K.S.t0 from by decide,show K.R.z≠K.R.x from by decide,
      show K.R.z≠K.S.t0 from by decide,show K.S.t0≠K.R.x from by decide,ite_true,ite_false]
  have vals:=outvals (tmv C 4 base u)
  have vx:=congrArg Prod.fst vals
  have vy:=congrArg (fun p=>p.2.1) vals
  have vz:=congrArg (fun p=>p.2.2) vals
  dsimp only at vx vy vz
  rw [vx,vy,vz,hx,hy,hz]
  exact hi.point.out hC

theorem finish_ok (hC : Law C) {base : Addr} {P : Point C} {k : Nat} {s : State}
    (hi : LoopInv base P k 0 s) :
    WP isa windowFinish s (WindowPost base P k s) := by
  obtain ⟨Q,_,he,hq⟩:=hi.state
  refine WP.mono (finish_point_ok hC hq) fun t ⟨fr,_,it,hrep⟩=>?_
  refine ⟨frame_build fr,it,fun _ hk=>?_⟩
  have eq:=he hk
  rw [Window5.winE_zero,offset_eq,Nat.add_sub_cancel] at eq
  rw [←eq]
  exact hrep

end VG.Proof.P256.EcdhJac

end

end

end

/-! ### `P256.EcdhJac.First`, which only this module used -/

section

/-! ## `Entry` -/

@[expose] public section

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

def selected : List Nat := [704,736,768,5400,5432]

theorem selected_mem : ∀ i<5,selectedSlot i∈selected := by decide

/-- What a selection of entry `a` gives, from code `c` that stores the
entry's words and keeps the registers but `R` (`x5`, `x17`). -/
theorem selectBlock_field_ok {base : Addr} {P : Point C} {k a : Nat} {s : State}
    {V : List Nat} (hV : ∀ x∈V,x∈live)
    (hi : Inv M base 8192 C.p Sl V (tmv C 4 base s) s)
    (hf : Fixed base P k s) (ht : TblOk base P 16 s)
    (ha : a≤16) {c : List Instr} {R : List Reg} (hR : ∀ r∈R,r∈[.x5,.x17])
    (hc : WP isa (.block c) s fun t=>
      (∀ j<20,word t.mem base (Select.output j)=if a=0 then 0 else
        word s.mem base (2816+160*(a-1)+8*j)) ∧
      KeepRegs R s t ∧ Unch base Select.outputRanges s.mem t.mem) :
    WP isa (.block c) s fun t=>
      Frame base work s t ∧ t.gpr .x19=s.gpr .x19 ∧
      Inv M base 8192 C.p Sl (selected++V) (tmv C 4 base t) t ∧
      (1≤a→JPt base t selectedSlot (mul a P)) ∧
      (a=0→∀ i<5,wordsVal t.mem base (selectedSlot i) 4=0) ∧
      (∀ x∈V,wordsVal t.mem base x 4=wordsVal s.mem base x 4) := by
  refine WP.mono hc fun t ⟨hw,hkeep',ho⟩=>?_
  obtain hkeep : KeepRegs [.x5,.x17] s t := hkeep'.mono hR
  obtain fr : Frame base work s t := ⟨hkeep.mono (by decide),ho.cover (by decide)⟩
  obtain hv : ∀ i<5,wordsVal t.mem base (selectedSlot i) 4=
      if a=0 then 0 else wordsVal s.mem base (entrySlot a i) 4 := by
    intro i hi'
    by_cases hz : a=0
    · rw [ite_eq_left hz]
      apply (wordsVal_eq_zero_iff _ _ _ _).mpr
      intro j hj
      obtain hh := hw (4*i+j) (by omega_arith)
      obtain hout : Select.output (4*i+j)=selectedSlot i+8*j := by
        unfold Select.output selectedSlot; split <;> split <;> omega_arith
      simpa only [hout,hz,ite_true] using hh
    · rw [ite_eq_right hz]
      apply wordsVal_of_words₂
      intro j hj
      obtain hh := hw (4*i+j) (by omega_arith)
      obtain hout : Select.output (4*i+j)=selectedSlot i+8*j := by
        unfold Select.output selectedSlot; split <;> split <;> omega_arith
      obtain hin : 2816+160*(a-1)+8*(4*i+j)=entrySlot a i+8*j := by unfold entrySlot; omega_arith
      simpa only [hout,hin,ite_eq_right hz] using hh
  obtain hfix := hf.keep (frame_build fr)
  refine ⟨fr,hkeep.gpr _ (by decide),?_,fun hnz=>(ht a hnz ha).congr (fun i hi'=>by
    rw [hv i hi',ite_eq_right (by omega_arith)]),fun hz i hi'=>by
      simpa only [hz,ite_true] using hv i hi',?_⟩
  rotate_left
  · intro x hx
    exact ho.wordsVal (by
      obtain hh : ∀ x∈live,∀ w∈Select.outputRanges,x+32≤w.1 ∨ w.1+w.2≤x := by decide
      exact hh x (hV x hx)) (by
      obtain hh : ∀ x∈live,x+32≤2^64 := by decide
      exact hh x (hV x hx))
  refine ⟨fr.scr regs_x0 hi.scr,hfix.field.mod,?_,?_,fun _ _=>rfl⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · have hh : ∀ x∈selected,Sl x := by decide
      exact hh x hx
    · exact hi.sl x hx
  · intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · have hh : ∀ x∈selected,∃ i<5,x=selectedSlot i := by decide
      obtain ⟨i,hi',rfl⟩:=hh x hx
      change wordsVal t.mem base (selectedSlot i) 4<C.p
      rw [hv i hi']
      split
      · decide
      · exact (ht a (by omega_arith) ha).lt i hi'
    · have hwv : wordsVal t.mem base x 4=wordsVal s.mem base x 4 :=
        ho.wordsVal (by
          obtain hsep : ∀ x∈live,∀ w∈Select.outputRanges,x+32≤w.1 ∨ w.1+w.2≤x := by decide
          exact hsep x (hV x hx)) (by
          obtain hb : ∀ x∈live,x+32≤2^64 := by decide
          exact hb x (hV x hx))
      change wordsVal t.mem base x 4<C.p
      rw [hwv]; exact hi.lt x hx

theorem select_field_ok {base : Addr} {P : Point C} {k a : Nat} {s : State}
    {V : List Nat} (hV : ∀ x∈V,x∈live)
    (hi : Inv M base 8192 C.p Sl V (tmv C 4 base s) s)
    (hf : Fixed base P k s) (ht : TblOk base P 16 s)
    (ha : a≤16) (hmag : s.gpr .x2=BitVec.ofNat 64 a) :
    WP isa (.block (Impl.P256.EcdhSelect.neon 2816 704 5400)) s fun t=>
      Frame base work s t ∧ t.gpr .x19=s.gpr .x19 ∧
      Inv M base 8192 C.p Sl (selected++V) (tmv C 4 base t) t ∧
      (1≤a→JPt base t selectedSlot (mul a P)) ∧
      (a=0→∀ i<5,wordsVal t.mem base (selectedSlot i) 4=0) ∧
      (∀ x∈V,wordsVal t.mem base x 4=wordsVal s.mem base x 4) :=
  selectBlock_field_ok hV hi hf ht ha (fun _ h=>h) (Select.neon_ok hi.scr ha hmag)

/-- The selection's rows and store, from its setup's broadcasts. -/
theorem selectV_field_ok {base : Addr} {P : Point C} {k a : Nat} {s : State}
    {V : List Nat} (hV : ∀ x∈V,x∈live)
    (hi : Inv M base 8192 C.p Sl V (tmv C 4 base s) s)
    (hf : Fixed base P k s) (ht : TblOk base P 16 s) (ha : a≤16)
    (hidx : s.v .v28=dup2 0) (hinc : s.v .v31=dup2 1) (hmag : s.v .v30=dup2 (BitVec.ofNat 64 a))
    (hz : ∀ i<10,s.v (Select.acc i)=0) :
    WP isa (.block (Select.scan 2816 16++Select.store)) s fun t=>
      Frame base work s t ∧ t.gpr .x19=s.gpr .x19 ∧
      Inv M base 8192 C.p Sl (selected++V) (tmv C 4 base t) t ∧
      (1≤a→JPt base t selectedSlot (mul a P)) ∧
      (a=0→∀ i<5,wordsVal t.mem base (selectedSlot i) 4=0) ∧
      (∀ x∈V,wordsVal t.mem base x 4=wordsVal s.mem base x 4) :=
  selectBlock_field_ok hV hi hf ht ha (R := [.x17]) (by decide) (Select.scanStore_ok hi.scr ha hidx hinc hmag hz)

def signedEntry : List Instr :=
  Impl.P256.EcdhSelect.neon 2816 704 5400++negYW M 5 K.neg K.zero K.E.y K.bits

structure EntryPost (base : Addr) (P : Point C) (k j : Nat) (V : List Nat) (s t : State) : Prop where
  frame : Frame base work s t
  counter : t.gpr .x19=s.gpr .x19
  field : Inv M base 8192 C.p Sl (selected++V) (tmv C 4 base t) t
  zero : magH 16 (Window5.nib (k+offset) j)=0→tmv C 4 base t K.E.z=0
  cache2 : tmv C 4 base t 5400=tmv C 4 base t K.E.z*tmv C 4 base t K.E.z
  cache3 : tmv C 4 base t 5432=tmv C 4 base t 5400*tmv C 4 base t K.E.z
  same : ∀ x∈V,wordsVal t.mem base x 4=wordsVal s.mem base x 4
  point : 1≤magH 16 (Window5.nib (k+offset) j) →
    JPt base t selectedSlot (Window5.winPt C P (k+offset) j)

/-- A selection `c` of digit `j`'s entry, then its `y` negated for a
negative digit. -/
theorem signedBlock_ok {base : Addr} {P : Point C} {k j : Nat} {s : State}
    {V : List Nat} (hV : ∀ x∈V,x∈live) (hro : ∀ x∈ro,x∈V)
    (hf : Fixed base P k s) (hj : j<52)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j) {c : List Instr}
    (hc : WP isa (.block c) s fun t=>
      Frame base work s t ∧ t.gpr .x19=s.gpr .x19 ∧
      Inv M base 8192 C.p Sl (selected++V) (tmv C 4 base t) t ∧
      (1≤magH 16 (Window5.nib (k+offset) j)→JPt base t selectedSlot (mul (magH 16 (Window5.nib (k+offset) j)) P)) ∧
      (magH 16 (Window5.nib (k+offset) j)=0→∀ i<5,wordsVal t.mem base (selectedSlot i) 4=0) ∧
      (∀ x∈V,wordsVal t.mem base x 4=wordsVal s.mem base x 4)) :
    WP isa (.block (c++negYW M 5 K.neg K.zero K.E.y K.bits)) s (EntryPost base P k j V s) := by
  rw [WP.block_append_iff]
  refine WP.mono hc fun s₁ ⟨fr₁,c₁,i₁,p₁,z₁,same₁⟩=>?_
  obtain f₁ := hf.keep (frame_build fr₁)
  obtain hz : tmv C 4 base s₁ K.zero=0 := by unfold tmv; rw [f₁.zero,toM_zero]
  obtain hy : K.E.y∈selected++V := by apply List.mem_append_left; decide
  obtain hzero : K.zero∈selected++V := List.mem_append_right _ (hro _ (by decide))
  refine WP.mono (negFieldWindow_ok layout aligned (unitMod_pow_two (by decide) _) i₁
    (by decide : Sl K.neg) hzero hy (by decide) hz (by decide : 1≤5) (by decide)
    (by omega_arith : 5*j+5≤260) (by decide) (by decide) (c₁.trans h19) f₁.bits
    (by decide) (by decide)) fun t ⟨kp₂,i₂⟩=>?_
  obtain fr₂ : Frame base work s₁ t := AllocatedFrame.of_prog kp₂ clob_regs (by decide)
  obtain iv := i₂.sub (fun x (hx : x∈selected++V)=>List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
  obtain hez : tmv C 4 base t K.E.z=tmv C 4 base s₁ K.E.z := by
    have hh:=iv.val K.E.z (by apply List.mem_append_left; decide)
    change tmv C 4 base t K.E.z=_ at hh
    simpa only [Function.update_of_ne (by decide : K.E.z≠K.E.y),
      Function.update_of_ne (by decide : K.E.z≠K.neg)] using hh
  have he (i : Nat) (hi' : i<5) (hne : i≠1) :
      tmv C 4 base t (selectedSlot i)=tmv C 4 base s₁ (selectedSlot i) := by
    obtain hv := iv.val _ (List.mem_append_left _ (selected_mem i hi'))
    obtain ne : selectedSlot i≠K.E.y ∧ selectedSlot i≠K.neg := by
      obtain hh : ∀ i<5,i≠1→selectedSlot i≠K.E.y ∧ selectedSlot i≠K.neg := by decide
      exact hh i hi' hne
    change tmv C 4 base t (selectedSlot i)=_ at hv
    simpa only [Function.update_of_ne ne.1,Function.update_of_ne ne.2] using hv
  obtain hc2 : tmv C 4 base s₁ 5400=tmv C 4 base s₁ K.E.z*tmv C 4 base s₁ K.E.z := by
    by_cases hz : magH 16 (Window5.nib (k+offset) j)=0
    · have e2:=z₁ hz 2 (by decide)
      have e3:=z₁ hz 3 (by decide)
      change wordsVal s₁.mem base 768 4=0 at e2
      change wordsVal s₁.mem base 5400 4=0 at e3
      change toM _ _ (wordsVal s₁.mem base 5400 4)=toM _ _ (wordsVal s₁.mem base 768 4)*toM _ _ (wordsVal s₁.mem base 768 4)
      rw [e2,e3,toM_zero]; grind
    · exact (p₁ (by omega_arith)).z2
  obtain hc3 : tmv C 4 base s₁ 5432=tmv C 4 base s₁ 5400*tmv C 4 base s₁ K.E.z := by
    by_cases hz : magH 16 (Window5.nib (k+offset) j)=0
    · have e4:=z₁ hz 4 (by decide)
      have e3:=z₁ hz 3 (by decide)
      change wordsVal s₁.mem base 5432 4=0 at e4
      change wordsVal s₁.mem base 5400 4=0 at e3
      unfold tmv
      rw [e4,e3,toM_zero]; grind
    · exact (p₁ (by omega_arith)).z3
  refine ⟨fr₁.trans fr₂,(kp₂.gpr _ (x19_not_clob _)).trans c₁,iv.to_tmv,fun hz=>?_,?_,?_,?_,fun hnz=>?_⟩
  · rw [hez]; unfold tmv; rw [show wordsVal s₁.mem base K.E.z 4=0 from z₁ hz 2 (by decide),toM_zero]
  · change tmv C 4 base t (selectedSlot 3)=tmv C 4 base t (selectedSlot 2)*tmv C 4 base t (selectedSlot 2)
    rw [he 3 (by decide) (by decide),he 2 (by decide) (by decide)]; exact hc2
  · change tmv C 4 base t (selectedSlot 4)=tmv C 4 base t (selectedSlot 3)*tmv C 4 base t (selectedSlot 2)
    rw [he 4 (by decide) (by decide),he 3 (by decide) (by decide),he 2 (by decide) (by decide)]; exact hc3
  · intro x hx
    rw [kp₂.unch.wordsVal (by
      obtain hh : ∀ x∈live,∀ w∈([K.neg,K.E.y].map (·,8*M.n)++[(M.tmp,8*M.n)]),x+32≤w.1 ∨ w.1+w.2≤x := by decide
      exact hh x (hV x hx)) (by
      obtain hh : ∀ x∈live,x+32≤2^64 := by decide
      exact hh x (hV x hx))]
    exact same₁ x hx
  obtain p := p₁ hnz
  obtain hey : tmv C 4 base t (selectedSlot 1)=
      if decide (Window5.nib (k+offset) j<16) then -tmv C 4 base s₁ (selectedSlot 1)
      else tmv C 4 base s₁ (selectedSlot 1) := by
    obtain hv := iv.val _ (List.mem_append_left _ (selected_mem 1 (by decide)))
    change tmv C 4 base t (selectedSlot 1)=_ at hv
    simpa only [show selectedSlot 1=K.E.y from rfl,Function.update_self,Window5.combWin_five,
      show 2^(5-1)=16 from rfl] using hv
  refine ⟨fun i hi'=>iv.lt _ (List.mem_append_left _ (selected_mem i hi')),?_,?_,?_,?_⟩
  · rw [he 0 (by decide) (by decide),hey,he 2 (by decide) (by decide),Window5.winPt_mag]
    split
    · exact p.jac.negY
    · exact p.jac
  · rw [he 2 (by decide) (by decide)]; exact p.z
  · rw [he 3 (by decide) (by decide),he 2 (by decide) (by decide)]; exact p.z2
  · rw [he 4 (by decide) (by decide),he 3 (by decide) (by decide),he 2 (by decide) (by decide)]; exact p.z3

theorem signedEntry_ok {base : Addr} {P : Point C} {k j : Nat} {s : State}
    {V : List Nat} (hV : ∀ x∈V,x∈live) (hro : ∀ x∈ro,x∈V)
    (hi : Inv M base 8192 C.p Sl V (tmv C 4 base s) s)
    (hf : Fixed base P k s) (ht : TblOk base P 16 s) (hj : j<52)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j)
    (hmag : s.gpr .x2=BitVec.ofNat 64 (magH 16 (Window5.nib (k+offset) j))) :
    WP isa (.block signedEntry) s (EntryPost base P k j V s) :=
  signedBlock_ok hV hro hf hj h19
    (select_field_ok hV hi hf ht (magH_le (Nat.mod_lt _ (by decide))) hmag)

/-- `signedEntry` but its setup, from the setup's broadcasts. -/
theorem signedEntryV_ok {base : Addr} {P : Point C} {k j : Nat} {s : State}
    {V : List Nat} (hV : ∀ x∈V,x∈live) (hro : ∀ x∈ro,x∈V)
    (hi : Inv M base 8192 C.p Sl V (tmv C 4 base s) s)
    (hf : Fixed base P k s) (ht : TblOk base P 16 s) (hj : j<52)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j)
    (hidx : s.v .v28=dup2 0) (hinc : s.v .v31=dup2 1)
    (hmag : s.v .v30=dup2 (BitVec.ofNat 64 (magH 16 (Window5.nib (k+offset) j))))
    (hz : ∀ i<10,s.v (Select.acc i)=0) :
    WP isa (.block (Select.scan 2816 16++Select.store++negYW M 5 K.neg K.zero K.E.y K.bits)) s
      (EntryPost base P k j V s) :=
  signedBlock_ok hV hro hf hj h19
    (selectV_field_ok hV hi hf ht (magH_le (Nat.mod_lt _ (by decide))) hidx hinc hmag hz)

def entry : List Instr := tc.digit++signedEntry

theorem entry_ok {base : Addr} {P : Point C} {k j : Nat} {s : State}
    {V : List Nat} (hV : ∀ x∈V,x∈live) (hro : ∀ x∈ro,x∈V)
    (hi : Inv M base 8192 C.p Sl V (tmv C 4 base s) s)
    (hf : Fixed base P k s) (ht : TblOk base P 16 s) (hj : j<52)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (.block entry) s (EntryPost base P k j V s) := by
  rw [entry,WP.block_append_iff]
  refine WP.mono (digitW_ok tc hi.scr (k:=k+offset) (j:=j) (N:=260)
    (by decide) (by decide) (by change 5*j+5≤260; omega_arith) (by decide) (by decide) h19 hf.bits)
    fun u ⟨hu,hkeep⟩=>?_
  obtain fr : Frame base work s u := (AllocatedFrame.of_keeps hkeep).widenRegs (by decide)
  obtain iu : Inv M base 8192 C.p Sl V (tmv C 4 base u) u := by
    have hh:=hi.of_keeps hkeep (by decide)
    obtain he : tmv C 4 base u=tmv C 4 base s := by funext x; unfold tmv; rw [hkeep.mem]
    rw [he]; exact hh
  refine WP.mono (signedEntry_ok hV hro iu (hf.keep (frame_build fr)) (ht.keep fr) hj
    ((hkeep.gpr _ (by decide)).trans h19) (by
      change u.gpr .x2=BitVec.ofNat 64 (magH 16 (combWin 5 (k+offset) j)) at hu
      simpa only [Window5.combWin_five] using hu)) fun t hp=>?_
  refine ⟨fr.trans hp.frame,hp.counter.trans (hkeep.gpr _ (by decide)),hp.field,hp.zero,hp.cache2,hp.cache3,?_,hp.point⟩
  intro x hx
  rw [hp.same x hx,hkeep.mem]

end VG.Proof.P256.EcdhJac

end

/-! ## `First` -/

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

theorem first_split : Impl.P256.EcdhJac.first=
    ([.movz .x .x19 51 0] : List Instr)++entry++copyPt 4 K.R K.E := by
  simp only [Impl.P256.EcdhJac.first,entry,signedEntry,Impl.P256.EcdhJac.select,List.append_assoc,
    show Impl.P256.EcdhJac.K.tbl=2816 from rfl,show Impl.P256.EcdhJac.K.E.x=704 from rfl,
    show Impl.P256.EcdhJac.z2=5400 from rfl]

theorem first_ok (hC : Law C) {base : Addr} {P : Point C} {k : Nat} {s : State}
    (hP : onCurve C P=true) (hk : k<2^256) (hf : Fixed base P k s) (ht : TblOk base P 16 s) :
    WP isa (.block Impl.P256.EcdhJac.first) s fun t=>Frame base work s t ∧ LoopInv base P k 51 t := by
  rw [first_split,WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (movz_ok s .x19 51) fun u ⟨hu,ku⟩=>?_
  obtain fu : Frame base work s u := (AllocatedFrame.of_keeps ku).widenRegs (by decide)
  obtain hfu := hf.keep (frame_build fu)
  refine WP.mono (entry_ok (V:=ro) (j:=51) (by intro x hx; exact List.mem_append_right _ hx)
    (fun _ h=>h) hfu.field hfu (ht.keep fu) (by decide) (by exact hu)) fun v hv=>?_
  obtain hepoint : InvJ C (tmv C 4 base v K.E.x) (tmv C 4 base v K.E.y)
      (tmv C 4 base v K.E.z) (Window5.winPt C P (k+offset) 51) := by
    by_cases hz : magH 16 (Window5.nib (k+offset) 51)=0
    · rw [Window5.winPt_zero hz]
      exact Or.inl ⟨rfl,hv.zero hz⟩
    · exact (hv.point (by omega_arith)).jac
  obtain hA : RcbApart K.S K.E K.E K.R := ⟨by decide,by decide⟩
  obtain hsl : ∀ x∈rcbW K.S K.R++rcbR K.S K.E K.E,Sl x := by decide
  obtain hvalid : ∀ x∈rcbR K.S K.E K.E,x∈selected++ro := by decide
  refine WP.mono (copyPoint_ok layout aligned hA hsl hv.field hvalid) fun t ⟨et,kp,it,ep⟩=>?_
  obtain ft : Frame base work v t := AllocatedFrame.of_prog kp clob_regs (by decide)
  obtain allframe := fu.trans (hv.frame.trans ft)
  obtain iout := it.sub (fun x (hx : x∈live)=>by
    rcases List.mem_append.mp hx with hx|hx
    · exact List.mem_append_left _ hx
    · exact List.mem_append_right _ (List.mem_append_right _ hx))
  obtain exyz : et K.R.x=tmv C 4 base v K.E.x ∧ et K.R.y=tmv C 4 base v K.E.y ∧
      et K.R.z=tmv C 4 base v K.E.z := by simpa only [Prod.mk.injEq] using ep
  obtain ip : InvJ C (et K.R.x) (et K.R.y) (et K.R.z) (Window5.winPt C P (k+offset) 51) := by
    rw [exyz.1,exyz.2.1,exyz.2.2]; exact hepoint
  refine ⟨allframe,⟨⟨Window5.winPt C P (k+offset) 51,Window5.onCurve_winPt hC hP (k+offset) 51,fun _=>?_,
    ⟨hf.keep (frame_build allframe),ht.keep allframe,iout.to_tmv,?_⟩⟩,?_⟩⟩
  · have he := Window5.win_add hC hP (k:=k+offset) (J:=52) (j:=51)
      (by rw [offset_eq]; omega_arith) (by decide)
    obtain htop : Window5.winE (k+offset) 52 52=0 :=
      Window5.winE_top (by rw [offset_eq]; exact Window5.recode_lt hk)
    rw [show 51+1=52 from rfl,htop,Nat.mul_zero,Window5.mul_zero_pt,infinity_add'] at he
    exact he
  · have vals : ∀ x∈live,tmv C 4 base t x=et x := by
      intro x hx
      exact iout.val x hx
    change InvJ C (tmv C 4 base t K.R.x) (tmv C 4 base t K.R.y) (tmv C 4 base t K.R.z) _
    rw [vals K.R.x (by decide),vals K.R.y (by decide),vals K.R.z (by decide)]
    exact ip
  · rw [kp.gpr _ (x19_not_clob _),hv.counter,hu]
    rfl

end VG.Proof.P256.EcdhJac

end

end

end

/-! ### `Weierstrass.WinJacPoint`, which only this module used -/

section

/-! Architecture-independent masked Jacobian window arithmetic, including invalid scalars. -/

@[expose] public section

namespace VG.Proof.Weierstrass.Window5
open VG Spec.Weierstrass
variable {C : Curve}

/-- The iteration's result: `R` for a zero digit, else `T` where `R = O`, else
the Jacobian sum, a triple of `[winE k' J i]P`. -/
theorem jstep_point (hC : Law C) (hM3 : AM3 C) (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true)
    (hP0 : P ≠ .infinity) (hn17 : 17 ≤ C.n % 32) (hn64 : 64 ≤ C.n) {k J i : Nat} (hk : k < C.n)
    (hi : i < J) {X1 Y1 Z1 X2 Y2 Z2 : Fe C}
    (h1 : InvJ C X1 Y1 Z1 (mul (32 * Window5.winE (k + 16 * Window5.geom J) J (i + 1)) P))
    (h2 : 1 ≤ magH 16 (Window5.nib (k + 16 * Window5.geom J) i) →
      InvJ C X2 Y2 Z2 (Window5.winPt C P (k + 16 * Window5.geom J) i) ∧ Z2 ≠ 0) :
    InvJ C
      (if magH 16 (Window5.nib (k + 16 * Window5.geom J) i) = 0 then X1
        else if Z1 = 0 then X2 else (jacAddF X1 Y1 Z1 X2 Y2 Z2).1)
      (if magH 16 (Window5.nib (k + 16 * Window5.geom J) i) = 0 then Y1
        else if Z1 = 0 then Y2 else (jacAddF X1 Y1 Z1 X2 Y2 Z2).2.1)
      (if magH 16 (Window5.nib (k + 16 * Window5.geom J) i) = 0 then Z1
        else if Z1 = 0 then Z2 else (jacAddF X1 Y1 Z1 X2 Y2 Z2).2.2)
      (mul (Window5.winE (k + 16 * Window5.geom J) J i) P) := by
  obtain hadd := Window5.win_add hC hP (k := k + 16 * Window5.geom J) (J := J) (j := i) (Nat.le_add_left _ _) hi
  generalize hk' : k + 16 * Window5.geom J = k' at hadd h1 h2 ⊢
  generalize he : Window5.winE k' J (i + 1) = e at hadd h1
  rw [← hadd]
  by_cases h0 : magH 16 (Window5.nib k' i) = 0
  · simp only [h0, ↓reduceIte]
    rw [Window5.winPt_zero h0, add_infinity]
    exact h1
  · simp only [h0, ↓reduceIte]
    obtain ⟨J2, z2⟩ := h2 (by omega_using [h0])
    obtain hQ := hC.onCurve_mul hP (32 * e)
    obtain hW : onCurve C (Window5.winPt C P k' i) = true := Window5.onCurve_winPt hC hP k' i
    by_cases hz : Z1 = 0
    · simp only [hz, ↓reduceIte]
      rw [(h1.z_zero_iff hC).mp hz, infinity_add']
      exact J2
    · simp only [hz, ↓reduceIte]
      obtain he1 : 1 ≤ e := by
        rcases Nat.eq_zero_or_pos e with rfl | h
        · exact absurd ((h1.z_zero_iff hC).mpr (by rw [Nat.mul_zero, Window5.mul_zero_pt])) hz
        · exact h
      rw [← he, ← hk'] at he1
      obtain ⟨ne1, ne2⟩ := Window5.loop_noexc hC hO hP hP0 hn17 hn64 hk hi he1
      rw [hk', he] at ne1 ne2
      obtain hh : X2 * (Z1 * Z1) - X1 * (Z2 * Z2) ≠ 0 := by
        intro hx
        by_cases hy : Y2 * Z1 * (Z1 * Z1) - Y1 * Z2 * (Z2 * Z2) = 0
        · exact ne1 (h1.same hC J2 hz z2 hx hy)
        · exact ne2 (h1.opposite hC hQ hW J2 hz z2 hx hy)
      exact h1.add_ne hC hM3 hQ hW J2 hz z2 hh

/-- The iteration's result for any `k`: a triple of a point of the curve, which
is `[winE k' J i]P` for `k < n` (`jstep_point`). Beyond `n` an addition may be
exceptional: then `Z = 0`, a triple of `O`. -/
theorem jstep_pt (hC : Law C) (hM3 : AM3 C) (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true)
    (hP0 : P ≠ .infinity) (hn17 : 17 ≤ C.n % 32) (hn64 : 64 ≤ C.n) {k J i : Nat}
    (hi : i < J) {X1 Y1 Z1 X2 Y2 Z2 : Fe C} {Q1 : Point C} (hQ1 : onCurve C Q1 = true)
    (hQ1e : k < C.n → Q1 = mul (32 * Window5.winE (k + 16 * Window5.geom J) J (i + 1)) P)
    (h1 : InvJ C X1 Y1 Z1 Q1)
    (h2 : 1 ≤ magH 16 (Window5.nib (k + 16 * Window5.geom J) i) →
      InvJ C X2 Y2 Z2 (Window5.winPt C P (k + 16 * Window5.geom J) i) ∧ Z2 ≠ 0) :
    ∃ Q : Point C, onCurve C Q = true ∧ (k < C.n → Q = mul (Window5.winE (k + 16 * Window5.geom J) J i) P) ∧
      InvJ C
        (if magH 16 (Window5.nib (k + 16 * Window5.geom J) i) = 0 then X1
          else if Z1 = 0 then X2 else (jacAddF X1 Y1 Z1 X2 Y2 Z2).1)
        (if magH 16 (Window5.nib (k + 16 * Window5.geom J) i) = 0 then Y1
          else if Z1 = 0 then Y2 else (jacAddF X1 Y1 Z1 X2 Y2 Z2).2.1)
        (if magH 16 (Window5.nib (k + 16 * Window5.geom J) i) = 0 then Z1
          else if Z1 = 0 then Z2 else (jacAddF X1 Y1 Z1 X2 Y2 Z2).2.2) Q := by
  by_cases hk : k < C.n
  · refine ⟨_, hC.onCurve_mul hP _, fun _ => rfl, ?_⟩
    rw [hQ1e hk] at h1
    exact jstep_point hC hM3 hO hP hP0 hn17 hn64 hk hi h1 h2
  obtain nk : ∀ Q : Point C, k < C.n → Q = mul (Window5.winE (k + 16 * Window5.geom J) J i) P :=
    fun _ h' => absurd h' hk
  generalize k + 16 * Window5.geom J = k' at h2 nk ⊢
  by_cases h0 : magH 16 (Window5.nib k' i) = 0
  · simp only [h0, ↓reduceIte]
    exact ⟨Q1, hQ1, nk _, h1⟩
  · simp only [h0, ↓reduceIte]
    obtain ⟨J2, z2⟩ := h2 (by omega_using [h0])
    obtain hW : onCurve C (Window5.winPt C P k' i) = true := Window5.onCurve_winPt hC hP k' i
    by_cases hz : Z1 = 0
    · simp only [hz, ↓reduceIte]
      exact ⟨_, hW, nk _, J2⟩
    · simp only [hz, ↓reduceIte]
      by_cases hh : X2 * (Z1 * Z1) - X1 * (Z2 * Z2) = 0
      · refine ⟨.infinity, rfl, nk _, Or.inl ⟨rfl, ?_⟩⟩
        show Z1 * Z2 * (X2 * (Z1 * Z1) - X1 * (Z2 * Z2)) = 0
        rw [hh]; grind
      · exact ⟨_, hC.onCurve_add hQ1 hW, nk _, h1.add_ne hC hM3 hQ1 hW J2 hz z2 hh⟩


end VG.Proof.Weierstrass.Window5

end

end


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
  obtain hi' : Inv M base 8192 C.p Ecdsa.Verify.AArch64.Allocated.Sl V E s :=
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
  obtain hs : Sl x := by
    rcases (mem_validAfter _ _).mp hx with hv|hv
    · exact hi.sl x hv
    · obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hv
      exact hslots op hop op.out (by simp)
  obtain hb := (show ∀ x,Sl x → x+32≤5464 from by decide +kernel) x hs
  exact ⟨Or.inl hk,Or.inl (by omega_using [hi4, hb])⟩

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
  obtain hr := readsOk_mono CachedField.reads_full hv
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
  obtain hp : ∀x∈live,tmv C 4 base t x=tmv C 4 base s x := by
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
  obtain same : ∀x∈selected++live,tmv C 4 base t x=tmv C 4 base s x := by
    intro x hx
    obtain hv := it.val x (List.mem_append_right _ hx)
    change tmv C 4 base t x=_ at hv
    rw [hv]
    apply runOps_of_not_out
    obtain hn : ∀op∈CachedField.head++CachedField.tail,∀x∈selected++live,op.out≠x := by decide
    exact fun op hop => hn op hop x hx
  obtain state : RState base P Q k t := by
    refine ⟨hs.fixed.keep (frame_build (kt.widenRegs allocated_regs)),
      hs.table.keep (kt.widenRegs allocated_regs),it.to_tmv.sub (by decide),?_⟩
    rw [same _ (by decide),same _ (by decide),same _ (by decide)]
    exact hs.point
  refine ⟨kt,state,it.to_tmv,same,?_⟩
  obtain vx := it.val K.D.x (by decide)
  obtain vy := it.val K.D.y (by decide)
  obtain vz := it.val K.D.z (by decide)
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
  obtain fa : Frame base work s a := (AllocatedFrame.of_keeps ka).widenRegs (by decide)
  obtain ca := hs.of_keeps ka (by decide)
  let I := fun q t => Frame base work s t ∧ RState base P (mul (2^(4-q)) Q) k t ∧
    t.gpr .x19=BitVec.ofNat 64 (2048*q+j)
  apply countRegLoop_ok .x4 (Inv:=I) (n:=4) (by decide)
  · intro q b hq hq5 hi
    obtain ⟨fb,cb,b19⟩ := hi
    unfold Impl.P256.EcdhJac.dblStep
    apply WP.seq
    refine WP.mono (double_state hC ha (hC.onCurve_mul hQ _) cb) fun d ⟨fd,cd⟩ => ?_
    obtain d19 := (fd.regs.gpr .x19 allocatedRegs_x19).trans b19
    refine WP.mono (doubleCounter_ok d hq (by omega_using [hq5]) hj d19) fun t ⟨t19,t4,kt⟩ => ?_
    obtain ft : Frame base work d t := (AllocatedFrame.of_keeps kt).widenRegs (by decide)
    obtain ct := cd.of_keeps kt (by decide)
    obtain ep : add (mul (2^(4-q)) Q) (mul (2^(4-q)) Q)=mul (2^(4-(q-1))) Q := by
      rw [hC.add_mul_mul hQ,show 4-(q-1)=(4-q)+1 by omega_using [hq, hq5],Nat.pow_succ]
      congr 1
      omega_using []
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
  obtain hq' : k<C.n→Q=mul (32*Window5.winE (k+16*Window5.geom 52) 52 (j+1)) P := by
    simpa only [offset_eq] using hq
  obtain he' : 1≤magH 16 (Window5.nib (k+16*Window5.geom 52) j)→
      InvJ C (tmv C 4 base s K.E.x) (tmv C 4 base s K.E.y) (tmv C 4 base s K.E.z)
        (Window5.winPt C P (k+16*Window5.geom 52) j) ∧ tmv C 4 base s K.E.z≠0 := by
    simpa only [digitMagnitude,offset_eq] using he
  obtain ⟨Q',hQ',hq',hj'⟩ := Window5.jstep_pt hC ha hO hP (hs.fixed.peer_ne hC)
    (by decide) (by decide) hj hQ hq' hs.point he'
  rw [←offset_eq] at hq' hj'
  refine WP.mono (masks_ok hs.fixed hj h19) fun t ⟨kt,hv⟩ => ?_
  obtain fw := kt.widenRegs allocated_regs
  obtain fixed := hs.fixed.keep (frame_build fw)
  obtain hziff : wordsVal s.mem base 576 4=0 ↔ tmv C 4 base s 576=0 :=
    (toM_eq_zero_iff (unitMod_pow_two (by decide) _) (hi.lt _ (by decide))).symm
  obtain values : ∀ i<3,tmv C 4 base t (512+32*i)=
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
  obtain ilt : ∀ x∈live,wordsVal t.mem base x 4<C.p := by
    intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · have hh : ∀ x∈[K.R.x,K.R.y,K.R.z],∃ i<3,x=512+32*i := by decide
      obtain ⟨i,hi',rfl⟩ := hh x hx
      rw [hv i hi']
      split
      · exact hi.lt _ (by
          obtain hh : ∀ i<3,512+32*i∈addLive := by decide
          exact hh i hi')
      · split
        · exact hi.lt _ (by
            obtain hh : ∀ i<3,704+32*i∈addLive := by decide
            exact hh i hi')
        · exact hi.lt _ (by
            obtain hh : ∀ i<3,608+32*i∈addLive := by decide
            exact hh i hi')
    · exact fixed.field.lt x hx
  obtain it : Inv M base 8192 C.p Sl live (tmv C 4 base t) t :=
    ⟨fixed.field.scr,fixed.field.mod,by decide,ilt,fun _ _ => rfl⟩
  refine ⟨fw,⟨⟨Q',hQ',hq',fixed,hs.table.keep fw,it,?_⟩,
    (kt.regs.gpr _ allocatedRegs_x19).trans h19⟩⟩
  obtain v0 := values 0 (by decide)
  obtain v1 := values 1 (by decide)
  obtain v2 := values 2 (by decide)
  change tmv C 4 base t K.R.x=_ at v0
  change tmv C 4 base t K.R.y=_ at v1
  change tmv C 4 base t K.R.z=_ at v2
  rw [v0,v1,v2]
  obtain dx := congrArg Prod.fst hd
  obtain dy := congrArg (fun p => p.2.1) hd
  obtain dz := congrArg (fun p => p.2.2) hd
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
      obtain fr := Interleave.frame hf he
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
  refine WP.mono (decCounter_ok s hj (by omega_using [hj52]) s19) fun a ⟨a19,ka⟩ => ?_
  obtain fa : Frame base work s a := (AllocatedFrame.of_keeps ka).widenRegs (by decide)
  obtain ra := rs.of_keeps ka (by decide)
  apply WP.seq
  refine WP.mono (doubles_ok hC ha hQ (by omega_using [hj52]) ra a19) fun b ⟨fb,rb,b19⟩ => ?_
  obtain qb : k<C.n → mul 32 Q=mul (32*Window5.winE (k+offset) 52 ((j-1)+1)) P := by
    intro hk
    rw [hq hk,Window5.mul_mul hC hP,show j-1+1=j by omega_using [hj]]
  apply WP.seq
  -- The digit, the selection's setup, the fifth doubling with the selection's
  -- rows, the store and the negation.
  rw [step_split,WP.block_append_iff]
  refine WP.mono (digitW_ok tc rb.field.scr (k:=k+offset) (j:=j-1) (N:=260)
    (by decide) (by decide) (by change 5*(j-1)+5≤260; omega_using [hj52]) (by decide) (by decide) b19 rb.fixed.bits)
    fun u ⟨hu,ku⟩=>?_
  obtain fu : Frame base work b u := (AllocatedFrame.of_keeps ku).widenRegs (by decide)
  obtain ru := rb.of_keeps ku (by decide)
  obtain hmag : u.gpr .x2=BitVec.ofNat 64 (magH 16 (Window5.nib (k+offset) (j-1))) := by
    change u.gpr .x2=BitVec.ofNat 64 (magH 16 (combWin 5 (k+offset) (j-1))) at hu
    simpa only [Window5.combWin_five] using hu
  rw [WP.block_append_iff]
  refine WP.mono (Select.setup_ok u) fun s₁ ⟨idx₁,inc₁,mag₁,z₁,k₁⟩=>?_
  obtain f₁ : Frame base work u s₁ := (AllocatedFrame.of_keeps k₁.keeps).widenRegs (by decide)
  obtain r₁ := ru.of_keeps k₁.keeps (by decide)
  rw [WP.block_append_iff]
  refine Interleave.WP.weave doubleSel_indeps ?_
  obtain h16 : onCurve C (mul 16 Q)=true := hC.onCurve_mul hQ _
  refine WP.mono (double_stateV hC ha h16 r₁) fun s₂ ⟨fd,r₂,v₂⟩=>?_
  obtain e32 : add (mul 16 Q) (mul 16 Q)=mul 32 Q := by
    rw [hC.add_mul_mul hQ]
  rw [e32] at r₂
  obtain f₂ : Frame base work s₁ s₂ := fd.widenRegs allocated_regs
  obtain s₂19 : s₂.gpr .x19=BitVec.ofNat 64 (j-1) := by
    rw [fd.regs.gpr _ allocatedRegs_x19,k₁.gpr _ (by decide),ku.gpr _ (by decide),b19]
  rw [← WP.block_append_iff,← List.append_assoc]
  refine WP.mono (signedEntryV_ok (fun _ h => h) (by decide) r₂.field r₂.fixed r₂.table (by omega_using [hj52]) s₂19
    (by rw [v₂]; exact idx₁) (by rw [v₂]; exact inc₁)
    (by rw [v₂,mag₁,hmag]) (fun i hi=>by rw [v₂]; exact z₁ i hi)) fun e he => ?_
  obtain re := he.rstate r₂
  obtain e19 := he.counter.trans s₂19
  apply WP.seq
  refine WP.mono (add_state re he.field he.cache2 (by
    rw [he.cache3,he.cache2]; exact Lean.Grind.CommSemiring.mul_comm _ _)) fun d hd => ?_
  obtain d19 := (hd.frame.regs.gpr _ allocatedRegs_x19).trans e19
  obtain ep : 1≤digitMagnitude k (j-1) →
      InvJ C (tmv C 4 base d K.E.x) (tmv C 4 base d K.E.y) (tmv C 4 base d K.E.z)
        (Window5.winPt C P (k+offset) (j-1)) ∧ tmv C 4 base d K.E.z≠0 := by
    intro hn
    obtain hp := he.point hn
    rw [hd.same _ (by decide),hd.same _ (by decide),hd.same _ (by decide)]
    exact ⟨hp.jac,hp.z⟩
  refine WP.mono (masked_ok hC ha hO hP (hC.onCurve_mul hQ _) qb hd.state
    (by omega_using [hj52]) d19 hd.field ep hd.point) fun t ⟨ft,ht⟩ => ?_
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
