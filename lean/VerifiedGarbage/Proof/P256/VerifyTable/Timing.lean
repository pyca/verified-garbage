module

public import VerifiedGarbage.Proof.P256.VerifyTable.Build
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.P256.EcdhJac.Masks
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
import VerifiedGarbage.Proof.Weierstrass.CombLay
meta import VerifiedGarbage.Proof.P256.VerifyTable.Build
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.P256.EcdhJac.Masks
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
meta import VerifiedGarbage.Proof.Weierstrass.CombLay

/-! The co-Z table's timing: its addresses and loop depend on the scratch
pointer alone, so runs from field environments that agree keep them
agreeing. -/

@[expose] public section

namespace VG.Proof.P256.VerifyTable
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (read_x)

theorem start_ct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
    (.block Impl.P256.VerifyTable.start) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0]) (fun _ _ _ _ h => h) (by taint_decide)

theorem swap_ct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
    (.block Impl.P256.VerifyTable.swap) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0]) (fun _ _ _ _ h => h) (by taint_decide)

theorem finish_ct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
    (.block Impl.P256.VerifyTable.finish) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0]) (fun _ _ _ _ h => h) (by taint_decide)

theorem inc_ct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
    (.block [.addImm .x .x19 .x19 1]) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0]) (fun _ _ _ _ h => h) (by taint_decide)

theorem store_ct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19]))
    (.block (Impl.P256.VerifyTable.storeEntry ++ ([.subImm .x .x4 .x19 8] : List Instr))) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0,.x19]) (fun _ _ _ _ h => h) (by taint_decide)

/-- A phase whose public registers are determined by its precondition. -/
theorem phase_relCT {c : Prog isa} {τ : VG.AArch64.Taint.T} {A B : State → Prop}
    (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree τ) c)
    (hw : ∀ s,A s → WP isa c s fun t => B t ∧ t.sp=s.sp)
    (hp : ∀ s t,A s → A t → s.sp=t.sp → AArch64.Taint.Agree τ s t) :
    RelCT isa (fun s t => A s ∧ A t ∧ s.sp=t.sp) c (fun s t => B s ∧ B t ∧ s.sp=t.sp) := by
  intro s t ts tt s' t' ⟨as,at',sp⟩ es et
  obtain ⟨_,_,xs,bs,ks⟩ := hw s as
  obtain ⟨_,_,xt,bt,kt⟩ := hw t at'
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  exact ⟨hct _ _ _ _ _ _ trivial trivial (hp s t as at' sp) es et,bs,bt,ks.trans (sp.trans kt.symm)⟩

theorem agree0 {base : Addr} {s t : State} (hs : Scr s base 8192) (ht : Scr t base 8192)
    (sp : s.sp=t.sp) : AArch64.Taint.Agree (Taint.ofRegs [.x0]) s t := by
  refine ⟨sp,fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs,List.mem_singleton] at hr
  subst hr
  exact hs.x0.trans ht.x0.symm

theorem agree19 {base : Addr} {s t : State} (hs : Scr s base 8192) (ht : Scr t base 8192)
    (sp : s.sp=t.sp) (h19 : s.gpr .x19=t.gpr .x19) :
    AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19]) s t := by
  refine ⟨sp,fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact hs.x0.trans ht.x0.symm
  · exact h19

section
variable {Sl : Nat → Prop} (layout : Lay M 8192 Sl) (aligned : Aligned M Sl)
  (hs : ∀ x∈buildSlots,Sl x)
include layout aligned hs

theorem loop_relCT {base : Addr} {F : Nat → Fe C} :
    RelCT isa (fun s t =>
        (Inv M base 8192 C.p Sl (Vl 0) F s ∧ s.gpr .x19=BitVec.ofNat 64 1) ∧
        (Inv M base 8192 C.p Sl (Vl 0) F t ∧ t.gpr .x19=BitVec.ofNat 64 1) ∧ s.sp=t.sp)
      (.loop Impl.P256.VerifyTable.step (.nonzero .x .x4))
      (fun s t => Inv M base 8192 C.p Sl (Vl 7) (loopEnv 7 F) s ∧
        Inv M base 8192 C.p Sl (Vl 7) (loopEnv 7 F) t ∧ s.sp=t.sp) := by
  let Ph (n : Nat) (s : State) : Prop :=
    Inv M base 8192 C.p Sl (Vl (6-n)) (loopEnv (6-n) F) s ∧ s.gpr .x19=BitVec.ofNat 64 (7-n)
  let I (n : Nat) (s t : State) : Prop := n≤6 ∧ Ph n s ∧ Ph n t ∧ s.sp=t.sp
  have step (n : Nat) : RelCT isa (I n) Impl.P256.VerifyTable.step fun s t =>
      isa.eval (.nonzero .x .x4) s=isa.eval (.nonzero .x .x4) t ∧
      (isa.eval (.nonzero .x .x4) s=some false →
        Inv M base 8192 C.p Sl (Vl 7) (loopEnv 7 F) s ∧
        Inv M base 8192 C.p Sl (Vl 7) (loopEnv 7 F) t ∧ s.sp=t.sp) ∧
      (isa.eval (.nonzero .x .x4) s=some true → ∃ m<n,I m s t) := by
    by_cases hn : n≤6
    swap
    · exact RelCT.of_false fun _ _ h => hn h.1
    let k := 6-n
    have hk : k≤6 := by omega
    let A1 (s : State) : Prop :=
      Inv M base 8192 C.p Sl (Vl k) (loopEnv k F) s ∧ s.gpr .x19=BitVec.ofNat 64 (k+2)
    let A2 (s : State) : Prop :=
      Inv M base 8192 C.p Sl (Vl k) (runOps (ops false) (loopEnv k F)) s ∧
        s.gpr .x19=BitVec.ofNat 64 (k+2)
    let A3 (s : State) : Prop :=
      Inv M base 8192 C.p Sl (Vl (k+1)) (stepEnv (k+2) (loopEnv k F)) s ∧
        s.gpr .x19=BitVec.ofNat 64 (k+2) ∧ s.gpr .x4=BitVec.ofNat 64 (k+2)-8
    have r1 : RelCT isa (fun s t => Ph n s ∧ Ph n t ∧ s.sp=t.sp) (.block [.addImm .x .x19 .x19 1])
        (fun s t => A1 s ∧ A1 t ∧ s.sp=t.sp) := by
      refine phase_relCT inc_ct (fun s ⟨is,cs⟩ => ?_) (fun s t a b sp => agree0 a.1.scr b.1.scr sp)
      refine WP.mono (Proof.P256.EcdhJac.buildIncrement_ok s (m:=k+1) (by rw [cs]; congr 1; omega))
        fun t ⟨ct,kt⟩ => ⟨⟨is.of_keeps kt (by decide),ct⟩,kt.sp⟩
    have r2 : RelCT isa (fun s t => A1 s ∧ A1 t ∧ s.sp=t.sp) (Impl.P256.EcdhTable.program false)
        (fun s t => A2 s ∧ A2 t ∧ s.sp=t.sp) := by
      refine phase_relCT (Proof.P256.EcdhTable.Zaddu.ct) (fun s ⟨is,cs⟩ => ?_)
        (fun s t a b sp => agree0 a.1.scr b.1.scr sp)
      exact WP.mono (zaddu_ok layout aligned hs hk is) fun t ⟨kt,ct,it⟩ =>
        ⟨⟨it,ct.trans cs⟩,kt.regs.sp⟩
    have r3 : RelCT isa (fun s t => A2 s ∧ A2 t ∧ s.sp=t.sp)
        (.block (Impl.P256.VerifyTable.storeEntry ++ ([.subImm .x .x4 .x19 8] : List Instr)))
        (fun s t => A3 s ∧ A3 t ∧ s.sp=t.sp) := by
      refine phase_relCT store_ct (fun s ⟨is,cs⟩ => ?_)
        (fun s t a b sp => agree19 a.1.scr b.1.scr sp (a.2.trans b.2.symm))
      exact WP.mono (store_ok layout hs hk is cs) fun t ⟨kt,ct,xt,it⟩ => ⟨⟨it,ct,xt⟩,kt.regs.sp⟩
    have whole := RelCT.seq r1 (RelCT.seq r2 r3)
    refine (whole.mono (fun s t ⟨_,ps,pt,sp⟩ => ⟨ps,pt,sp⟩) fun s t ⟨⟨is,cs,xs⟩,⟨it,ct,xt⟩,sp⟩ => ?_)
    have hz (u : State) (xu : u.gpr .x4=BitVec.ofNat 64 (k+2)-8) :
        isa.eval (.nonzero .x .x4) u=some (decide (n≠0)) := by
      show some (u.read .x .x4 != 0)=_
      rw [read_x,xu]
      congr 1
      by_cases h : n=0
      · rw [decide_eq_false (not_not.mpr h)]
        have : k+2=8 := by omega
        rw [this]; rfl
      · rw [decide_eq_true h,bne_iff_ne,ne_eq]
        intro he
        have hh : BitVec.ofNat 64 (k+2) = (8 : BitVec 64) := by bv_omega
        have he' := congrArg BitVec.toNat hh
        simp only [BitVec.toNat_ofNat,show (8 : BitVec 64).toNat=8 from rfl,
          Nat.mod_eq_of_lt (show k+2<2^64 by omega)] at he'
        omega
    have e7 : loopEnv (k+1) F=stepEnv (k+2) (loopEnv k F) := rfl
    refine ⟨by rw [hz s xs,hz t xt],fun hf => ?_,fun ht => ?_⟩
    · rw [hz s xs] at hf
      have h0 : n=0 := by
        by_contra h; rw [decide_eq_true h] at hf; cases hf
      have : k+1=7 := by omega
      rw [← e7,this] at is it
      exact ⟨is,it,sp⟩
    · rw [hz s xs] at ht
      have h0 : n≠0 := by
        intro h; rw [decide_eq_false (not_not.mpr h)] at ht; cases ht
      refine ⟨n-1,by omega,by omega,⟨?_,?_⟩,⟨?_,?_⟩,sp⟩
      · rw [show 6-(n-1)=k+1 by omega,e7]; exact is
      · rw [cs,show 7-(n-1)=k+2 by omega]
      · rw [show 6-(n-1)=k+1 by omega,e7]; exact it
      · rw [ct,show 7-(n-1)=k+2 by omega]
  exact (RelCT.loop I step 6).mono (fun s t ⟨⟨is,cs⟩,⟨it,ct⟩,sp⟩ =>
    ⟨by decide,⟨is,cs⟩,⟨it,ct⟩,sp⟩) fun _ _ h => h

/-- Runs of the build from one environment leak the same and reach one
environment. -/
theorem build_relCT {base : Addr} {E : Nat → Fe C} :
    RelCT isa (fun s t => Inv M base 8192 C.p Sl V0 E s ∧ Inv M base 8192 C.p Sl V0 E t ∧ s.sp=t.sp)
      Impl.P256.VerifyTable.build
      (fun s t => Inv M base 8192 C.p Sl (copiesV l4 (Vl 7)) (buildEnv E) s ∧
        Inv M base 8192 C.p Sl (copiesV l4 (Vl 7)) (buildEnv E) t ∧ s.sp=t.sp) := by
  unfold Impl.P256.VerifyTable.build
  have r1 := phase_relCT (A:=Inv M base 8192 C.p Sl V0 E)
    (B:=fun t => Inv M base 8192 C.p Sl (dsts 1 ++ copiesV l1 V0) (startEnv E) t ∧
      t.gpr .x19=BitVec.ofNat 64 1) start_ct
    (fun s is => WP.mono (start_ok layout aligned hs is) fun t ⟨kt,ct,it⟩ => ⟨⟨it,ct⟩,kt.regs.sp⟩)
    (fun s t a b sp => agree0 a.scr b.scr sp)
  have r2 := phase_relCT
    (A:=fun t => Inv M base 8192 C.p Sl (dsts 1 ++ copiesV l1 V0) (startEnv E) t ∧
      t.gpr .x19=BitVec.ofNat 64 1)
    (B:=fun t => Inv M base 8192 C.p Sl ([704,736,768,864,896,5400,5432] ++ dsts 1 ++ V0)
      (runOps (ops true) (startEnv E)) t ∧ t.gpr .x19=BitVec.ofNat 64 1) Proof.P256.EcdhTable.Dblu.ct
    (fun s ⟨is,cs⟩ => WP.mono (dblu_ok layout aligned hs is) fun t ⟨kt,ct,it⟩ =>
      ⟨⟨it,ct.trans cs⟩,kt.regs.sp⟩)
    (fun s t a b sp => agree0 a.1.scr b.1.scr sp)
  have r3 := phase_relCT
    (A:=fun t => Inv M base 8192 C.p Sl ([704,736,768,864,896,5400,5432] ++ dsts 1 ++ V0)
      (runOps (ops true) (startEnv E)) t ∧ t.gpr .x19=BitVec.ofNat 64 1)
    (B:=fun t => Inv M base 8192 C.p Sl (Vl 0) (dbluEnv E) t ∧ t.gpr .x19=BitVec.ofNat 64 1) swap_ct
    (fun s ⟨is,cs⟩ => WP.mono (swap_ok layout aligned hs is) fun t ⟨kt,ct,it⟩ =>
      ⟨⟨it,ct.trans cs⟩,kt.regs.sp⟩)
    (fun s t a b sp => agree0 a.1.scr b.1.scr sp)
  have r5 := phase_relCT (A:=Inv M base 8192 C.p Sl (Vl 7) (loopEnv 7 (dbluEnv E)))
    (B:=Inv M base 8192 C.p Sl (copiesV l4 (Vl 7)) (buildEnv E)) finish_ct
    (fun s is => WP.mono (finish_ok layout aligned hs is) fun t ⟨kt,it⟩ => ⟨it,kt.regs.sp⟩)
    (fun s t a b sp => agree0 a.scr b.scr sp)
  exact r1.seq (r2.seq (r3.seq ((loop_relCT layout aligned hs).seq r5)))

end

end VG.Proof.P256.VerifyTable
