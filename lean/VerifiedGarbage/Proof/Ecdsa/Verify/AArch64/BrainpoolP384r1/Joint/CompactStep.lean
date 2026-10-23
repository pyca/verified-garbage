module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Prep
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Choose
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.LoopOps
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP384r1.AArch64.Joint
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.TableLayout

/-! One complete addition shared by the fifteen public table entries. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint

materialize_code Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.prepChoice
materialize_code Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.storeChoice

theorem with_counter {c : Prog isa} {s : State} {Q : State → Prop}
    (h : ∀ i ∈ instrs c,clobbers i .x19=false) (w : WP isa c s Q) :
    WP isa c s fun t => Q t ∧ t.gpr .x19=s.gpr .x19 := by
  obtain ⟨tr,t,e,q⟩ := w
  exact ⟨tr,t,e,q,Exec.gpr h e⟩

private theorem prep_counter : ∀ i ∈ instrs prepChoice,clobbers i .x19=false := by
  have h : prepChoice.allInstrs (fun i => decide (clobbers i .x19=false))=true := by lit_decide
  rw [Code.allInstrs_eq,List.all_eq_true] at h
  exact fun i hi => of_decide_eq_true (h i hi)

private theorem store_counter : ∀ i ∈ instrs storeChoice,clobbers i .x19=false := by
  have h : storeChoice.allInstrs (fun i => decide (clobbers i .x19=false))=true := by lit_decide
  rw [Code.allInstrs_eq,List.all_eq_true] at h
  exact fun i hi => of_decide_eq_true (h i hi)

theorem prepChoice_ok {base : Addr} {P Q : Point C} {s : State}
    (hc : BaseCfgOk cfg) (hC : Law C) {d : Nat} (h1 : 1 ≤ d) (h15 : d ≤ 15)
    (hi : Inputs base P Q s) (ht : Table base P Q (d-1) s)
    (h19 : s.gpr .x19=BitVec.ofNat 64 d) :
    WP isa prepChoice s fun t =>
      (Changes base loopWork s t ∧ Inputs base P Q t ∧
        PointAt base t resultPt (pair P Q ((previous d)%4) ((previous d)/4)) ∧
        PointAt base t entry (if d%4=0 then Q else P)) ∧ t.gpr .x19=s.gpr .x19 := by
  apply with_counter prep_counter
  apply choose_wp tablePrep 15 (by decide) h1 h15 h19
  intro u ku
  have W : Changes base loopWork s u := Changes.of_keeps ku (by decide)
  have I := hi.unch (W.mono loopWork_sub)
  have T : Table base P Q (d-1) u := fun j hj hjm =>
    W.table hi.scr hj (by omega) (ht j hj hjm)
  exact WP.mono (tablePrep_ok hc hC h1 h15 I T) fun t ⟨w,i,r,e⟩ => ⟨W.trans w,i,r,e⟩

theorem storeChoice_ok {base : Addr} {P Q : Point C} {s : State}
    {d : Nat} (h1 : 1 ≤ d) (h15 : d ≤ 15) (hi : Inputs base P Q s)
    (ht : Table base P Q (d-1) s)
    (hp : PointAt base s resultPt (pair P Q (d%4) (d/4)))
    (h19 : s.gpr .x19=BitVec.ofNat 64 d) :
    WP isa storeChoice s fun t =>
      (Changes base arithmeticWork s t ∧ Inputs base P Q t ∧ Table base P Q d t) ∧
      t.gpr .x19=s.gpr .x19 := by
  apply with_counter store_counter
  apply choose_wp tableStore 15 (by decide) h1 h15 h19
  intro u ku
  have W : Changes base loopWork s u := Changes.of_keeps ku (by decide)
  have I := hi.unch (W.mono loopWork_sub)
  have T : Table base P Q (d-1) u := fun j hj hjm =>
    W.table hi.scr hj (by omega) (ht j hj hjm)
  have R := hp.of_mem ku.mem
  refine WP.mono (copy_point I.scr (store_layout h1 h15) R) fun t ⟨k,p,_⟩ => ?_
  have K := (W.mono loopWork_sub).trans (k.cover (tableWork_cover h1 h15))
  refine ⟨K,hi.unch K,fun j hj hjd => ?_⟩
  by_cases heq : j=d
  · subst j; exact p
  · have hj' : j < d := by omega
    exact k.point I.scr (T j hj (by omega))
      (fun x hx => Nat.le_trans (table_coord_bounds hj (by omega) x hx).2.1 (by decide))
      (earlier_table_apart hj hj')
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
