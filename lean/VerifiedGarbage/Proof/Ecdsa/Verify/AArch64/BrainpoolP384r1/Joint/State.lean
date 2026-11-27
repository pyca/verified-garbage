module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Sum
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointAll
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP384r1.AArch64.Joint
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.AArch64
public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP384r1.AArch64.Joint
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
public import VerifiedGarbage.Proof.Mont.AArch64.Words
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.MulContract
meta import VerifiedGarbage.Proof.Weierstrass.MulContract

/-! The curve's kit for the joint verification loop (`Proof/Ecdsa/Verify/AArch64/JointAll.lean`), with its
frames and live point representations. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64
open VG.Spec.Weierstrass
open VG.Impl.Ecdsa.Verify.AArch64 (UX UY UZ)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint

abbrev C := cfg.C
abbrev coordinates (p : Pt) : List Nat := [p.x,p.y,p.z]
abbrev num (base : Addr) (s : State) (o : Nat) := wordsVal s.mem base o cfg.n
abbrev val (base : Addr) (s : State) (o : Nat) := tmv cfg.C cfg.n base s o

materialize_code Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.addPoints

/-- Complete addition preserves the public loop counter, including through the field calls. -/
theorem sum_counter : ∀ i ∈ instrs (sum cfg),clobbers i .x19 = false := by
  change ∀ i ∈ instrs addPoints,clobbers i .x19 = false
  have h : addPoints.allInstrs (fun i => decide (clobbers i .x19 = false)) = true := by lit_decide
  rw [Code.allInstrs_eq,List.all_eq_true] at h
  exact fun i hi => of_decide_eq_true (h i hi)

/-- The curve's kit. -/
instance kit : JointKit.Kit cfg := ⟨by decide, sum_counter⟩

/-- The loop's rounds: a scalar of six words. -/
theorem rounds : JointKit.Rounds cfg cfg.n :=
  ⟨by decide, by decide, fun hc => hc.n_lt⟩

materialize_code Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.prepChoice
materialize_code Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.storeChoice

/-- The table's two choices keep its counter. -/
theorem prep_counter : ∀ i ∈ instrs prepChoice,clobbers i .x19=false := by
  have h : prepChoice.allInstrs (fun i => decide (clobbers i .x19=false))=true := by lit_decide
  rw [Code.allInstrs_eq,List.all_eq_true] at h
  exact fun i hi => of_decide_eq_true (h i hi)

theorem store_counter : ∀ i ∈ instrs storeChoice,clobbers i .x19=false := by
  have h : storeChoice.allInstrs (fun i => decide (clobbers i .x19=false))=true := by lit_decide
  rw [Code.allInstrs_eq,List.all_eq_true] at h
  exact fun i hi => of_decide_eq_true (h i hi)

/-- The curve's kit for the table by a choice of copies. -/
instance compact : JointKit.Compact cfg := ⟨prep_counter, store_counter⟩

abbrev PointAt (base : Addr) (s : State) (p : Pt) (P : Point C) : Prop := JointKit.PointAt cfg base s p P
abbrev addWork : List (Nat × Nat) := JointKit.addWork cfg
abbrev entryWork : List (Nat × Nat) := JointKit.entryWork cfg
abbrev loopWork : List (Nat × Nat) := JointKit.loopWork cfg
abbrev work : List (Nat × Nat) := JointKit.work cfg
abbrev Changes (base : Addr) (W : List (Nat × Nat)) (s t : State) : Prop := JointKit.Changes base W s t

/-- Complete addition in the three live slots, with the same existing field and curve contracts. -/
theorem sum_points {base : Addr} {s : State} (hc : BaseCfgOk cfg) (hC : Law C)
    (hs : Scr s base 8192) (hm : ModOkA cfg.MP' 8192 C.p s.mem base)
    (ha : val base s (cfg.sl AP) = Fin.ofNat C.p C.a)
    (hb : val base s (cfg.sl EXPP) = Fin.ofNat C.p (3*C.b))
    (hal : num base s (cfg.sl AP) < C.p) (hbl : num base s (cfg.sl EXPP) < C.p)
    {P Q : Point C} (hP : onCurve C P = true) (hQ : onCurve C Q = true)
    (hp : PointAt base s entry P) (hq : PointAt base s resultPt Q) :
    WP isa (sum cfg) s fun t =>
      Changes base addWork s t ∧ PointAt base t resultPt (Spec.Weierstrass.add P Q) ∧
      t.gpr .x19 = s.gpr .x19 :=
  JointKit.sum_points (c := cfg) hc hC hs hm ha hb hal hbl hP hQ hp hq
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
