module

public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.NatPairs
public import VerifiedGarbage.Spec.Ecdsa.P384
public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
public import VerifiedGarbage.Proof.Ecdsa.Arm.Main
public import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Umaal
public import VerifiedGarbage.Impl.Ecdsa.P384.ArmComb
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Arm.P384.CombGenerator
import VerifiedGarbage.Proof.Ecdsa.Arm.P384.CombLit
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
public import VerifiedGarbage.Proof.Ecdsa.Contract
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConsts
import VerifiedGarbage.Proof.Framework.Arm.TaintSym
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PlainSimp
import Mathlib.Logic.Function.Basic
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Umaal
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P384.CombLit
meta import VerifiedGarbage.Proof.Framework.Arm.TaintSym
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Impl.Ecdsa.P384.ArmComb
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData

/-!
# ECDSA over P-384 on 32-bit ARM with the generator comb

`vg_ecdsa_p384_sign` with `[k]G` by the shared signed seven-bit comb, whose
table is a read-only constant: the contract with the table, its constant
time, and `Verified`.
-/

@[expose] public section
namespace VG.Proof.Ecdsa.Arm.P384
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm.TComb
open VG.Proof.Ecdsa.Arm

/-- The tables signing reads: the comb's, and the setup's constants. -/
abbrev combSignK (u : Bool) : List (String × List (BitVec 64)) := p384CombConsts ++ (p384With u).constsK

def combSignPre (u : Bool) (s : State) : Prop :=
  Pre (p384With u) s (constRegs (combSignK u) s) ∧ ConstsOk (combSignK u) 0 s

def combSignPub (u : Bool) (s t : State) : Prop :=
  signArm.pub s t ∧ s.syms p384Comb.tsym=t.syms p384Comb.tsym ∧ s.syms (p384With u).constSym=t.syms (p384With u).constSym

theorem combSign_agree {u : Bool} {s t : State} (hs : combSignPre u s) (ht : combSignPre u t)
    (pub : combSignPub u s t) :
    VG.Arm.Taint.Agree τ₁ s t ∧ ∀ n ∈ [p384Comb.tsym,(p384With u).constSym], s.syms n = t.syms n :=
  ⟨agree₁ (agree₀ hs.1 ht.1 pub.1),fun n hn => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl|rfl
    exacts [pub.2.1,pub.2.2]⟩

theorem combSign_ct : ConstantTime isa (combSignPre false) (combSignPub false) signP384Comb :=
  VG.Taint.constantTime (A := taintSym [p384Comb.tsym,(p384With false).constSym]) τ₁
    (fun _ _ hs ht pub => combSign_agree hs ht pub) (by native_taint_decide)

theorem combSignU_ct : ConstantTime isa (combSignPre true) (combSignPub true) signP384CombU :=
  VG.Taint.constantTime (A := taintSymU [p384Comb.tsym,(p384With true).constSym]) τ₁
    (fun _ _ hs ht pub => combSign_agree hs ht pub) (by native_taint_decide)

theorem combSign_ok (hC : Law Spec.P384.curve) {u : Bool} {s₀ : State} (hp : combSignPre u s₀) :
    WP isa (signP384CombWith u) s₀ fun t => SignKeep (p384With u) s₀ t ∧ SignPost (p384With u) s₀ t := by
  have member : (p384Comb.tsym,p384CombWords)∈combSignK u := List.mem_cons_self
  have ht := tableMem_of_consts hp.2 member
  have hd := table_disjoint_of_consts hp.2 member
    (show scR s₀∈s₀.wr by rw [hp.1.wr]; simp)
  exact signWith_ok (p384With_ok u) hC hp.1 fun _ S sy => comb_generator_stage hC S sy ht rfl hd

end VG.Proof.Ecdsa.Arm.P384
