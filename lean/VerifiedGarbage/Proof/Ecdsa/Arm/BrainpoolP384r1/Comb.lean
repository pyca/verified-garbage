module

public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.NatPairs
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP384r1
public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
public import VerifiedGarbage.Proof.Ecdsa.Arm.Main
public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP384r1.Verified
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.ArmComb
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP384r1.CombGenerator
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP384r1.CombLit
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
public import VerifiedGarbage.Proof.Ecdsa.Contract
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConsts
import VerifiedGarbage.Proof.Framework.Arm.TaintSym
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PlainSimp
import Mathlib.Logic.Function.Basic
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP384r1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP384r1.CombLit
meta import VerifiedGarbage.Proof.Framework.Arm.TaintSym
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.ArmComb
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
public import VerifiedGarbage.Proof.Weierstrass.MulContract
meta import VerifiedGarbage.Proof.Weierstrass.MulContract

/-!
# ECDSA over brainpoolP384r1 on 32-bit ARM with the generator comb

`vg_ecdsa_brainpoolp384r1_sign` with `[k]G` by the shared signed seven-bit comb, whose
table is a read-only constant: the contract with the table, its constant
time, and `Verified`.
-/

@[expose] public section
namespace VG.Proof.Ecdsa.Arm.BrainpoolP384r1
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm.TComb
open VG.Proof.Ecdsa.Arm

def combSignPre (u : Bool) (s : State) : Prop :=
  Pre (brainpoolp384r1With u) s (constRegs brainpoolp384r1CombConsts s) ∧ ConstsOk brainpoolp384r1CombConsts 0 s

def combSignPub (s t : State) : Prop := signArm.pub s t ∧ s.syms brainpoolp384r1Comb.tsym=t.syms brainpoolp384r1Comb.tsym

theorem combSign_ct : ConstantTime isa (combSignPre false) combSignPub signBrainpoolP384r1Comb := by
  refine VG.Taint.constantTime (A := taintSym [brainpoolp384r1Comb.tsym]) τ₁ ?_ (by native_taint_decide)
  intro s t hs ht pub
  exact ⟨agree₁ (agree₀ hs.1 ht.1 pub.1),fun n hn => by
    obtain rfl := List.mem_singleton.mp hn
    exact pub.2⟩

theorem combSignU_ct : ConstantTime isa (combSignPre true) combSignPub signBrainpoolP384r1CombU := by
  refine VG.Taint.constantTime (A := taintSymU [brainpoolp384r1Comb.tsym]) τ₁ ?_ (by taint_decide)
  intro s t hs ht pub
  exact ⟨agree₁ (agree₀ hs.1 ht.1 pub.1),fun n hn => by
    obtain rfl := List.mem_singleton.mp hn
    exact pub.2⟩

theorem combSign_ok (hC : Law Spec.BrainpoolP384r1.curve) {u : Bool} {s₀ : State} (hp : combSignPre u s₀) :
    WP isa (signBrainpoolP384r1CombWith u) s₀ fun t => SignKeep (brainpoolp384r1With u) s₀ t ∧ SignPost (brainpoolp384r1With u) s₀ t := by
  have member : (brainpoolp384r1Comb.tsym,brainpoolp384r1CombWords)∈brainpoolp384r1CombConsts := List.mem_singleton_self _
  have ht := tableMem_of_consts hp.2 member
  have hd := table_disjoint_of_consts hp.2 member
    (show scR s₀∈s₀.wr by rw [hp.1.wr]; simp)
  exact signWith_ok (brainpoolp384r1With_ok u) hC hp.1 fun _ S sy => comb_generator_stage hC S sy ht rfl hd

end VG.Proof.Ecdsa.Arm.BrainpoolP384r1
