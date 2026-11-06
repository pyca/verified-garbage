module

public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.NatPairs
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP256r1
public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
public import VerifiedGarbage.Proof.Ecdsa.Arm.Main
public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.Contract
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.ArmComb
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.CombGenerator
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.CombLit
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
public import VerifiedGarbage.Proof.BrainpoolP256r1.Arm.Comb
public import VerifiedGarbage.Proof.Ecdsa.Contract
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConsts
import VerifiedGarbage.Proof.Framework.Arm.TaintSym
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PlainSimp
import Mathlib.Logic.Function.Basic
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.CombLit
meta import VerifiedGarbage.Proof.Framework.Arm.TaintSym
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.ArmComb
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
public import VerifiedGarbage.Proof.Weierstrass.MulContract
meta import VerifiedGarbage.Proof.Weierstrass.MulContract

/-!
# ECDSA over brainpoolP256r1 on 32-bit ARM with the generator comb

`vg_ecdsa_brainpoolp256r1_sign` with `[k]G` by the shared signed seven-bit comb, whose
table is a read-only constant: the contract with the table, its constant
time, and `Verified`.
-/

@[expose] public section
namespace VG.Proof.Ecdsa.Arm.BrainpoolP256r1
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm.TComb
open VG.Proof.Ecdsa.Arm

def combSignPre (u : Bool) (s : State) : Prop :=
  Pre (brainpoolp256r1With u) s (constRegs brainpoolp256r1CombConsts s) ∧ ConstsOk brainpoolp256r1CombConsts 0 s

def combSignPub (s t : State) : Prop := signArm.pub s t ∧ s.syms brainpoolp256r1Comb.tsym=t.syms brainpoolp256r1Comb.tsym

theorem combSign_ct : ConstantTime isa (combSignPre false) combSignPub signBrainpoolP256r1Comb := by
  refine VG.Taint.constantTime (A := taintSym [brainpoolp256r1Comb.tsym]) τ₀ ?_ (by native_taint_decide)
  intro s t hs ht pub
  exact ⟨agree₀ hs.1 ht.1 pub.1,fun n hn => by
    obtain rfl := List.mem_singleton.mp hn
    exact pub.2⟩

theorem combSignU_ct : ConstantTime isa (combSignPre true) combSignPub signBrainpoolP256r1CombU := by
  refine VG.Taint.constantTime (A := taintSymU [brainpoolp256r1Comb.tsym]) τ₀ ?_ (by taint_decide)
  intro s t hs ht pub
  exact ⟨agree₀ hs.1 ht.1 pub.1,fun n hn => by
    obtain rfl := List.mem_singleton.mp hn
    exact pub.2⟩

theorem combSign_ok (hC : Law Spec.BrainpoolP256r1.curve) {u : Bool} {s₀ : State} (hp : combSignPre u s₀) :
    WP isa (signBrainpoolP256r1CombWith u) s₀ fun t => SignKeep (brainpoolp256r1With u) s₀ t ∧ SignPost (brainpoolp256r1With u) s₀ t := by
  have member : (brainpoolp256r1Comb.tsym,brainpoolp256r1CombWords)∈brainpoolp256r1CombConsts := List.mem_singleton_self _
  have ht := tableMem_of_consts hp.2 member
  have hd := table_disjoint_of_consts hp.2 member
    (show scR s₀∈s₀.wr by rw [hp.1.wr]; simp)
  exact signWith_ok (brainpoolp256r1With_ok u) hC hp.1 fun _ S sy => comb_generator_stage hC S sy ht rfl hd

end VG.Proof.Ecdsa.Arm.BrainpoolP256r1
