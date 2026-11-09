module

public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.NatPairs
public import VerifiedGarbage.Spec.Ecdsa.P256
public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
public import VerifiedGarbage.Proof.Ecdsa.Arm.Main
public import VerifiedGarbage.Proof.Ecdsa.Arm.Contract
public import VerifiedGarbage.Impl.Ecdsa.P256.ArmComb
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.Arm.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.P256.CombGenerator
import VerifiedGarbage.Proof.Ecdsa.Arm.P256.CombLit
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
public import VerifiedGarbage.Proof.P256.Arm.Comb
public import VerifiedGarbage.Proof.Ecdsa.Contract
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConsts
import VerifiedGarbage.Proof.Framework.Arm.TaintSym
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Ecdsa.Arm.P256.Umaal
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PlainSimp
import Mathlib.Logic.Function.Basic
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P256.CombLit
meta import VerifiedGarbage.Proof.Framework.Arm.TaintSym
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Impl.Ecdsa.P256.ArmComb
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData

/-!
# ECDSA over P-256 on 32-bit ARM with the generator comb

`vg_ecdsa_p256_sign` with `[k]G` by the shared signed seven-bit comb, whose
table is a read-only constant: the contract with the table, its constant
time, and `Verified`.
-/

@[expose] public section
namespace VG.Proof.Ecdsa.Arm.P256
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm.TComb
open VG.Proof.Ecdsa.Arm

def combSignPre (u : Bool) (s : State) : Prop :=
  Pre (p256With u) s (constRegs p256CombConsts s) ∧ ConstsOk p256CombConsts 0 s

def combSignPub (s t : State) : Prop := signArm.pub s t ∧ s.syms p256Comb.tsym=t.syms p256Comb.tsym

theorem combSign_ct : ConstantTime isa (combSignPre false) combSignPub signP256Comb := by
  refine VG.Taint.constantTime (A := taintSym [p256Comb.tsym]) τ₀ ?_ (by native_taint_decide)
  intro s t hs ht pub
  exact ⟨agree₀ hs.1 ht.1 pub.1,fun n hn => by
    obtain rfl := List.mem_singleton.mp hn
    exact pub.2⟩

theorem combSignU_ct : ConstantTime isa (combSignPre true) combSignPub signP256CombU := by
  refine VG.Taint.constantTime (A := taintSymU [p256Comb.tsym]) τ₀ ?_ (by taint_decide)
  intro s t hs ht pub
  exact ⟨agree₀ hs.1 ht.1 pub.1,fun n hn => by
    obtain rfl := List.mem_singleton.mp hn
    exact pub.2⟩

theorem combSign_ok (hC : Law Spec.P256.curve) {u : Bool} {s₀ : State} (hp : combSignPre u s₀) :
    WP isa (signP256CombWith u) s₀ fun t => SignKeep (p256With u) s₀ t ∧ SignPost (p256With u) s₀ t := by
  have member : (p256Comb.tsym,p256CombWords)∈p256CombConsts := List.mem_singleton_self _
  have ht := tableMem_of_consts hp.2 member
  have hd := table_disjoint_of_consts hp.2 member
    (show scR s₀∈s₀.wr by rw [hp.1.wr]; simp)
  exact signWith_ok (p256With_ok u) hC hp.1 fun _ S sy => comb_generator_stage hC S sy ht rfl hd

end VG.Proof.Ecdsa.Arm.P256
