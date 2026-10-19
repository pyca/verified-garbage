module

public import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeState
public import VerifiedGarbage.Impl.Bignum.Arm.PdFn
public import VerifiedGarbage.Proof.Bignum.Arm.PdBodyInput
public import VerifiedGarbage.Proof.Bignum.Arm.PdCheckRest
public import VerifiedGarbage.Proof.Bignum.Arm.PdImport
import VerifiedGarbage.Proof.Bignum.Arm.PdChecks
import VerifiedGarbage.Proof.Bignum.Arm.PdPrepare
import VerifiedGarbage.Proof.Framework.Offset

/-! # Intermediate public states used to compose the packed-key leakage proof -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

structure PdPrepared (base dst pp ep xp : BitVec 32) (len k eLen N R : Nat) (eb xb : List Byte) (s : State) : Prop where
  body : PdBodyInput base dst pp ep xp len k eLen N R eb xb s
  input : PdImportInput base pp len (Spec.Rsa.modulusWords k) s

structure PdLoaded (base dst pp ep xp : BitVec 32) (len k eLen N R : Nat) (eb xb : List Byte) (s : State) : Prop where
  body : PdBodyInput base dst pp ep xp len k eLen N R eb xb s
  check : PdCheckState base len (Spec.Rsa.modulusWords k) N R s

structure PdCheckedState (base dst pp ep xp : BitVec 32) (len k eLen N R : Nat) (eb xb : List Byte) (s : State) : Prop extends
    PdLoaded base dst pp ep xp len k eLen N R eb xb s where
  flag : s.z = !(pdAccepted N R)

theorem pdPrepare_ready (s : State) {base dst pp ep xp : BitVec 32} {len k eLen N R : Nat} {eb xb : List Byte}
    (h : PdBodyInput base dst pp ep xp len k eLen N R eb xb s) :
    WP isa PdFn.prepare s (PdPrepared base dst pp ep xp len k eLen N R eb xb) :=
  WP.mono (pdPrepare_ok s h) (fun _ j => ⟨j.1, j.2.1⟩)

theorem pdImport_ready (s : State) {base dst pp ep xp : BitVec 32} {len k eLen N R : Nat} {eb xb : List Byte}
    (h : PdPrepared base dst pp ep xp len k eLen N R eb xb s) :
    WP isa pdImport s (PdLoaded base dst pp ep xp len k eLen N R eb xb) := by
  refine WP.mono (pdImport_ok s h.input) ?_
  rintro t ⟨ready, modulus, r2, frame, rest⟩
  have ht := h.body.after_workspace frame rest ready.ptr
  exact ⟨ht, ⟨ready, by have := ht.stack.nowrap; omega,
    ⟨_, ht.stack.frameWritable, Offset.contains_base _ (by decide) (by decide)⟩,
    ht.stack.separate.symm.sub_right (Offset.sub_base _ (by decide)),
    modulus.trans h.body.modulus, r2.trans h.body.r2⟩⟩

theorem pdChecks_ready (s : State) {base dst pp ep xp : BitVec 32} {len k eLen N R : Nat} {eb xb : List Byte}
    (h : PdLoaded base dst pp ep xp len k eLen N R eb xb s) :
    WP isa pdChecks s (PdCheckedState base dst pp ep xp len k eLen N R eb xb) := by
  refine WP.mono (pdChecks_ok s h.check) ?_
  rintro t ⟨check, _, flag, frame, rest⟩
  exact ⟨⟨h.body.after_checks frame rest check.ready.ptr, check⟩, flag⟩

theorem PdLoaded.precompute {s : State} {base dst pp ep xp : BitVec 32} {len k eLen N R : Nat} {eb xb : List Byte}
    (h : PdLoaded base dst pp ep xp len k eLen N R eb xb s) (valid : pdAccepted N R = true) :
    PrecomputeModulus base len (Spec.Rsa.modulusWords k) s := by
  obtain ⟨large, _, odd⟩ := pdAccepted_facts valid
  exact ⟨⟨h.check.ready.workspace, h.check.ready.layout, h.check.ready.width, h.check.ready.ptr,
    h.check.ready.stackRead, h.check.ready.stackSep, h.check.ready.saved⟩,
    by rw [h.check.modulus]; exact large, by rw [h.check.modulus]; exact odd⟩
end VG.Proof.Bignum.Arm
