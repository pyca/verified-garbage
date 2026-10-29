module

public import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeState
public import VerifiedGarbage.Impl.Bignum.Arm.PdFn
public import VerifiedGarbage.Proof.Bignum.Arm.PdBodyInput
public import VerifiedGarbage.Proof.Bignum.Arm.PdCheckRest
public import VerifiedGarbage.Proof.Bignum.Arm.PdImport

import VerifiedGarbage.Proof.Bignum.Arm.PdChecksCT
import VerifiedGarbage.Proof.Bignum.Arm.PdApplyCT
import VerifiedGarbage.Proof.Bignum.Arm.PdFailCT
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeCT
import VerifiedGarbage.Proof.Bignum.Arm.PdInverse
import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
import VerifiedGarbage.Proof.Bignum.Arm.PdChecks
import VerifiedGarbage.Proof.Bignum.Arm.PdPrepare
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Arm.PublicStackFrame
/-! # Packed-key checks branch only on public values -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/PdStages.lean`, which only this module imported.
section

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
end

end

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem pdInverseApply_ct {base dst pp ep xp : BitVec 32} {len k eLen N R : Nat} {eb xb1 xb2 : List Byte}
    (valid : pdAccepted N R = true) :
    RelCT isa (fun s t => PdLoaded base dst pp ep xp len k eLen N R eb xb1 s ∧
      PdLoaded base dst pp ep xp len k eLen N R eb xb2 t ∧ s.sp = t.sp)
      PdFn.apply (fun _ _ => True) := by
  have wp (s : State) {xb : List Byte} (h : PdLoaded base dst pp ep xp len k eLen N R eb xb s) :
      WP isa precomputeInverse s (PdArithmetic base dst pp ep xp len k eLen N R eb xb) :=
    WP.mono (pdInverse_ok s h.body h.check valid) (fun _ j => j.1)
  exact crt_seq_ct (precomputeInverse_ct.mono
    (fun _ _ h => ⟨h.1.precompute valid, h.2.1.precompute valid⟩) (fun _ _ _ => trivial))
    (fun s h => wp s h) (fun s h => wp s h) pdApply_ct

theorem pdChecked_ct {base dst pp ep xp : BitVec 32} {len k eLen N R : Nat} {eb xb1 xb2 : List Byte} :
    RelCT isa (fun s t => PdLoaded base dst pp ep xp len k eLen N R eb xb1 s ∧
      PdLoaded base dst pp ep xp len k eLen N R eb xb2 t ∧ s.sp = t.sp)
      PdFn.checked (fun _ _ => True) := by
  have branch : RelCT isa (fun s t => PdCheckedState base dst pp ep xp len k eLen N R eb xb1 s ∧
      PdCheckedState base dst pp ep xp len k eLen N R eb xb2 t ∧ s.sp = t.sp)
      (.ite .eq PublicFn.fail PdFn.apply) (fun _ _ => True) := by
    apply RelCT.ite
    · intro s t h
      change some s.z = some t.z
      rw [h.1.flag, h.2.1.flag]
    · exact pdFail_ct.mono (fun _ _ h => ⟨h.1.1.body, h.1.2.1.body, h.1.2.2⟩) (fun _ _ _ => trivial)
    · intro s t tr1 tr2 u v h e1 e2
      have valid : pdAccepted N R = true := by
        have cond := h.2
        change some s.z = some false at cond
        rw [h.1.1.flag] at cond
        simpa using cond
      exact pdInverseApply_ct valid s t tr1 tr2 u v
        ⟨h.1.1.toPdLoaded, h.1.2.1.toPdLoaded, h.1.2.2⟩ e1 e2
  exact crt_seq_ct (pdChecks_ct.mono (fun _ _ h => ⟨h.1.check, h.2.1.check, h.2.2⟩) (fun _ _ _ => trivial))
    (fun s h => pdChecks_ready s h) (fun s h => pdChecks_ready s h) branch
end VG.Proof.Bignum.Arm
