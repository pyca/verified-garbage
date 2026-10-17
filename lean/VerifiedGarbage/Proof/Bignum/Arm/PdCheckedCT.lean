module

public import VerifiedGarbage.Proof.Bignum.Arm.PdStages
public import VerifiedGarbage.Proof.Bignum.Arm.PdChecksCT
public import VerifiedGarbage.Proof.Bignum.Arm.PdApplyCT
public import VerifiedGarbage.Proof.Bignum.Arm.PdFailCT
public import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Packed-key checks branch only on public values -/

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
