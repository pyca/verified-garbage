module

public import VerifiedGarbage.Proof.Bignum.Arm.PcPrepareCT
public import VerifiedGarbage.Proof.Bignum.Arm.PcComputed
public import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeCT
public import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOutCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Successful public precomputation has no secret-dependent trace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem pcValid_ct {base dst src : BitVec 32} {len k : Nat} (hk : k ≤ 1024) :
    RelCT isa (fun s t => PcValidInput base dst src len k s ∧ PcValidInput base dst src len k t ∧ s.sp = t.sp)
      PcFn.valid (fun _ _ => True) := by
  have countFit : 128 * Spec.Rsa.modulusWords k < 2 ^ 32 := by
    simp only [Spec.Rsa.modulusWords]; omega
  have arithmetic := (relCT_keep_sp ((precompute_ct countFit).mono
    (P' := fun (s t : State) => PcPrepared base dst src len k s ∧ PcPrepared base dst src len k t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.input, h.2.1.input, h.2.2⟩) (fun _ _ h => h)) (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨pcComputed_ready s h.1, pcComputed_ready t h.2.1⟩)
  have output := ((loadStack_ct .r4 4).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ PcComputed base dst src len k s ∧ PcComputed base dst src len k t)
    (fun _ _ h => h.1) (fun _ _ _ => True.intro)).wp
    (fun s t h => ⟨pcExport_ready s h.2.1, pcExport_ready t h.2.2⟩)
  have tail := arithmetic.seq ((output.mono (fun _ _ h => h) (fun _ _ h => h.2)).seq precomputeOut_ct)
  have all := pcPrepare_ct.seq tail
  intro s t tr1 tr2 u v h e1 e2
  cases e1 with
  | seq a1 b1 =>
    cases b1 with
    | seq b1 c1 =>
      cases c1 with
      | seq c1 d1 =>
        cases e2 with
        | seq a2 b2 =>
          cases b2 with
          | seq b2 c2 =>
            cases c2 with
            | seq c2 d2 =>
              obtain ⟨trace, post⟩ := all _ _ _ _ _ _ h
                (.seq (.seq a1 (.seq b1 c1)) d1) (.seq (.seq a2 (.seq b2 c2)) d2)
              exact ⟨by simpa only [List.append_assoc] using trace, post⟩

end VG.Proof.Bignum.Arm
