module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTSieveLoop
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPolicy
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveInit
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTSieveStep

/-! Complete small-prime screening leaks only the public candidate and workspace layout. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post)

def SievePublic (p : SieveData) (s : State) : Prop :=
  SieveContext p.dst p.base p.bytes.length s ∧ Spec.Rsa.bytesAt s.mem (State.addr p.dst) p.bytes.length = p.bytes

private theorem sieveInit_ct : RelCT isa (fun s t => s.sp = t.sp)
    VG.Impl.Ffdh.Arm.ParameterCandidate.sieveInit (fun s t => s.sp = t.sp) := by
  have tail : RelCT isa (fun s t => s.sp = t.sp) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.sieveInitTail)
      (fun s t => s.sp = t.sp) :=
    RelCT.block_append ((stackOnly_ct VG.Impl.Ffdh.Arm.ParameterCandidate.sieveInitRegisters (by decide)).seq (save_ct .r1 64))
  exact (stackOnly_ct VG.Impl.Ffdh.Arm.ParameterCandidate.tablePointer (by decide)).seq tail

theorem sieve_ct : RelCT isa (Two SievePublic) VG.Impl.Ffdh.Arm.ParameterCandidate.sieve (fun _ _ => True) := by
  have init : RelCT isa (Two SievePublic) VG.Impl.Ffdh.Arm.ParameterCandidate.sieveInit
      (Two fun p s => SieveCTState (p, 0) s) :=
    two_post (sieveInit_ct.mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun p s h => by
      refine WP.mono (sieveInit_ok h.1) ?_
      intro t inv
      rw [h.2] at inv
      exact ⟨s, inv⟩)
  have finish : RelCT isa (fun s t => s.sp = t.sp) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.sieveFinish)
      (fun _ _ => True) := (stackOnly_ct _ rfl).mono (fun _ _ h => h) (fun _ _ _ => trivial)
  exact init.seq ((relCT_keep_sp sieveLoop_ct (fun _ _ ⟨_, _, _, sp⟩ => sp)).seq
    (finish.seq (RelCT.block_nil (fun _ _ h => h))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
