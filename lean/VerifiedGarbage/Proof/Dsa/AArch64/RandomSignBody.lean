module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFinishResult
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Dsa.RandomSign

/-! Compose initialization, bounded retries, and publication for admissible q. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_remaining_failure (p : VG.Proof.Dsa.RandomSignInput) (used fuel : Nat)
    (hs : (randomSignRemaining p used fuel).status ≠ 1) :
    (randomSignRemaining p used fuel).signature = none := by
  have he := randomSignLoop_success p.pLen p.qLen p.key p.digest fuel (p.rand.drop used)
  cases hc : (randomSignRemaining p used fuel).signature with
  | none => rfl
  | some sig =>
    exact False.elim (hs (he.mpr (by change (randomSignRemaining p used fuel).signature.isSome = true; rw [hc]; rfl)))

theorem random_sign_body_valid (v : Backend) {s : State} (h : RandomSignABI v.stack s)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)) :
    WP isa (RandomSign.body (randomSignerName v) (SignVerify.sign v.mul))
      (allocated Random.frameBytes s)
      (RandomSignBodyPost s (randomSignRemaining (randomInput s) 0 8)) := by
  unfold RandomSign.body
  apply WP.assoc
  refine WP.seq (WP.mono (random_sign_init_running h hq) fun t ⟨ha, hr⟩ => ?_)
  refine WP.seq (WP.ite false (by simp [eval, State.read, ha])
    (fun he => Bool.noConfusion he) (fun _ => ?_))
  refine WP.mono (random_sign_loop_correct v hr (by decide) (by decide)) fun w hw => ?_
  exact random_finish_result hw (randomSignLoop_status_le _ _ _ _ _ _) (random_remaining_failure _ _ _)

end VG.Proof.Dsa.AArch64
