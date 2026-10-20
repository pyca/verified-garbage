module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignFinishResult
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Dsa.RandomSign
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! Compose initialization, bounded retries, and publication for admissible q. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem random_sign_test_zero {t : State} :
    WP isa (.block [.alu .cmp .rax (.imm 0)]) t fun u =>
      (u.mem = t.mem ∧ u.zf = some (t.gpr .rax == 0)) ∧ Keep [.rax] t u := by
  refine WP.keep [.rax] ?_ rfl
  xrun []
  exact sub_beq_zero _ _

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
    WP isa (RandomSign.body (randomSignerName v) (SignVerify.sign v.sq v.mul))
      (allocState Random.frameBytes s)
      (RandomSignBodyPost s (randomSignRemaining (randomInput s) 0 8)) := by
  unfold RandomSign.body
  apply WP.assoc
  refine WP.seq (WP.mono (random_sign_init_running h hq) fun t ⟨ha, hr⟩ => ?_)
  refine WP.seq (WP.mono_mx (by decide) (random_sign_test_zero (t := t)) fun u ⟨⟨hum, huz⟩, hku⟩ hmx => ?_)
  have hur := hr.congr hum hku hmx
  refine WP.seq (WP.ite false (by simp only [eval, huz, ha]; rfl)
    (fun he => Bool.noConfusion he) (fun _ => ?_))
  refine WP.mono (random_sign_loop_correct v hur (by decide) (by decide)) fun w hw => ?_
  exact random_finish_result hw (randomSignLoop_status_le _ _ _ _ _ _) (random_remaining_failure _ _ _)

end VG.Proof.Dsa.X86_64
