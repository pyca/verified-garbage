module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFinishResult

import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignInvalid
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Dsa.RandomSign
/-! Whole-entry execution, frame restoration, and stack bounds. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/RandomSignBody.lean`, which only this module imported.
section

/-! Compose initialization, bounded retries, and publication for admissible q. -/
section
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
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_sign_sp (v : Backend) :
    (RandomSign.code (randomSignerName v) (SignVerify.sign v.mul)).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_forall (fun _ => rfl) _

theorem random_sign_depth (v : Backend) :
    16 * (RandomSign.code (randomSignerName v) (SignVerify.sign v.mul)).aarch64Depth ≤ v.stack + 256 := by
  simp only [RandomSign.code, RandomSign.body, RandomSign.attempt, Code.aarch64Depth,
    show Random.prepare.aarch64Depth = 0 from rfl,
    show Random.sample.aarch64Depth = 0 from rfl,
    show RandomSign.callFinish.aarch64Depth = 0 from rfl,
    show RandomSign.finish.aarch64Depth = 0 from rfl,
    Nat.zero_max, Nat.max_zero]
  change 16 * ((SignVerify.sign v.mul).aarch64Depth + 16) ≤ _
  simpa only [Nat.mul_add, show 16 * 16 = 256 from rfl] using Nat.add_le_add_right v.signDepth 256

theorem random_sign_body (v : Backend) {s : State} (h : RandomSignABI v.stack s) :
    WP isa (RandomSign.body (randomSignerName v) (SignVerify.sign v.mul))
      (allocated Random.frameBytes s)
      (RandomSignBodyPost s (randomSignRemaining (randomInput s) 0 8)) := by
  by_cases hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)
  · exact random_sign_body_valid v h hq
  · exact random_sign_body_invalid v h hq

theorem random_remaining_bytes {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    randomSignRemaining (randomInput s) 0 8 =
      Spec.Dsa.randomSignBytes (randomInput s).pLen (randomInput s).qLen (randomInput s).key
        (randomInput s).digest (randomInput s).rand := by
  simp only [Spec.Dsa.randomSignBytes, randomInput, bytesAt_length, h.lengths, h.keyLength,
    bne_self_eq_false, decide_true, Bool.not_true, Bool.false_or, Bool.false_eq_true, ite_false,
    randomSignRemaining, List.drop_zero]

structure RandomSignCodePost (s : State) (result : Spec.Dsa.RandomSignResult) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  status : t.gpr .x0 = BitVec.ofNat 64 result.status
  output : Spec.Rsa.bytesAt t.mem (s.gpr .x0) (s.gpr .x1).toNat =
    result.signature.getD (List.replicate (s.gpr .x1).toNat 0)
  used : t.mem.readW (s.gpr .x2) 64 = BitVec.ofNat 64 result.used
  callee : ∀ r ∈ preserved, t.gpr r = s.gpr r
  sp : t.sp = s.sp
  vectors : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  nonce : ∀ i < 32, t.mem (off (randomBase s) (200 + i)) = 0

theorem random_sign_code (v : Backend) {s : State} (h : RandomSignABI v.stack s) :
    WP isa (RandomSign.code (randomSignerName v) (SignVerify.sign v.mul)) s
      (RandomSignCodePost s (randomSignRemaining (randomInput s) 0 8)) := by
  apply random_frame_ok h
  refine WP.mono (random_sign_body v h) fun t ht => ⟨ht.sp, ht.wr, ?_⟩
  refine ⟨ht.rd, by change t.wr.tail = _; rw [ht.wr]; rfl, ht.status, ht.output, ht.used,
    ht.callee, ?_, ht.vectors, ht.nonce⟩
  change t.sp + BitVec.ofNat 64 Random.frameBytes = s.sp
  rw [ht.sp, randomBase, BitVec.sub_add_cancel]

end VG.Proof.Dsa.AArch64
