module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSingle
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSample
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Execute one randomized signing attempt, including sampling and retries. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64
open VG.Proof.Dsa.Random

def RandomSignAttemptPost {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)) (used fuel : Nat) (u : State) : Prop :=
  let draw := VG.Proof.Dsa.randomSignDraw (randomInput s) used
  match draw.scalar with
  | none => RandomSignRunning h hq (used + draw.used) fuel u ∧
      word u.mem (randomBase s) Random.oStatus = BitVec.ofNat 64 (sampleStatus draw)
  | some k =>
      RandomSignRunning h hq (used + draw.used) (if (randomSingleResult s k).isSome then fuel else fuel - 1) u ∧
      word u.mem (randomBase s) Random.oStatus =
        (if (randomSingleResult s k).isSome then 1 else if fuel = 1 then 0 else 4) ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .x0) (s.gpr .x1).toNat =
        (randomSingleResult s k).getD (List.replicate (s.gpr .x1).toNat 0)

theorem random_sign_test_one {t : State} :
    WP isa (.block [.subImm .x .x4 .x0 1]) t fun u =>
      (u.mem = t.mem ∧ (u.gpr .x4 == 0#64) = (t.gpr .x0 == 1#64)) ∧ Keep [.x0, .x4] t u := by
  refine WP.keep [.x0, .x4] ?_ rfl rfl rfl
  brun []
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, BitVec.sub_eq_iff_eq_add, BitVec.zero_add]


theorem random_sign_attempt (v : Backend) {s t : State} {h : RandomSignABI v.stack s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {used fuel : Nat}
    (hr : RandomSignRunning h hq used fuel t) (hpos : 0 < fuel) (hbound : fuel < 2 ^ 64) :
    WP isa (RandomSign.attempt (randomSignerName v) (SignVerify.sign v.mul)) t (RandomSignAttemptPost h hq used fuel) := by
  unfold RandomSign.attempt
  refine WP.seq (WP.mono (random_sign_sample hr) fun a ⟨ha, hstatus, har, hnonce⟩ => ?_)
  refine WP.seq (WP.mono (random_sign_test_one (t := a)) fun b ⟨⟨hbm, hbz⟩, hkb⟩ => ?_)
  have hbr := har.congr hbm hkb
  rw [ha] at hbz
  cases hc : (VG.Proof.Dsa.randomSignDraw (randomInput s) used).scalar with
  | none =>
    have ht : (BitVec.ofNat 64 (sampleStatus (VG.Proof.Dsa.randomSignDraw (randomInput s) used)) == 1#64) = false := by
      simp only [sampleStatus, hc]
      split <;> rfl
    refine WP.ite false (by
      change some (b.gpr .x4 == 0#64) = _
      rw [hbz, ht]) (fun he => Bool.noConfusion he)
      (fun _ => WP.block_nil ?_)
    simp only [RandomSignAttemptPost, hc]
    exact ⟨hbr, by rw [hbm]; exact hstatus⟩
  | some k =>
    have ht : (BitVec.ofNat 64 (sampleStatus (VG.Proof.Dsa.randomSignDraw (randomInput s) used)) == 1#64) = true := by
      rw [sampleStatus, hc]
      rfl
    refine WP.ite true (by
      change some (b.gpr .x4 == 0#64) = _
      rw [hbz, ht]) (fun _ => ?_) (fun he => Bool.noConfusion he)
    refine WP.mono (random_sign_single v hbr hpos hbound (by rw [hbm]; exact hnonce k hc)) fun u hu => ?_
    simpa only [RandomSignAttemptPost, hc] using hu

end VG.Proof.Dsa.AArch64
