module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSingle
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSample
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! Execute one randomized signing attempt, including sampling and retries. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64
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
      Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
        (randomSingleResult s k).getD (List.replicate (s.gpr .rsi).toNat 0)

theorem random_sign_test_one {t : State} :
    WP isa (.block [.alu .cmp .rax (.imm 1)]) t fun u =>
      (u.mem = t.mem ∧ u.zf = some (t.gpr .rax == 1)) ∧ Keep [.rax] t u := by
  refine WP.keep [.rax] ?_ rfl
  xrun []
  exact sub_beq_zero _ _

theorem random_sign_attempt (v : Backend) {s t : State} {h : RandomSignABI v.stack s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {used fuel : Nat}
    (hr : RandomSignRunning h hq used fuel t) (hpos : 0 < fuel) (hbound : fuel < 2 ^ 64) :
    WP isa (RandomSign.attempt (randomSignerName v) (SignVerify.sign v.sq v.mul)) t (RandomSignAttemptPost h hq used fuel) := by
  unfold RandomSign.attempt
  refine WP.seq (WP.mono (random_sign_sample hr) fun a ⟨ha, hstatus, har, hnonce⟩ => ?_)
  refine WP.seq (WP.mono_mx (by decide) (random_sign_test_one (t := a)) fun b ⟨⟨hbm, hbz⟩, hkb⟩ hmx => ?_)
  have hbr := har.congr hbm hkb hmx
  rw [ha] at hbz
  cases hc : (VG.Proof.Dsa.randomSignDraw (randomInput s) used).scalar with
  | none =>
    have ht : (BitVec.ofNat 64 (sampleStatus (VG.Proof.Dsa.randomSignDraw (randomInput s) used)) == 1) = false := by
      simp only [sampleStatus, hc]
      split <;> rfl
    refine WP.ite false (by simp only [eval, hbz, ht]) (fun he => Bool.noConfusion he)
      (fun _ => WP.block_nil ?_)
    simp only [RandomSignAttemptPost, hc]
    exact ⟨hbr, by rw [hbm]; exact hstatus⟩
  | some k =>
    have ht : (BitVec.ofNat 64 (sampleStatus (VG.Proof.Dsa.randomSignDraw (randomInput s) used)) == 1) = true := by
      rw [sampleStatus, hc]
      rfl
    refine WP.ite true (by simp only [eval, hbz, ht]) (fun _ => ?_) (fun he => Bool.noConfusion he)
    refine WP.mono (random_sign_single v hbr hpos hbound (by rw [hbm]; exact hnonce k hc)) fun u hu => ?_
    simpa only [RandomSignAttemptPost, hc] using hu

end VG.Proof.Dsa.X86_64
