module
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignRunning
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCall

import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignResume
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignArgsSaved
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallRetry
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallValue
import VerifiedGarbage.Proof.Dsa.AArch64.CallFinishCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallMemory
import VerifiedGarbage.Proof.Dsa.AArch64.RandomMemory
import VerifiedGarbage.Proof.Bignum.Octets

/-! One complete supplied-nonce signing step, including arguments and retry state. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def randomSingleResult (s : State) (k : Nat) : Option (List Byte) :=
  Spec.Dsa.signBytes (randomInput s).pLen (randomInput s).qLen (randomInput s).key
    (Spec.Dsa.encodeBE (randomInput s).qLen k) (randomInput s).digest

theorem random_sign_single (v : Backend) {s t : State} {h : RandomSignABI v.stack s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {used fuel k : Nat}
    (hr : RandomSignRunning h hq used fuel t) (hpos : 0 < fuel) (hbound : fuel < 2 ^ 64)
    (hnonce : Spec.Rsa.bytesAt t.mem (off (randomBase s) Random.oNonce) (s.gpr .x6).toNat =
      Spec.Dsa.encodeBE (s.gpr .x6).toNat k) :
    WP isa (.seq (.block RandomSign.callArgs)
      (.seq (.call (randomSignerName v) (SignVerify.sign v.mul)) RandomSign.callFinish)) t fun u =>
      RandomSignRunning h hq used (if (randomSingleResult s k).isSome then fuel else fuel - 1) u ∧
      word u.mem (randomBase s) Random.oStatus =
        (if (randomSingleResult s k).isSome then 1 else if fuel = 1 then 0 else 4) ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .x0) (s.gpr .x1).toNat =
        (randomSingleResult s k).getD (List.replicate (s.gpr .x1).toNat 0) := by
  obtain ⟨cm, draws, hready⟩ := hr.ready
  refine WP.seq (WP.mono (random_callArgs_saved hready.scr hready.sp hr.saved)
    fun a ⟨hdi, hsi, hdx, hcx, h8, h9, h6, h7, hw, _, hargs, hka⟩ => ?_)
  have hspA := hka.sp.trans hready.sp
  have hargsF := InScr.of_outside hargs (show 0 + 40 ≤ Random.frameBytes by decide)
  have hkeyA := hr.key.congrK hargsF hka
  have hdigestA := hr.digest.congrK hargsF hka
  have hqbound : (s.gpr .x6).toNat ≤ 32 := by
    have hl := h.lengths
    unfold Spec.Dsa.lengthsValid at hl
    omega
  have hres : randomCallResult s a = randomSingleResult s k := by
    rw [random_callResult_plain h hspA]
    have hkey : Spec.Rsa.bytesAt a.mem (s.gpr .x3) (s.gpr .x4).toNat = (randomInput s).key := by
      simpa only [randomInput, bytesAt_length] using sourceBytes_eq hkeyA
    have hdigest : Spec.Rsa.bytesAt a.mem (s.gpr .x7) (stackArg s 0).toNat = (randomInput s).digest := by
      simpa only [randomInput, bytesAt_length] using sourceBytes_eq hdigestA
    have hnonceA := (random_outside_bytes hargs
      (show Random.oNonce + (s.gpr .x6).toNat ≤ 2 ^ 64 by unfold Random.oNonce; omega)
      (Or.inr (show 0 + 40 ≤ Random.oNonce by decide))).trans hnonce
    rw [hkey, hdigest, hnonceA]
    rfl
  have hna : word a.mem (randomBase s) Random.oAttempts = BitVec.ofNat 64 fuel :=
    (hargs.word (by decide) (by decide)).trans hr.attempts
  have hlink : word a.mem (randomBase s) RandomSign.oLink = a.gpr .x30 := by
    rw [hargs.word (by decide) (by decide), hr.link,
      hka.gpr .x30 (by decide), hr.callee .x30 (by simp [preserved])]
  refine WP.mono (random_signer_retry v h hspA hw hdi hsi hdx hcx h8 h9 h6 h7
    (hka.rd.trans hr.rd) (hka.wr.trans hr.wr) hna hlink hpos hbound)
    fun u ⟨hur, huw, husp, huc, ⟨m, hf, hout, hum⟩, hv⟩ => ?_
  rw [hres] at hout hum
  have hpostF : InScr (randomBase s) Random.frameBytes m u.mem := by
    rw [hum]; exact InScr.of_outside (random_retry_outside _ _ _ _) (by decide)
  refine ⟨hr.after_signer (randomSingleResult s k).isSome hargs (hka.mono (by decide)) hf hum hur huw huc husp
    (fun r hc => (hv r hc).trans (hka.vcs r hc)), ?_, ?_⟩
  · rw [hum, random_retry_status]
  · exact (random_private_bytes hpostF ((h.stackOut.sub_left (random_frame_sub h)).symm)
      (Nat.le_of_lt (s.gpr .x1).isLt)).trans hout

end VG.Proof.Dsa.AArch64
