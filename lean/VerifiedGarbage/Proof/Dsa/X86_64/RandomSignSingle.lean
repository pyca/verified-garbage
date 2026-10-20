module
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignRunning
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCall

import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignResume
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignArgsSaved
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallRetry
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallValue
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedExp
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallMemory
import VerifiedGarbage.Proof.Dsa.X86_64.RandomMemory
import VerifiedGarbage.Proof.Bignum.Octets

/-! One complete supplied-nonce signing step, including arguments and retry state. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def randomSingleResult (s : State) (k : Nat) : Option (List Byte) :=
  Spec.Dsa.signBytes (randomInput s).pLen (randomInput s).qLen (randomInput s).key
    (Spec.Dsa.encodeBE (randomInput s).qLen k) (randomInput s).digest

theorem random_sign_single (v : Backend) {s t : State} {h : RandomSignABI v.stack s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {used fuel k : Nat}
    (hr : RandomSignRunning h hq used fuel t) (hpos : 0 < fuel) (hbound : fuel < 2 ^ 64)
    (hnonce : Spec.Rsa.bytesAt t.mem (off (randomBase s) Random.oNonce) (stackArg s 0).toNat =
      Spec.Dsa.encodeBE (stackArg s 0).toNat k) :
    WP isa (.seq (.block RandomSign.callArgs)
      (.seq (.call (randomSignerName v) (SignVerify.sign v.sq v.mul)) RandomSign.callFinish)) t fun u =>
      RandomSignRunning h hq used (if (randomSingleResult s k).isSome then fuel else fuel - 1) u ∧
      word u.mem (randomBase s) Random.oStatus =
        (if (randomSingleResult s k).isSome then 1 else if fuel = 1 then 0 else 4) ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
        (randomSingleResult s k).getD (List.replicate (s.gpr .rsi).toNat 0) := by
  obtain ⟨cm, draws, hready⟩ := hr.ready
  refine WP.seq (WP.mono_mx (by decide) (random_callArgs_saved hready.scr hready.sp hr.saved)
    fun a ⟨hdi, hsi, hdx, hcx, h8, h9, hw, _, hargs, hka⟩ hmxa => ?_)
  have hspA := (hka.gpr (by decide)).trans hready.sp
  have hargsF := InScr.of_outside hargs (show 0 + 40 ≤ Random.frameBytes by decide)
  have hkeyA := hr.key.congrK hargsF hka
  have hdigestA := hr.digest.congrK hargsF hka
  have hqbound : (stackArg s 0).toNat ≤ 32 := by
    have hl := h.lengths
    unfold Spec.Dsa.lengthsValid at hl
    omega
  have hres : randomCallResult s a = randomSingleResult s k := by
    rw [random_callResult_plain h hspA]
    have hkey : Spec.Rsa.bytesAt a.mem (s.gpr .rcx) (s.gpr .r8).toNat = (randomInput s).key := by
      simpa only [randomInput, bytesAt_length] using FoldedPublic.src_bytesAt hkeyA
    have hdigest : Spec.Rsa.bytesAt a.mem (stackArg s 1) (stackArg s 2).toNat = (randomInput s).digest := by
      simpa only [randomInput, bytesAt_length] using FoldedPublic.src_bytesAt hdigestA
    have hnonceA := (random_outside_bytes hargs
      (show Random.oNonce + (stackArg s 0).toNat ≤ 2 ^ 64 by unfold Random.oNonce; omega)
      (Or.inr (show 0 + 40 ≤ Random.oNonce by decide))).trans hnonce
    rw [hkey, hdigest, hnonceA]
    rfl
  have hna : word a.mem (randomBase s) Random.oAttempts = BitVec.ofNat 64 fuel :=
    (hargs.word (by decide) (by decide)).trans hr.attempts
  refine WP.mono (random_signer_retry v h hspA hw hdi hsi hdx hcx h8 h9
    (hka.2.1.trans hr.rd) (hka.2.2.trans hr.wr) hna hpos hbound)
    fun u ⟨hur, huw, huc, ⟨m, hf, hout, hum⟩, hmx⟩ => ?_
  rw [hres] at hout hum
  have hpostF : InScr (randomBase s) Random.frameBytes m u.mem := by
    rw [hum]; exact InScr.of_outside (random_retry_outside _ _ _ _) (by decide)
  refine ⟨hr.after_signer (randomSingleResult s k).isSome hargs (hka.mono (by decide)) hf hum hur huw huc
    (by rw [hmx, hmxa]), ?_, ?_⟩
  · rw [hum, random_retry_status]
  · exact (random_private_bytes hpostF ((h.stackOut.sub_left (random_frame_sub h)).symm)
      (Nat.le_of_lt (s.gpr .rsi).isLt)).trans hout

end VG.Proof.Dsa.X86_64
