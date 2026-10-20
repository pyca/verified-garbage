module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallCT
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSingle
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignRetryCT
import VerifiedGarbage.Proof.Dsa.AArch64.CallFinishCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallValue
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignArgsSaved
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallMemory
import VerifiedGarbage.Proof.Dsa.AArch64.RandomMemory
import VerifiedGarbage.Proof.Bignum.Octets

/-! Observe call-boundary data without constraining the private nonce or digest. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_call_key_source {extra : Nat} {s t : State} (_h : RandomSignABI extra s)
    (_hsp : t.sp = randomBase s)
    (hkey : Src t (randomBase s) Random.frameBytes (s.gpr .x3) (randomInput s).key) :
    randomCallPublicKey s t = Spec.Dsa.publicBytesLeak (randomInput s).pLen (randomInput s).qLen (randomInput s).key := by
  unfold randomCallPublicKey
  change Spec.Dsa.publicBytesLeak _ _ (Spec.Rsa.bytesAt t.mem _ _) = _
  have hkb : Spec.Rsa.bytesAt t.mem (s.gpr .x3) (s.gpr .x4).toNat = (randomInput s).key := by
    simpa only [randomInput, bytesAt_length] using sourceBytes_eq hkey
  rw [hkb]
  rfl

theorem random_signer_retry_pre (v : Backend) {s t : State} {fuel : Nat} {h : RandomSignABI v.stack s}
    (hc : RandomSignCallState h t)
    (hn : word t.mem (randomBase s) Random.oAttempts = BitVec.ofNat 64 fuel)
    (hpos : 0 < fuel) (hbound : fuel < 2 ^ 64) :
    WP isa (.call (randomSignerName v) (SignVerify.sign v.mul)) t
      (RandomRetryPre ⟨randomBase s, (randomCallResult s t).isSome, fuel⟩) := by
  refine WP.mono (random_signer_outcome v h hc.sp hc.args hc.di hc.si hc.dx hc.cx hc.r8 hc.r9 hc.x6 hc.x7 hc.rd hc.wr)
    fun u ⟨_, huw, husp, _, hf, hstatus, _, _⟩ => ?_
  refine ⟨(random_alloc_scr h).congr (huw.trans hc.wr), husp.trans hc.sp,
    ?_, (random_frame_words (random_call_frameBytes h hf) (by decide)).trans hn, hpos, hbound⟩
  apply BitVec.eq_of_toNat_eq
  rw [hstatus]
  cases randomCallResult s t <;> rfl

theorem random_callArgs_observe (v : Backend) {s t : State} {h : RandomSignABI v.stack s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {used fuel k : Nat}
    (hr : RandomSignRunning h hq used fuel t)
    (hnonce : Spec.Rsa.bytesAt t.mem (off (randomBase s) Random.oNonce) (s.gpr .x6).toNat =
      Spec.Dsa.encodeBE (s.gpr .x6).toNat k) :
    WP isa (.block RandomSign.callArgs) t fun a =>
      RandomSignCallState h a ∧ randomCallResult s a = randomSingleResult s k ∧
      randomCallPublicKey s a = Spec.Dsa.publicBytesLeak (randomInput s).pLen (randomInput s).qLen (randomInput s).key ∧
      word a.mem (randomBase s) Random.oAttempts = BitVec.ofNat 64 fuel := by
  obtain ⟨cm, draws, hready⟩ := hr.ready
  refine WP.mono (random_callArgs_saved hready.scr hready.sp hr.saved)
    fun a ⟨hdi, hsi, hdx, hcx, h8, h9, h6, h7, hw, _, hargs, hka⟩ => ?_
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
  exact ⟨⟨hspA, hw, hdi, hsi, hdx, hcx, h8, h9, h6, h7, hka.rd.trans hr.rd, hka.wr.trans hr.wr⟩,
    hres, random_call_key_source h hspA hkeyA, hna⟩

end VG.Proof.Dsa.AArch64
