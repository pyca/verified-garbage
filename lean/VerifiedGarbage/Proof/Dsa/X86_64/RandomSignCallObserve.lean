module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallCT
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSingle
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignRetryCT
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedExp
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallValue
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignArgsSaved
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallMemory
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallGeometry
import VerifiedGarbage.Proof.Dsa.X86_64.RandomMemory
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset

/-! Observe call-boundary data without constraining the private nonce or digest. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem random_call_key_source {extra : Nat} {s t : State} (h : RandomSignABI extra s)
    (hsp : t.gpr .rsp = randomBase s)
    (hkey : Src t (randomBase s) Random.frameBytes (s.gpr .rcx) (randomInput s).key) :
    randomCallPublicKey s t = Spec.Dsa.publicBytesLeak (randomInput s).pLen (randomInput s).qLen (randomInput s).key := by
  have hsub : Region.Sub ⟨randomBase s - 8, 8⟩ (below (s.gpr .rsp) (extra + 256)) := by
    rw [random_callBase extra s]
    exact Offset.sub_base _ (by omega)
  have hm := random_callEntry_bytes hsp
    (((h.stackKey.sub_left hsub).symm).sep (Region.contains_self _ _) (Region.contains_self _ _)) (s.gpr .r8).isLt
  unfold randomCallPublicKey
  rw [hm]
  have hkb : Spec.Rsa.bytesAt t.mem (s.gpr .rcx) (s.gpr .r8).toNat = (randomInput s).key := by
    simpa only [randomInput, bytesAt_length] using FoldedPublic.src_bytesAt hkey
  rw [hkb]
  rfl

theorem random_signer_retry_pre (v : Backend) {s t : State} {fuel : Nat} {h : RandomSignABI v.stack s}
    (hc : RandomSignCallState h t)
    (hn : word t.mem (randomBase s) Random.oAttempts = BitVec.ofNat 64 fuel)
    (hpos : 0 < fuel) (hbound : fuel < 2 ^ 64) :
    WP isa (.call (randomSignerName v) (SignVerify.sign v.sq v.mul)) t
      (RandomRetryPre ⟨randomBase s, (randomCallResult s t).isSome, fuel⟩) := by
  refine WP.mono (random_signer_outcome v h hc.sp hc.args hc.di hc.si hc.dx hc.cx hc.r8 hc.r9 hc.rd hc.wr)
    fun u ⟨_, huw, huc, hf, hstatus, _, _⟩ => ?_
  refine ⟨(random_alloc_scr h).congr (huw.trans hc.wr), (huc .rsp (by decide)).trans hc.sp,
    ?_, (random_frame_words (random_call_frameBytes h hf) (by decide)).trans hn, hpos, hbound⟩
  apply BitVec.eq_of_toNat_eq
  rw [hstatus]
  cases randomCallResult s t <;> rfl

theorem random_callArgs_observe (v : Backend) {s t : State} {h : RandomSignABI v.stack s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {used fuel k : Nat}
    (hr : RandomSignRunning h hq used fuel t)
    (hnonce : Spec.Rsa.bytesAt t.mem (off (randomBase s) Random.oNonce) (stackArg s 0).toNat =
      Spec.Dsa.encodeBE (stackArg s 0).toNat k) :
    WP isa (.block RandomSign.callArgs) t fun a =>
      RandomSignCallState h a ∧ randomCallResult s a = randomSingleResult s k ∧
      randomCallPublicKey s a = Spec.Dsa.publicBytesLeak (randomInput s).pLen (randomInput s).qLen (randomInput s).key ∧
      word a.mem (randomBase s) Random.oAttempts = BitVec.ofNat 64 fuel := by
  obtain ⟨cm, draws, hready⟩ := hr.ready
  refine WP.mono_mx (by decide) (random_callArgs_saved hready.scr hready.sp hr.saved)
    fun a ⟨hdi, hsi, hdx, hcx, h8, h9, hw, _, hargs, hka⟩ _ => ?_
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
  exact ⟨⟨hspA, hw, hdi, hsi, hdx, hcx, h8, h9, hka.2.1.trans hr.rd, hka.2.2.trans hr.wr⟩,
    hres, random_call_key_source h hspA hkeyA, hna⟩

end VG.Proof.Dsa.X86_64
