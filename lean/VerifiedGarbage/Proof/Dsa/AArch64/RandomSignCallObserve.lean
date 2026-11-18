module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSingle
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignPublic
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCall
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignRetryCT
import VerifiedGarbage.Proof.Dsa.AArch64.CallFinishCT
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallMemory
import VerifiedGarbage.Proof.Dsa.AArch64.RandomMemory
import VerifiedGarbage.Proof.Bignum.Octets

/-! ### `Dsa.AArch64.RandomSignCallCT`, which only this module used -/

section

/-! Instantiate the supplied-nonce signer's leakage contract at a wrapper call. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

structure RandomSignCallState {extra : Nat} {s : State} (h : RandomSignABI extra s) (t : State) : Prop where
  sp : t.sp = randomBase s
  args : ∀ i < 3, word t.mem (randomBase s) (8 * i) = randomCallArg s i
  di : t.gpr .x0 = s.gpr .x0
  si : t.gpr .x1 = s.gpr .x1
  dx : t.gpr .x2 = s.gpr .x3
  cx : t.gpr .x3 = s.gpr .x4
  r8 : t.gpr .x4 = s.gpr .x5
  r9 : t.gpr .x5 = off (randomBase s) Random.oNonce
  x6 : t.gpr .x6 = s.gpr .x6
  x7 : t.gpr .x7 = s.gpr .x7
  rd : t.rd = s.rd
  wr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr
  key : Spec.Rsa.bytesAt t.mem (s.gpr .x3) (s.gpr .x4).toNat = (randomInput s).key

def randomCallPublicKey (s t : State) : List Nat :=
  Spec.Dsa.publicBytesLeak (s.gpr .x5).toNat (s.gpr .x6).toNat
    (Spec.Rsa.bytesAt t.callEntry.mem (s.gpr .x3) (s.gpr .x4).toNat)

theorem random_call_public {valid : Nat → Nat → List Byte → Bool} {extra : Nat} {s t a b : State}
    {hs : RandomSignABI extra s} {ht : RandomSignABI extra t}
    (ha : RandomSignCallState hs a) (hb : RandomSignCallState ht b) (hp : RandomSignPublicAgree s t)
    (hk : randomCallPublicKey s a = randomCallPublicKey t b)
    (hr : Spec.Dsa.signStatus (randomCallResult s a) = Spec.Dsa.signStatus (randomCallResult t b)) :
    (signContractWith valid abi extra).pub
      (a.callEntry.withRegions (randomCallRd s) (randomCallWr s))
      ((b.callEntry.withRegions (randomCallRd t) (randomCallWr t)).withDit
        (a.callEntry.withRegions (randomCallRd s) (randomCallWr s)).dit) := by
  have hA (i : Nat) (hi : i < 3) :
      stackArg (a.callEntry.withRegions (randomCallRd s) (randomCallWr s)) i = randomCallArg s i :=
    (random_call_stackArg ha.sp _ _ i).trans (ha.args i hi)
  have hB (i : Nat) (hi : i < 3) :
      stackArg (b.callEntry.withRegions (randomCallRd t) (randomCallWr t)) i = randomCallArg t i :=
    (random_call_stackArg hb.sp _ _ i).trans (hb.args i hi)
  sig_pub [signContractWith, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs]
  simp only [stackArg_withDit, ha.sp, hb.sp, ha.di, hb.di, ha.si, hb.si, ha.dx, hb.dx, ha.cx, hb.cx, ha.r8, hb.r8, ha.r9, hb.r9, ha.x6, hb.x6, ha.x7, hb.x7,
    hA 0 (by decide), hA 1 (by decide), hA 2 (by decide),
    hB 0 (by decide), hB 1 (by decide), hB 2 (by decide), randomCallArg]
  refine ⟨?_, ?_, hp.regs .x0 (by decide), hp.regs .x1 (by decide), hp.regs .x3 (by decide),
    hp.regs .x4 (by decide), hp.regs .x5 (by decide), ?_, hp.regs .x6 (by decide), hp.regs .x7 (by decide),
    hp.args 0 (by decide), hp.args 3 (by decide), hp.args 4 (by decide)⟩
  · rw [hp.base]
  · simp only [randomCallPublicKey, randomCallResult, State.callEntry] at hk hr
    rw [hk, hr]
  · rw [hp.base]

def RandomSignCallRelated (S : Signer) (a b : State) : Prop :=
  ∃ s t, ∃ hs : RandomSignABI S.stack s, ∃ ht : RandomSignABI S.stack t,
    RandomValid S s ∧ RandomValid S t ∧ RandomSignCallState hs a ∧ RandomSignCallState ht b ∧ RandomSignPublicAgree s t ∧
    randomCallPublicKey s a = randomCallPublicKey t b ∧
    Spec.Dsa.signStatus (randomCallResult s a) = Spec.Dsa.signStatus (randomCallResult t b)

theorem random_signer_ct (S : Signer) : RelCT isa (RandomSignCallRelated S)
    (.call S.name S.code) (fun _ _ => True) := by
  apply VG.AArch64.RelCT.callExDit S.verified.1 S.verified.2.1 S.noDit (fun _ _ h => h)
  intro a b ⟨s, t, hs, ht, hvs, hvt, ha, hb, hp, hk, hr⟩
  obtain ⟨hca, hwa⟩ := random_call_covers hs ha.rd ha.wr
  obtain ⟨hcb, hwb⟩ := random_call_covers ht hb.rd hb.wr
  exact ⟨randomCallRd s, randomCallWr s, randomCallRd t, randomCallWr t,
    random_call_pre_with S hs ha.sp ha.args ha.di ha.si ha.dx ha.cx ha.r8 ha.r9 ha.x6 ha.x7 ha.key hvs,
    random_call_pre_with S ht hb.sp hb.args hb.di hb.si hb.dx hb.cx hb.r8 hb.r9 hb.x6 hb.x7 hb.key hvt,
    random_call_public ha hb hp hk hr, hca, hwa, hcb, hwb⟩

end VG.Proof.Dsa.AArch64

end

end


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

theorem random_signer_retry_pre (S : Signer) {s t : State} {fuel : Nat} {h : RandomSignABI S.stack s}
    (hc : RandomSignCallState h t)
    (hn : word t.mem (randomBase s) Random.oAttempts = BitVec.ofNat 64 fuel)
    (hpos : 0 < fuel) (hbound : fuel < 2 ^ 64) (hv : RandomValid S s) :
    WP isa (.call S.name S.code) t
      (RandomRetryPre ⟨randomBase s, (randomCallResult s t).isSome, fuel⟩) := by
  refine WP.mono (random_signer_outcome S h hc.sp hc.args hc.di hc.si hc.dx hc.cx hc.r8 hc.r9 hc.x6 hc.x7 hc.rd hc.wr hc.key hv)
    fun u ⟨_, huw, husp, _, hf, hstatus, _, _⟩ => ?_
  refine ⟨(random_alloc_scr h).congr (huw.trans hc.wr), husp.trans hc.sp,
    ?_, (random_frame_words (random_call_frameBytes h hf) (by decide)).trans hn, hpos, hbound⟩
  apply BitVec.eq_of_toNat_eq
  rw [hstatus]
  cases randomCallResult s t <;> rfl

theorem random_callArgs_observe (S : Signer) {s t : State} {h : RandomSignABI S.stack s}
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
    omega_using [hl]
  have hkeyA' : Spec.Rsa.bytesAt a.mem (s.gpr .x3) (s.gpr .x4).toNat = (randomInput s).key := by
    simpa only [randomInput, bytesAt_length] using sourceBytes_eq hkeyA
  have hres : randomCallResult s a = randomSingleResult s k := by
    rw [random_callResult_plain h hspA]
    have hkey := hkeyA'
    have hdigest : Spec.Rsa.bytesAt a.mem (s.gpr .x7) (stackArg s 0).toNat = (randomInput s).digest := by
      simpa only [randomInput, bytesAt_length] using sourceBytes_eq hdigestA
    have hnonceA := (random_outside_bytes hargs
      (show Random.oNonce + (s.gpr .x6).toNat ≤ 2 ^ 64 by unfold Random.oNonce; omega_using [hqbound])
      (Or.inr (show 0 + 40 ≤ Random.oNonce by decide))).trans hnonce
    rw [hkey, hdigest, hnonceA]
    rfl
  have hna : word a.mem (randomBase s) Random.oAttempts = BitVec.ofNat 64 fuel :=
    (hargs.word (by decide) (by decide)).trans hr.attempts
  exact ⟨⟨hspA, hw, hdi, hsi, hdx, hcx, h8, h9, h6, h7, hka.rd.trans hr.rd, hka.wr.trans hr.wr, hkeyA'⟩,
    hres, random_call_key_source h hspA hkeyA, hna⟩

end VG.Proof.Dsa.AArch64
