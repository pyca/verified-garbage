module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignAttempt
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignPublic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignPublic
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignAttempt
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCall
import VerifiedGarbage.Proof.Dsa.AArch64.CallFinishCT
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallMemory
import VerifiedGarbage.Proof.Dsa.AArch64.RandomMemory
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Impl.Dsa.AArch64.RandomSign
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignRetry
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Impl.Dsa.AArch64.RandomSign
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignRetry
meta import Mathlib.Algebra.Group.Nat.Defs
meta import Mathlib.Tactic.Attr.Core
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCall
meta import VerifiedGarbage.Proof.Dsa.AArch64.CallFinishCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallMemory
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomMemory
meta import VerifiedGarbage.Proof.Bignum.Octets

/-! ### `Dsa.AArch64.RandomSignCallObserve`, which only this module used -/

section

/-! ### `Dsa.AArch64.RandomSignRetryCT`, which only this module used -/

section

/-! Retry control reveals only the signer's low-word success bit and attempt budget. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

structure RandomRetryPublic where
  B : Addr
  success : Bool
  attempts : Nat

def RandomRetryPre (p : RandomRetryPublic) (s : State) : Prop :=
  Scr s p.B Random.frameBytes ∧ s.sp = p.B ∧
  (s.gpr .x0).setWidth 32 = (if p.success then 1 else 0) ∧
  word s.mem p.B Random.oAttempts = BitVec.ofNat 64 p.attempts ∧
  0 < p.attempts ∧ p.attempts < 2 ^ 64

def RandomRetryMid (p : RandomRetryPublic) (s : State) : Prop :=
  Scr s p.B Random.frameBytes ∧ s.sp = p.B ∧
  s.gpr .x0 = (if p.success then (1 : BitVec 64) else 0) ∧
  word s.mem p.B Random.oAttempts = BitVec.ofNat 64 p.attempts ∧
  0 < p.attempts ∧ p.attempts < 2 ^ 64

private theorem header_ok {p : RandomRetryPublic} {s : State} (h : RandomRetryPre p s) :
    WP isa (.block (([.ldrSp .x30 RandomSign.oLink, .logic .orr .w .x0 .x0 .x0] : List Instr) ++
      Random.store Random.oStatus .x0)) s (RandomRetryMid p) := by
  obtain ⟨hs, hsp, ha, hn, hp, hb⟩ := h
  refine WP.mono (random_retryHead_ok p.success hs hsp ha) fun t ⟨hm, hx, _, hk⟩ => ?_
  refine ⟨hs.congr hk.wr, hk.sp.trans hsp, hx, ?_, hp, hb⟩
  rw [hm, (writeW_outside _ p.B _ (by decide)).word (by decide) (by decide)]
  exact hn

private theorem decrement_ok {p : RandomRetryPublic} {s : State} (h : RandomRetryMid p s) :
    WP isa (.block (([.ldrSp .x0 Random.oAttempts, .subImm .x .x0 .x0 1] : List Instr) ++
      Random.store Random.oAttempts .x0)) s fun t =>
      t.sp = p.B ∧ t.gpr .x0 = BitVec.ofNat 64 (p.attempts - 1) := by
  obtain ⟨hs, hsp, _, hn, hp, hb⟩ := h
  exact WP.mono (random_attemptDecrement_ok hs hsp hn hp hb)
    (fun _ ⟨_, hx, hk⟩ => ⟨hk.sp.trans hsp, hx⟩)

theorem random_callFinish_ct : RelCT isa (Two RandomRetryPre) RandomSign.callFinish (fun _ _ => True) := by
  unfold RandomSign.callFinish
  refine RelCT.seq (two_piece (Ψ := RandomRetryMid) [] (by intro _ _ _ _ _ _ h; cases h)
    (by taint_decide) (fun _ _ h => header_ok h)) ?_
  refine two_ite (fun p s t hs ht => by simp only [eval, State.read, hs.2.2.1, ht.2.2.1]) ?_ ?_
  · refine RelCT.seq (two_piece (Ψ := fun p s => s.sp = p.B ∧
      s.gpr .x0 = BitVec.ofNat 64 (p.attempts - 1)) []
      (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)
      (fun _ _ h => decrement_ok h.1)) ?_
    refine two_ite (fun p s t hs ht => by simp only [eval, State.read, hs.2, ht.2]) ?_ ?_
    · exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)
    · exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)
  · exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)

end VG.Proof.Dsa.AArch64

end

end

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

end

end

/-! One complete signing call leaks its public key and success bit only. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_post_of_exec {c : Prog isa} {s t : State} {trace : List Leak} {Q : State → Prop}
    (h : WP isa c s Q) (he : Exec isa c s trace t) : Q t := by
  obtain ⟨_, u, hu, hq⟩ := h
  obtain ⟨_, heq⟩ := Exec.det he hu
  rw [heq]
  exact hq

theorem random_callArgs_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block RandomSign.callArgs) (fun _ _ => True) := by
  refine (two_taint (Φ := fun (B : Addr) s => s.sp = B) []
    (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)).mono
    (fun s _ h => ⟨s.sp, rfl, h.symm, h⟩) (fun _ _ _ => trivial)

theorem random_sign_single_agreement (S : Signer) {s t a b : State}
    {hs : RandomSignABI S.stack s} {ht : RandomSignABI S.stack t}
    (hvs : RandomValid S s) (hvt : RandomValid S t)
    {hqs : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {hqt : 1 < Spec.Dsa.decodeBE (randomQBytes t)}
    {used fuel k l : Nat} (ha : RandomSignRunning hs hqs used fuel a) (hb : RandomSignRunning ht hqt used fuel b)
    (hpub : RandomSignPublicAgree s t) (hf : 0 < fuel) (hbound : fuel < 2 ^ 64)
    (hna : Spec.Rsa.bytesAt a.mem (off (randomBase s) Random.oNonce) (s.gpr .x6).toNat = Spec.Dsa.encodeBE (s.gpr .x6).toNat k)
    (hnb : Spec.Rsa.bytesAt b.mem (off (randomBase t) Random.oNonce) (t.gpr .x6).toNat = Spec.Dsa.encodeBE (t.gpr .x6).toNat l)
    (hsuccess : (randomSingleResult s k).isSome = (randomSingleResult t l).isSome)
    {tsa tsb : List Leak} {u w : State}
    (ea : Exec isa (.seq (.block RandomSign.callArgs)
      (.seq (.call S.name S.code) RandomSign.callFinish)) a tsa u)
    (eb : Exec isa (.seq (.block RandomSign.callArgs)
      (.seq (.call S.name S.code) RandomSign.callFinish)) b tsb w) : tsa = tsb := by
  cases ea with
  | seq eaa ear => cases ear with
    | seq eac eaf =>
      cases eb with
      | seq eba ebr => cases ebr with
        | seq ebc ebf =>
          obtain ⟨_, _, hra⟩ := ha.ready
          obtain ⟨_, _, hrb⟩ := hb.ready
          have hargs := (random_callArgs_ct _ _ _ _ _ _
            (hra.sp.trans (hpub.base.trans hrb.sp.symm)) eaa eba).1
          obtain ⟨hca, hresa, hkeya, hfua⟩ := random_post_of_exec (random_callArgs_observe S ha hna) eaa
          obtain ⟨hcb, hresb, hkeyb, hfub⟩ := random_post_of_exec (random_callArgs_observe S hb hnb) eba
          have hstatus : Spec.Dsa.signStatus (randomSingleResult s k) = Spec.Dsa.signStatus (randomSingleResult t l) := by
            cases hsa : randomSingleResult s k <;> cases hsb : randomSingleResult t l <;>
              simp only [hsa, hsb, Option.isSome_none, Option.isSome_some] at hsuccess <;>
              first | contradiction | rfl
          have hcall := (random_signer_ct S _ _ _ _ _ _
            ⟨s, t, hs, ht, hvs, hvt, hca, hcb, hpub, hkeya.trans (hpub.keyLeak.trans hkeyb.symm), by rw [hresa, hresb]; exact hstatus⟩ eac ebc).1
          have hpa := random_post_of_exec (random_signer_retry_pre S hca hfua hf hbound hvs) eac
          have hpb := random_post_of_exec (random_signer_retry_pre S hcb hfub hf hbound hvt) ebc
          rw [hresa] at hpa
          rw [hresb, ← hpub.base, ← hsuccess] at hpb
          have hfinish := (random_callFinish_ct _ _ _ _ _ _ ⟨_, hpa, hpb, hpa.2.1.trans hpb.2.1.symm⟩ eaf ebf).1
          rw [hargs, hcall, hfinish]

end VG.Proof.Dsa.AArch64
