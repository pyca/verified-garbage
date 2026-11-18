module

public import VerifiedGarbage.Impl.Dsa.AArch64.RandomSign
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCall
public import VerifiedGarbage.Spec.Dsa.RandomSign
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignAttempt
public import VerifiedGarbage.Proof.Dsa.AArch64.PrevalidatedSignVerified
public import VerifiedGarbage.Proof.Dsa.SignContractWith
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFrame
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCode
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignPublic
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFinishAgreement
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSingleCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCall
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignPublic
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFinishAgreement
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSingleCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCode
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignEnv
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomPrepareCT
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignEnv
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomPrepareCT
meta import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignRunning
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSampleLoop
import VerifiedGarbage.Proof.Dsa.RandomSignTrace
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignRunning
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSampleLoop
meta import VerifiedGarbage.Proof.Dsa.RandomSignTrace
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignAttempt
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSampleAgreement
import VerifiedGarbage.Proof.Dsa.RandomTraceResult
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSampleAgreement
meta import VerifiedGarbage.Proof.Dsa.RandomTraceResult
meta import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.RandomSignTraceResult
meta import VerifiedGarbage.Proof.Dsa.RandomSignTraceResult

/-! ### `Dsa.AArch64.RandomSignInvalidCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.RandomSignBodyCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.RandomSignLoopCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.RandomSignStep`, which only this module used -/

section

/-! Public status and continuation facts after one signing attempt. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def RandomSignStepPost {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)) (used fuel : Nat) (t : State) : Prop :=
  (∃ remaining, RandomSignRunning h hq (used + (randomSignDraw (randomInput s) used).used) remaining t) ∧
  word t.mem (randomBase s) Random.oStatus = BitVec.ofNat 64 (randomSignAttemptStatus (randomInput s) used fuel) ∧
  (randomSignAttemptStatus (randomInput s) used fuel = 4 →
    RandomSignRunning h hq (used + (randomSignDraw (randomInput s) used).used) (fuel - 1) t)

theorem random_sign_step (S : Signer) {s t : State} {h : RandomSignABI S.stack s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {used fuel : Nat}
    (hr : RandomSignRunning h hq used fuel t) (hf : 0 < fuel) (hb : fuel < 2 ^ 64) (hval : RandomValid S s) :
    WP isa (RandomSign.attempt S.name S.code) t (RandomSignStepPost h hq used fuel) := by
  refine WP.mono (random_sign_attempt S hr hf hb hval) fun u hu => ?_
  cases hd : (randomSignDraw (randomInput s) used).scalar with
  | none =>
    simp only [RandomSignAttemptPost, hd] at hu
    obtain ⟨hr', hs⟩ := hu
    refine ⟨⟨fuel, hr'⟩, ?_, ?_⟩
    · simpa only [randomSignAttemptStatus, hd] using hs
    · intro he
      obtain ⟨_, k, hk, _⟩ := random_sign_attempt_continue hf he
      rw [hd] at hk
      contradiction
  | some k =>
    simp only [RandomSignAttemptPost, hd] at hu
    obtain ⟨hr', hs, _⟩ := hu
    refine ⟨⟨_, hr'⟩, ?_, ?_⟩
    · unfold randomSignAttemptStatus
      rw [hd]
      change word u.mem (randomBase s) Random.oStatus =
        BitVec.ofNat 64 (if (randomSingleResult s k).isSome then 1 else if fuel = 1 then 0 else 4)
      cases hk : (randomSingleResult s k).isSome <;> by_cases hn : fuel = 1 <;>
        simp only [hk, hn, Bool.false_eq_true, ite_true, ite_false] at hs ⊢ <;> exact hs
    · intro he
      obtain ⟨_, l, hl, hsign⟩ := random_sign_attempt_continue hf he
      rw [hd, Option.some.injEq] at hl
      subst l
      change randomSingleResult s k = none at hsign
      simpa only [hsign, Option.isSome_none, Bool.false_eq_true, ite_false] using hr'

theorem RandomSignStepPost.congr {extra : Nat} {s t u : State} {h : RandomSignABI extra s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {used fuel : Nat}
    (hp : RandomSignStepPost h hq used fuel t) (hm : u.mem = t.mem)
    (hk : Keep [.x0, .x4] t u) : RandomSignStepPost h hq used fuel u := by
  obtain ⟨⟨remaining, hr⟩, hs, hc⟩ := hp
  exact ⟨⟨remaining, hr.congr hm hk⟩, by rw [hm]; exact hs, fun hh => (hc hh).congr hm hk⟩

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.RandomSignAttemptCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.RandomSignSampleCT`, which this module and modules that import it used -/

section

/-! Transfer public argument and trace agreement to the complete nonce sampler. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

theorem random_sign_draw_agree {s t : State} {used : Nat} (hpub : RandomSignPublicAgree s t)
    (htrace : (randomSignDraw (randomInput s) used).trace = (randomSignDraw (randomInput t) used).trace) :
    (randomSignDraw (randomInput s) used).used = (randomSignDraw (randomInput t) used).used ∧
      (randomSignDraw (randomInput s) used).scalar.isSome = (randomSignDraw (randomInput t) used).scalar.isSome ∧
      Random.sampleStatus (randomSignDraw (randomInput s) used) = Random.sampleStatus (randomSignDraw (randomInput t) used) := by
  have hq : (Spec.Dsa.privateKeyBytes (randomInput s).pLen (randomInput s).qLen (randomInput s).key).params.q =
      (Spec.Dsa.privateKeyBytes (randomInput t).pLen (randomInput t).qLen (randomInput t).key).params.q := by
    rw [← random_q_decode, ← random_q_decode, hpub.qbytes]
  unfold randomSignDraw at htrace ⊢
  rw [hq] at htrace ⊢
  exact Random.sample_trace_agree htrace

theorem random_sign_sample_agreement {extra : Nat} {s t a b : State}
    {hs : RandomSignABI extra s} {ht : RandomSignABI extra t}
    {hqs : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {hqt : 1 < Spec.Dsa.decodeBE (randomQBytes t)}
    {used fuel : Nat} (ha : RandomSignRunning hs hqs used fuel a) (hb : RandomSignRunning ht hqt used fuel b)
    (hpub : RandomSignPublicAgree s t)
    (htrace : (randomSignDraw (randomInput s) used).trace = (randomSignDraw (randomInput t) used).trace)
    {tsa tsb : List Leak} {u w : State} (ea : Exec isa Random.sample a tsa u) (eb : Exec isa Random.sample b tsb w) :
    tsa = tsb := by
  obtain ⟨ma, da, hra⟩ := ha.ready
  obtain ⟨mb, db, hrb⟩ := hb.ready
  apply random_sample_agreement hra hrb hqs hpub.base (hpub.args 1 (by decide)) _ hpub.qbytes _ _ ea eb
  · change s.gpr .x3 + s.gpr .x5 = t.gpr .x3 + t.gpr .x5
    rw [hpub.regs .x3 (by decide), hpub.regs .x5 (by decide)]
  · simp only [randomContextOf, randomInput, bytesAt_length, hpub.args 2 (by decide)]
  · change (Spec.Dsa.Random.sample (Spec.Dsa.decodeBE (randomQBytes s)) 128 ((randomInput s).rand.drop used)).trace =
      (Spec.Dsa.Random.sample (Spec.Dsa.decodeBE (randomQBytes t)) 128 ((randomInput t).rand.drop used)).trace
    rw [random_q_decode, random_q_decode]
    exact htrace

end VG.Proof.Dsa.AArch64

end

end

/-! A complete signing attempt leaks only its specified sampling and signing markers. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

private theorem cmp_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block [.subImm .x .x4 .x0 1]) (fun _ _ => True) := by
  exact (two_taint (Φ := fun (_ : Unit) (_ : State) => True) []
    (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)).mono
    (fun _ _ h => ⟨(), trivial, trivial, h⟩) (fun _ _ _ => trivial)

private theorem some_of_status {draw : Spec.Dsa.Random.Sample}
    (h : (BitVec.ofNat 64 (Random.sampleStatus draw) == 1) = true) : ∃ k, draw.scalar = some k := by
  cases hc : draw.scalar with
  | some k => exact ⟨k, rfl⟩
  | none =>
    simp only [Random.sampleStatus, hc] at h
    split at h <;> contradiction

theorem random_sign_attempt_agreement (S : Signer) {s t a b : State}
    {hs : RandomSignABI S.stack s} {ht : RandomSignABI S.stack t}
    (hvs : RandomValid S s) (hvt : RandomValid S t)
    {hqs : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {hqt : 1 < Spec.Dsa.decodeBE (randomQBytes t)}
    {used fuel : Nat} (ha : RandomSignRunning hs hqs used (fuel + 1) a)
    (hb : RandomSignRunning ht hqt used (fuel + 1) b)
    (hpub : RandomSignPublicAgree s t) (hbound : fuel + 1 < 2 ^ 64)
    (htrace : (randomSignRemaining (randomInput s) used (fuel + 1)).trace =
      (randomSignRemaining (randomInput t) used (fuel + 1)).trace)
    {tsa tsb : List Leak} {u w : State}
    (ea : Exec isa (RandomSign.attempt S.name S.code) a tsa u)
    (eb : Exec isa (RandomSign.attempt S.name S.code) b tsb w) : tsa = tsb := by
  have hdraw := congrArg randomSamplingTrace htrace
  rw [random_sign_trace_draw, random_sign_trace_draw] at hdraw
  obtain ⟨hused, _, hstatus⟩ := random_sign_draw_agree hpub hdraw
  cases ea with
  | seq eas ear => cases ear with
    | seq eac eai =>
      cases eb with
      | seq ebs ebr => cases ebr with
        | seq ebc ebi =>
          have hsample := random_sign_sample_agreement ha hb hpub hdraw eas ebs
          obtain ⟨haa, _, har, hna⟩ := random_post_of_exec (random_sign_sample ha) eas
          obtain ⟨hba, _, hbr, hnb⟩ := random_post_of_exec (random_sign_sample hb) ebs
          obtain ⟨⟨ham, haz⟩, hka⟩ := random_post_of_exec
            random_sign_test_one eac
          obtain ⟨⟨hbm, hbz⟩, hkb⟩ := random_post_of_exec
            random_sign_test_one ebc
          obtain ⟨_, _, hra⟩ := har.ready
          obtain ⟨_, _, hrb⟩ := hbr.ready
          have hcmp := (cmp_ct _ _ _ _ _ _ (hra.sp.trans (hpub.base.trans hrb.sp.symm)) eac ebc).1
          have har' := har.congr ham hka
          have hbr' := hbr.congr hbm hkb
          rw [haa] at haz
          rw [hba] at hbz
          cases eai with
          | iteT hca eata =>
            cases ebi with
            | iteT hcb ebtb =>
              change some ((_ : State).gpr .x4 == 0#64) = some _ at hca
              rw [haz] at hca
              simp only [Option.some.injEq] at hca
              change some ((_ : State).gpr .x4 == 0#64) = some _ at hcb
              rw [hbz] at hcb
              simp only [Option.some.injEq] at hcb
              obtain ⟨k, hk⟩ := some_of_status hca
              obtain ⟨l, hl⟩ := some_of_status hcb
              have hsucc := random_sign_trace_call htrace hk hl
              have hnoncea := hna k hk
              have hnonceb := hnb l hl
              rw [← ham] at hnoncea
              rw [← hbm] at hnonceb
              rw [← hused] at hbr'
              have hsingle := random_sign_single_agreement S hvs hvt har' hbr' hpub (by omega_using []) hbound
                hnoncea hnonceb hsucc eata ebtb
              rw [hsample, hcmp, hsingle]
            | iteF hcb _ =>
              change some ((_ : State).gpr .x4 == 0#64) = some _ at hca
              rw [haz] at hca
              simp only [Option.some.injEq, hstatus] at hca
              change some ((_ : State).gpr .x4 == 0#64) = some _ at hcb
              rw [hbz] at hcb
              simp only [Option.some.injEq] at hcb
              rw [hca] at hcb
              contradiction
          | iteF hca eata =>
            cases ebi with
            | iteT hcb _ =>
              change some ((_ : State).gpr .x4 == 0#64) = some _ at hca
              rw [haz] at hca
              simp only [Option.some.injEq, hstatus] at hca
              change some ((_ : State).gpr .x4 == 0#64) = some _ at hcb
              rw [hbz] at hcb
              simp only [Option.some.injEq] at hcb
              rw [hca] at hcb
              contradiction
            | iteF _ ebtb =>
              have hnil := (RelCT.block_nil (P := fun _ _ => True) (fun _ _ _ => True.intro)
                _ _ _ _ _ _ trivial eata ebtb).1
              rw [hsample, hcmp, hnil]

end VG.Proof.Dsa.AArch64

end

end

/-! The outer retry loop reveals the sampling and signing decisions specified by its trace. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def randomSignStatusTest : Prog isa := .block (Random.statusTest 4)

private theorem status_ct : RelCT isa (fun s t => s.sp = t.sp)
    randomSignStatusTest (fun _ _ => True) := by
  exact (two_taint (Φ := fun (_ : Unit) (_ : State) => True) []
    (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)).mono
    (fun _ _ h => ⟨(), trivial, trivial, h⟩) (fun _ _ _ => trivial)

def RandomSignLoopAgree {extra : Nat} {s t : State} (hs : RandomSignABI extra s) (ht : RandomSignABI extra t)
    (hqs : 1 < Spec.Dsa.decodeBE (randomQBytes s)) (hqt : 1 < Spec.Dsa.decodeBE (randomQBytes t))
    (fuel : Nat) (a b : State) : Prop :=
  0 < fuel ∧ fuel ≤ 8 ∧ ∃ used, RandomSignRunning hs hqs used fuel a ∧ RandomSignRunning ht hqt used fuel b ∧
    (randomSignRemaining (randomInput s) used fuel).trace = (randomSignRemaining (randomInput t) used fuel).trace

theorem random_sign_loop_ct (S : Signer) {s t : State}
    {hs : RandomSignABI S.stack s} {ht : RandomSignABI S.stack t}
    {hqs : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {hqt : 1 < Spec.Dsa.decodeBE (randomQBytes t)}
    (hpub : RandomSignPublicAgree s t) (hvs : RandomValid S s) (hvt : RandomValid S t) (fuel : Nat) :
    RelCT isa (RandomSignLoopAgree hs ht hqs hqt fuel)
      (.loop (.seq (RandomSign.attempt S.name S.code) randomSignStatusTest) (.zero .x .x4))
      (fun _ _ => True) := by
  refine RelCT.loop (M := isa) (RandomSignLoopAgree hs ht hqs hqt) ?_ fuel
  intro n a b tsa tsb u w ⟨hf, hn, used, ha, hb, htrace⟩ ea eb
  cases n with
  | zero => omega
  | succ n =>
    have hdraw := congrArg randomSamplingTrace htrace
    rw [random_sign_trace_draw, random_sign_trace_draw] at hdraw
    obtain ⟨hused, hscalar, hsampleStatus⟩ := random_sign_draw_agree hpub hdraw
    have hstatus := random_sign_attempt_status_agree htrace hscalar hsampleStatus
    cases ea with
    | seq eaa eat =>
      cases eb with
      | seq eba ebt =>
        have hattempt := random_sign_attempt_agreement S hvs hvt ha hb hpub (by omega_using [hn]) htrace eaa eba
        have hpa := random_post_of_exec (random_sign_step S ha (by omega_using []) (by omega_using [hn]) hvs) eaa
        have hpb := random_post_of_exec (random_sign_step S hb (by omega_using []) (by omega_using [hn]) hvt) eba
        obtain ⟨_, hrunA⟩ := hpa.1
        obtain ⟨_, hrunB⟩ := hpb.1
        obtain ⟨_, _, hra⟩ := hrunA.ready
        obtain ⟨_, _, hrb⟩ := hrunB.ready
        have htest := (status_ct _ _ _ _ _ _ (hra.sp.trans (hpub.base.trans hrb.sp.symm)) eat ebt).1
        obtain ⟨hza, hma, hka⟩ := random_post_of_exec (random_statusTest_ok hra.scr hra.sp hpa.2.1) eat
        obtain ⟨hzb, hmb, hkb⟩ := random_post_of_exec (random_statusTest_ok hrb.scr hrb.sp hpb.2.1) ebt
        have hpa' := hpa.congr hma hka
        have hpb' := hpb.congr hmb hkb
        refine ⟨by rw [hattempt, htest], ?_, fun _ => trivial, ?_⟩
        · change some (u.gpr .x4 == 0#64) = some (w.gpr .x4 == 0#64)
          rw [hza, hzb, hstatus]
        · intro hc
          have hfour : randomSignAttemptStatus (randomInput s) used (n + 1) = 4 := by
            change some (u.gpr .x4 == 0#64) = some true at hc
            rw [hza] at hc
            simp only [Option.some.injEq, beq_iff_eq] at hc
            have hv := congrArg BitVec.toNat hc
            have hh := random_sign_attempt_status_bound (randomInput s) used (n + 1)
            change randomSignAttemptStatus (randomInput s) used (n + 1) % 2 ^ 64 = 4 at hv
            omega_using [hh, hv]
          have hfourB : randomSignAttemptStatus (randomInput t) used (n + 1) = 4 := hstatus.symm.trans hfour
          have hnext := random_sign_attempt_next_trace htrace hfour hfourB
          obtain ⟨hf', _⟩ := random_sign_attempt_continue (by omega_using []) hfour
          have ha' := hpa'.2.2 hfour
          have hb' := hpb'.2.2 hfourB
          simp only [Nat.add_sub_cancel] at ha' hb'
          rw [← hused] at hb' hnext
          exact ⟨n, by omega_using [], by omega_using [hf'], by omega_using [hn], used + (randomSignDraw (randomInput s) used).used,
            ha', hb', hnext⟩

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.RandomSignInitCT`, which only this module used -/

section

/-! Saving arguments and preparing q leaks no private key or random-tape bytes. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def RandomSignInitPre (p : RandomPreparePublic) (t : State) : Prop :=
  ∃ s extra, RandomSignABI extra s ∧ t = allocated Random.frameBytes s ∧
    p = ⟨randomBase s, s.gpr .x3 + s.gpr .x5, randomQBytes s⟩

private theorem entry_prepare {p : RandomPreparePublic} {t : State} (hp : RandomSignInitPre p t) :
    WP isa (.block RandomSign.entry) t (RandomPreparePre p) := by
  obtain ⟨s, extra, h, rfl, rfl⟩ := hp
  have hsp : (allocated Random.frameBytes s).sp = randomBase s := rfl
  refine WP.mono (random_entry_ok (random_alloc_scr h) hsp (random_incoming_read h))
    fun u ⟨hum, hk⟩ => ?_
  have hsaved : RandomSaved s u.mem := by rw [hum]; exact random_saved_entry s
  have hf : InScr (randomBase s) Random.frameBytes (allocated Random.frameBytes s).mem u.mem := by
    rw [hum]; exact InScr.of_outside (random_entry_outside _ _) (by decide)
  have hv (p : Nat × BitVec 64) (hp : p ∈ randomEntryValues (allocated Random.frameBytes s) (randomBase s)) :
      word u.mem (randomBase s) p.1 = p.2 := by
    rw [hum]; exact random_entry_values _ _ p hp
  have hqu : word u.mem (randomBase s) Random.oQ = s.gpr .x3 + s.gpr .x5 :=
    hv (168, s.gpr .x3 + s.gpr .x5) (by simp [randomEntryValues, allocated])
  have hql : word u.mem (randomBase s) Random.oQLen = BitVec.ofNat 64 (randomQBytes s).length := by
    simpa only [Random.oQLen, random_q_length h, ofNat_toNat64] using
      hsaved (88, s.gpr .x6) (by simp [randomSavedValues])
  refine ⟨(random_alloc_scr h).congr hk.wr, hk.sp.trans hsp,
    hqu, hql, (random_initial_q h).congrK hf hk, ?_, ?_⟩
  · change 0 < (randomQBytes s).length
    rw [random_q_length h]
    have hl := h.lengths
    unfold Spec.Dsa.lengthsValid at hl
    omega_using [hl]
  · change (randomQBytes s).length < 2 ^ 64
    rw [random_q_length h]
    exact (s.gpr .x6).isLt

theorem random_sign_init_ct : RelCT isa (Two RandomSignInitPre)
    (.seq (.block RandomSign.entry) Random.prepare) (fun _ _ => True) := by
  refine RelCT.seq (two_piece (Ψ := RandomPreparePre) [] ?_ (by taint_decide)
    (fun _ _ h => entry_prepare h)) random_prepare_ct
  intro _ _ _ _ _ _ h; cases h

end VG.Proof.Dsa.AArch64

end

end

/-! Compose initialization, retries, and publication for valid subgroup moduli. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_sign_init_agreement {extra : Nat} {s t : State}
    (hs : RandomSignABI extra s) (ht : RandomSignABI extra t) (hp : RandomSignPublicAgree s t)
    {tsa tsb : List Leak} {u w : State}
    (ea : Exec isa (.seq (.block RandomSign.entry) Random.prepare) (allocated Random.frameBytes s) tsa u)
    (eb : Exec isa (.seq (.block RandomSign.entry) Random.prepare) (allocated Random.frameBytes t) tsb w) : tsa = tsb := by
  have he : (⟨randomBase s, s.gpr .x3 + s.gpr .x5, randomQBytes s⟩ : RandomPreparePublic) =
      ⟨randomBase t, t.gpr .x3 + t.gpr .x5, randomQBytes t⟩ := by
    rw [hp.base, hp.regs .x3 (by decide), hp.regs .x5 (by decide), hp.qbytes]
  exact (random_sign_init_ct _ _ _ _ _ _
    ⟨_, ⟨s, extra, hs, rfl, rfl⟩, ⟨t, extra, ht, rfl, he⟩, hp.base⟩ ea eb).1

def randomSignTail (S : Signer) : Prog isa :=
  .seq (.ite (.zero .x .x0) (.block (Random.store Random.oStatus .x0))
    (.loop (.seq (RandomSign.attempt S.name S.code) randomSignStatusTest)
      (.zero .x .x4))) RandomSign.finish

private theorem valid_tail (S : Signer) {s t a b : State}
    {hs : RandomSignABI S.stack s} {ht : RandomSignABI S.stack t}
    {hqs : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {hqt : 1 < Spec.Dsa.decodeBE (randomQBytes t)}
    (ha : RandomSignRunning hs hqs 0 8 a) (hb : RandomSignRunning ht hqt 0 8 b)
    (hra : a.gpr .x0 = 1) (hrb : b.gpr .x0 = 1) (hp : RandomSignPublicAgree s t)
    (htrace : (randomSignRemaining (randomInput s) 0 8).trace = (randomSignRemaining (randomInput t) 0 8).trace)
    (hstatus : (randomSignRemaining (randomInput s) 0 8).status = (randomSignRemaining (randomInput t) 0 8).status)
    (hvs : RandomValid S s) (hvt : RandomValid S t)
    {tsa tsb : List Leak} {u w : State} (ea : Exec isa (randomSignTail S) a tsa u)
    (eb : Exec isa (randomSignTail S) b tsb w) : tsa = tsb := by
  cases ea with
  | seq eai eaf =>
    cases eb with
    | seq ebi ebf =>
      cases eai with
      | iteT hc _ => simp [eval, State.read, hra] at hc
      | iteF _ eal =>
        cases ebi with
        | iteT hc _ => simp [eval, State.read, hrb] at hc
        | iteF _ ebl =>
          have hloop := (random_sign_loop_ct S hp hvs hvt 8 _ _ _ _ _ _
            ⟨by decide, by decide, 0, ha, hb, htrace⟩ eal ebl).1
          obtain ⟨⟨_, hrunA⟩, hsta, _⟩ := random_post_of_exec (random_sign_loop_correct S ha (by decide) (by decide) hvs) eal
          obtain ⟨⟨_, hrunB⟩, hstb, _⟩ := random_post_of_exec (random_sign_loop_correct S hb (by decide) (by decide) hvt) ebl
          rw [← hstatus] at hstb
          have hfinish := random_finish_agreement hs ht hrunA.finishPre hrunB.finishPre hp hsta hstb eaf ebf
          rw [hloop, hfinish]

theorem random_sign_body_valid_ct (S : Signer) {s t : State}
    (hs : RandomSignABI S.stack s) (ht : RandomSignABI S.stack t) (hp : RandomSignPublicAgree s t)
    (hvs : RandomValid S s) (hvt : RandomValid S t)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s))
    (htrace : (randomSignRemaining (randomInput s) 0 8).trace = (randomSignRemaining (randomInput t) 0 8).trace)
    (hstatus : (randomSignRemaining (randomInput s) 0 8).status = (randomSignRemaining (randomInput t) 0 8).status)
    {tsa tsb : List Leak} {u w : State}
    (ea : Exec isa (RandomSign.body S.name S.code) (allocated Random.frameBytes s) tsa u)
    (eb : Exec isa (RandomSign.body S.name S.code) (allocated Random.frameBytes t) tsb w) : tsa = tsb := by
  have hqt : 1 < Spec.Dsa.decodeBE (randomQBytes t) := by rw [← hp.qbytes]; exact hq
  cases ea with
  | seq eae ear => cases ear with
    | seq eap eat =>
      cases eb with
      | seq ebe ebr => cases ebr with
        | seq ebp ebt =>
          have hinit := random_sign_init_agreement hs ht hp (.seq eae eap) (.seq ebe ebp)
          obtain ⟨hra, har⟩ := random_post_of_exec (random_sign_init_running hs hq) (.seq eae eap)
          obtain ⟨hrb, hbr⟩ := random_post_of_exec (random_sign_init_running ht hqt) (.seq ebe ebp)
          have htail := valid_tail S har hbr hra hrb hp htrace hstatus hvs hvt eat ebt
          rw [← List.append_assoc, ← List.append_assoc, hinit, htail]

end VG.Proof.Dsa.AArch64

end

end

/-! Rejection before sampling has a fixed schedule for the same public arguments. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

private theorem invalid_store_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block (Random.store Random.oStatus .x0)) (fun _ _ => True) := by
  exact (two_taint (Φ := fun (_ : Unit) (_ : State) => True) []
    (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)).mono
    (fun _ _ h => ⟨(), trivial, trivial, h⟩) (fun _ _ _ => trivial)

private theorem invalid_tail (S : Signer) {s t a b : State}
    (hs : RandomSignABI S.stack s) (ht : RandomSignABI S.stack t)
    (ha : RandomSignFinishPre s 0 a) (hb : RandomSignFinishPre t 0 b)
    (hra : a.gpr .x0 = 0) (hrb : b.gpr .x0 = 0) (hp : RandomSignPublicAgree s t)
    {tsa tsb : List Leak} {u w : State} (ea : Exec isa (randomSignTail S) a tsa u)
    (eb : Exec isa (randomSignTail S) b tsb w) : tsa = tsb := by
  cases ea with
  | seq eai eaf =>
    cases eb with
    | seq ebi ebf =>
      cases eai with
      | iteF hc _ => simp [eval, State.read, hra] at hc
      | iteT _ east =>
        cases ebi with
        | iteF hc _ => simp [eval, State.read, hrb] at hc
        | iteT _ ebst =>
          have hstore := (invalid_store_ct _ _ _ _ _ _
            (ha.sp.trans (hp.base.trans hb.sp.symm)) east ebst).1
          obtain ⟨hfa, hsa⟩ := random_post_of_exec (random_sign_invalid_store ha hra) east
          obtain ⟨hfb, hsb⟩ := random_post_of_exec (random_sign_invalid_store hb hrb) ebst
          have hfinish := random_finish_agreement hs ht hfa hfb hp hsa hsb eaf ebf
          rw [hstore, hfinish]

theorem random_sign_body_invalid_ct (S : Signer) {s t : State}
    (hs : RandomSignABI S.stack s) (ht : RandomSignABI S.stack t) (hp : RandomSignPublicAgree s t)
    (hq : ¬ 1 < Spec.Dsa.decodeBE (randomQBytes s))
    {tsa tsb : List Leak} {u w : State}
    (ea : Exec isa (RandomSign.body S.name S.code) (allocated Random.frameBytes s) tsa u)
    (eb : Exec isa (RandomSign.body S.name S.code) (allocated Random.frameBytes t) tsb w) : tsa = tsb := by
  have hqt : ¬ 1 < Spec.Dsa.decodeBE (randomQBytes t) := by rw [← hp.qbytes]; exact hq
  cases ea with
  | seq eae ear => cases ear with
    | seq eap eat =>
      cases eb with
      | seq ebe ebr => cases ebr with
        | seq ebp ebt =>
          have hinit := random_sign_init_agreement hs ht hp (.seq eae eap) (.seq ebe ebp)
          obtain ⟨hra, har⟩ := random_post_of_exec (random_sign_init_invalid hs hq) (.seq eae eap)
          obtain ⟨hrb, hbr⟩ := random_post_of_exec (random_sign_init_invalid ht hqt) (.seq ebe ebp)
          have htail := invalid_tail S hs ht har hbr hra hrb hp eat ebt
          rw [← List.append_assoc, ← List.append_assoc, hinit, htail]

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.RandomSignCorrect`, which only this module used -/

section

/-! Randomized signing's functional correctness against its shared contract. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_sign_shared_post {extra : Nat} {s t : State} (h : RandomSignABI extra s)
    (hp : RandomSignCodePost s (randomSignRemaining (randomInput s) 0 8) t) :
    (randomSignCheckedContract abi (extra + 256)).post s t := by
  sig_post [randomSignCheckedContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs]
  sig_post [randomSignCheckedContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs]
  have he := random_remaining_bytes h
  have hb : (randomSignRemaining (randomInput s) 0 8).status < 2 ^ 32 := by
    have := randomSignLoop_status_le (randomInput s).pLen (randomInput s).qLen 8
      (randomInput s).key (randomInput s).digest ((randomInput s).rand.drop 0)
    change (randomSignRemaining (randomInput s) 0 8).status ≤ 2 at this
    omega_using [this]
  refine ⟨?_, ?_, ?_⟩
  · rw [hp.status]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64),
      Nat.mod_eq_of_lt hb]
    exact congrArg Spec.Dsa.RandomSignResult.status he
  · exact (hp.output.trans (congrArg (fun r : Spec.Dsa.RandomSignResult => r.signature.getD
      (List.replicate (s.gpr .x1).toNat 0)) he))
  · change Spec.Rsa.wordsAt t.mem (s.gpr .x2) 1 = _
    simp only [Spec.Rsa.wordsAt, List.range_succ, List.range_zero, List.nil_append,
      List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero, hp.used]
    exact congrArg (fun r : Spec.Dsa.RandomSignResult => [BitVec.ofNat 64 r.used]) he

theorem random_sign_correct (S : Signer) (s : State)
    (hpre : (randomSignCheckedContract abi (S.stack + 256)).pre s) (hval : RandomValid S s) :
    ∃ trace t, Exec isa (RandomSign.code S.name S.code) s trace t ∧
      abiPreserved s t ∧ (randomSignCheckedContract abi (S.stack + 256)).post s t := by
  have h := randomSignABI_of hpre
  obtain ⟨trace, t, he, hp⟩ := random_sign_code S h hval
  exact ⟨trace, t, he, ⟨hp.callee, hp.sp, hp.vectors⟩, random_sign_shared_post h hp⟩

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.RandomSignConstantTime`, which only this module used -/

section

/-! Whole-entry leakage equality against the merged randomized-signing contract. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64

theorem random_sign_body_agreement (S : Signer) {s t : State}
    (hs : RandomSignABI S.stack s) (ht : RandomSignABI S.stack t) (hp : RandomSignPublicAgree s t)
    (hvs : RandomValid S s) (hvt : RandomValid S t)
    (htrace : (randomSignRemaining (randomInput s) 0 8).trace = (randomSignRemaining (randomInput t) 0 8).trace)
    (hstatus : (randomSignRemaining (randomInput s) 0 8).status = (randomSignRemaining (randomInput t) 0 8).status)
    {tsa tsb : List Leak} {u w : State}
    (ea : Exec isa (RandomSign.body S.name S.code) (allocated Random.frameBytes s) tsa u)
    (eb : Exec isa (RandomSign.body S.name S.code) (allocated Random.frameBytes t) tsb w) : tsa = tsb := by
  by_cases hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)
  · exact random_sign_body_valid_ct S hs ht hp hvs hvt hq htrace hstatus ea eb
  · exact random_sign_body_invalid_ct S hs ht hp hq ea eb

theorem random_sign_alloc {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    isa.push (.alloc Random.frameBytes) s = some (allocated Random.frameBytes s) := by
  have hl := h.stackLower
  simp only [isa, push, allocated]
  exact ite_eq_left ⟨by decide, by decide, by decide, by unfold Random.frameBytes; omega_using [hl]⟩

theorem random_sign_constantTime (S : Signer) :
    ConstantTime isa (fun s => (randomSignCheckedContract abi (S.stack + 256)).pre s ∧ RandomValid S s)
      (randomSignCheckedContract abi (S.stack + 256)).pub
      (RandomSign.code S.name S.code) := by
  intro s t tsa tsb u w ⟨hs, hvs⟩ ⟨ht, hvt⟩ hpub ea eb
  have hsa := randomSignABI_of hs
  have hta := randomSignABI_of ht
  obtain ⟨hp, hstatus, _, htrace⟩ := random_sign_public_related hsa hta hpub
  cases ea with
  | frame hap hab _ =>
    cases eb with
    | frame hbp hbb _ =>
      rw [random_sign_alloc hsa, Option.some.injEq] at hap
      rw [random_sign_alloc hta, Option.some.injEq] at hbp
      subst hap
      subst hbp
      have hh := random_sign_body_agreement S hsa hta hp hvs hvt htrace hstatus hab hbb
      simpa only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] using hh

end VG.Proof.Dsa.AArch64

end

end

/-! Complete verification of randomized DSA signing for every AArch64 backend:
`vg_dsa_sign_random`, which calls the fully checked signer, and
`vg_dsa_sign_random_prevalidated`, which calls the signer for a validated
private key. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64

def randomSignSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 40 | .x2 => 0x7000 | .x3 => 0x2000
    | .x4 => 424 | .x5 => 128 | .x6 => 20 | .x7 => 0x5000 | _ => 0
  sp := 0x1000000000000
  mem a := if 0x2000 ≤ a.toNat ∧ a.toNat < 0x21a8 then
      VG.Proof.Dsa.validPrivateKeyWitness[a.toNat - 0x2000]?.getD 0
    else if a = 0x1000000000009 then 0x60 else if a = 0x1000000000019 then 0x80
    else if a = 0x1000000000020 then 0x40 else if a = 0x1000000000021 then 8 else 0
  rd := [⟨0x2000, 424⟩, ⟨0x5000, 0⟩, ⟨0x6000, 0⟩, ⟨0x1000000000000, 40⟩]
  wr := [⟨0x1000, 40⟩, ⟨0x7000, 8⟩, ⟨0x8000, 16896⟩]

private theorem sat_arg_0 : stackArg randomSignSatState 0 = 0 := by decide +kernel
private theorem sat_arg_1 : stackArg randomSignSatState 1 = 24576 := by decide +kernel
private theorem sat_arg_2 : stackArg randomSignSatState 2 = 0 := by decide +kernel
private theorem sat_arg_3 : stackArg randomSignSatState 3 = 32768 := by decide +kernel
private theorem sat_arg_4 : stackArg randomSignSatState 4 = 2112 := by decide +kernel

theorem random_sign_sat_pre (extra : Nat) (hb : extra < 2 ^ 32) :
    (randomSignCheckedContract abi (extra + 256)).pre randomSignSatState := by
  sig_pre [randomSignCheckedContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs]
  sig_and_intros
  all_goals try simp only [sat_arg_0, sat_arg_1, sat_arg_2, sat_arg_3, sat_arg_4]
  all_goals first
    | (change extra + 256 ≤ 281474976710656; omega_using [hb])
    | exact Region.disjoint_of_sep (by decide +kernel)
    | decide +kernel
    | (intro a h₁ h₂; simp only [Region.Contains, stackArgAddr, randomSignSatState] at h₁ h₂; bv_omega)

theorem random_sign_satisfiable (v : Backend) :
    ∃ s, (randomSignCheckedContract abi (v.stack + 256)).pre s :=
  ⟨_, random_sign_sat_pre v.stack v.stackBound⟩

/-- A backend's fully checked signer, which accepts every key. -/
def Backend.signer (v : Backend) : Signer where
  name := randomSignerName v
  code := SignVerify.sign v.mul
  stack := v.stack
  valid := fun _ _ _ => true
  verified := Verified.of_narrow v.signVerified (fun s => s) (fun _ s => s)
    (fun _ h => (signWith_pre h).1) (fun _ _ _ _ e => e) (fun _ _ _ _ _ ha hp => ⟨ha, signWith_post hp⟩)
    (fun _ _ _ _ h => signWith_pub h)
    (by obtain ⟨s, hs⟩ := v.signVerified.2.2; exact ⟨s, signWith_of_pre hs rfl⟩)
  sp := v.signSp
  depth := v.signDepth
  stackBound := v.stackBound
  noDit := v.signNoDit

theorem random_sign_verified (v : Backend) :
    Verified target (RandomSign.code (randomSignerName v) (SignVerify.sign v.mul))
      (randomSignCheckedContract abi (v.stack + 256)) :=
  ⟨fun s h => random_sign_correct v.signer s h rfl,
    fun s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ => random_sign_constantTime v.signer s₁ s₂ t₁ t₂ u₁ u₂ ⟨h₁, rfl⟩ ⟨h₂, rfl⟩,
    random_sign_satisfiable v⟩

def prevalidatedSignerName (v : Backend) : String := "vg_dsa_sign_prevalidated" ++ v.suffix

/-- A backend's signer for a validated private key. -/
def Backend.prevalidatedSigner (v : Backend) : Signer where
  name := prevalidatedSignerName v
  code := PrevalidatedSign.sign v.mul
  stack := v.stack
  valid := Spec.Dsa.validatePrivateKeyBytes
  verified := v.prevalidatedSignVerified
  sp := v.prevalidatedSignSp
  depth := v.prevalidatedSignDepth
  stackBound := v.stackBound
  noDit := v.prevalidatedSignNoDit

theorem randomPrevalidated_pre {extra : Nat} {s : State}
    (h : (Spec.Dsa.randomSignPrevalidatedContract abi (extra + 256)).pre s) :
    (randomSignCheckedContract abi (extra + 256)).pre s ∧
      Spec.Dsa.validatePrivateKeyBytes (s.gpr .x5).toNat (s.gpr .x6).toNat
        (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) = true := by
  sig_pre [Spec.Dsa.randomSignPrevalidatedContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs,
    show extra + 256 = (extra + 255) + 1 from rfl] at h
  sig_pre [Spec.Dsa.randomSignPrevalidatedContract, Spec.Dsa.randomSignSig, abi, argRegs,
    randomSignStackArgs] at h
  sig_split h
  refine ⟨?_, by assumption⟩
  sig_pre [randomSignCheckedContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs,
    show extra + 256 = (extra + 255) + 1 from rfl]
  sig_pre [randomSignCheckedContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs]
  sig_and_intros <;> with_reducible assumption

theorem randomPrevalidated_of_pre {extra : Nat} {s : State}
    (h : (randomSignCheckedContract abi (extra + 256)).pre s)
    (hv : Spec.Dsa.validatePrivateKeyBytes (s.gpr .x5).toNat (s.gpr .x6).toNat
        (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) = true) :
    (Spec.Dsa.randomSignPrevalidatedContract abi (extra + 256)).pre s := by
  sig_pre [randomSignCheckedContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs,
    show extra + 256 = (extra + 255) + 1 from rfl] at h
  sig_pre [randomSignCheckedContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs] at h
  sig_pre [Spec.Dsa.randomSignPrevalidatedContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs,
    show extra + 256 = (extra + 255) + 1 from rfl]
  sig_pre [Spec.Dsa.randomSignPrevalidatedContract, Spec.Dsa.randomSignSig, abi, argRegs,
    randomSignStackArgs]
  sig_split h
  sig_and_intros <;> with_reducible assumption

theorem random_sign_sat_key :
    Spec.Rsa.bytesAt randomSignSatState.mem 0x2000 424 = VG.Proof.Dsa.validPrivateKeyWitness :=
  VG.Proof.Dsa.bytesAt_of_list (lo := 0x2000) (by decide +kernel) (by decide) fun a h1 h2 => by
    have h : 0x2000 ≤ a.toNat ∧ a.toNat < 0x21a8 := ⟨h1, h2⟩
    simp only [randomSignSatState, h, and_self, ↓reduceIte]

theorem random_sign_prevalidated_verified (v : Backend) :
    Verified target (RandomSign.code (prevalidatedSignerName v) (PrevalidatedSign.sign v.mul))
      (Spec.Dsa.randomSignPrevalidatedContract abi (v.stack + 256)) :=
  ⟨fun s h => random_sign_correct v.prevalidatedSigner s (randomPrevalidated_pre h).1
      (randomPrevalidated_pre h).2,
    fun s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ => random_sign_constantTime v.prevalidatedSigner s₁ s₂ t₁ t₂ u₁ u₂
      (randomPrevalidated_pre h₁) (randomPrevalidated_pre h₂),
    ⟨_, randomPrevalidated_of_pre (random_sign_sat_pre v.stack v.stackBound) (by
      change Spec.Dsa.validatePrivateKeyBytes 128 20 (Spec.Rsa.bytesAt randomSignSatState.mem 0x2000 424) = true
      rw [random_sign_sat_key]
      exact VG.Proof.Dsa.validPrivateKeyWitness_valid)⟩⟩

end VG.Proof.Dsa.AArch64
