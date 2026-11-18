module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSingle
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignLoopCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignFinishAgreement
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSingleCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignBody
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignLoopCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignFinishAgreement
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSingleCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignBody
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignEnv
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignEnv
meta import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Impl.Dsa.X86_64.Random
import VerifiedGarbage.Proof.Dsa.X86_64.SignificantCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomScan
import VerifiedGarbage.Proof.Dsa.X86_64.RandomClear
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
meta import VerifiedGarbage.Impl.Dsa.X86_64.Random
meta import VerifiedGarbage.Proof.Dsa.X86_64.SignificantCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomScan
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomClear
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
meta import Mathlib.Algebra.Group.Nat.Defs
meta import Mathlib.Tactic.Attr.Core
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel

/-! ### `Dsa.X86_64.RandomSignInitCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.RandomPrepareCT`, which this module and modules that import it used -/

section

/-! Preparing the sampler leaks public pointers and lengths only. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

structure RandomPreparePublic where
  B : Addr
  Q : Addr
  bytes : List Byte

def RandomPreparePre (p : RandomPreparePublic) (s : State) : Prop :=
  Scr s p.B Random.frameBytes ∧ s.gpr .rsp = p.B ∧
  word s.mem p.B Random.oQ = p.Q ∧ word s.mem p.B Random.oQLen = BitVec.ofNat 64 p.bytes.length ∧
  Src s p.B Random.frameBytes p.Q p.bytes ∧ 0 < p.bytes.length ∧ p.bytes.length < 2 ^ 64

def RandomPrepareRegs (p : RandomPreparePublic) (s : State) : Prop :=
  s.gpr .rsp = p.B ∧ s.gpr .r10 = p.Q ∧ s.gpr .r11 = BitVec.ofNat 64 p.bytes.length ∧
  Src s p.B Random.frameBytes p.Q p.bytes ∧ 0 < p.bytes.length ∧ p.bytes.length < 2 ^ 64

private theorem header_ok {p : RandomPreparePublic} {s : State} (h : RandomPreparePre p s) :
    WP isa (.block (Random.clearNonce ++ ([.mov .r10 (.mem (Random.sp Random.oQ)),
      .mov .r11 (.mem (Random.sp Random.oQLen))] : List Instr))) s (RandomPrepareRegs p) := by
  obtain ⟨hs, hsp, hq, hl, hsrc, hpos, hbound⟩ := h
  rw [WP.block_append_iff]
  refine WP.mono (random_clear_ok hs hsp) fun t ⟨hm, hk⟩ => ?_
  have hts := hs.congr hk.2.2
  have htsp := (hk.gpr (by decide)).trans hsp
  have htq : word t.mem p.B Random.oQ = p.Q := by
    rw [hm, (random_clear_outside _ _).word (by decide) (by decide)]; exact hq
  have htl : word t.mem p.B Random.oQLen = BitVec.ofNat 64 p.bytes.length := by
    rw [hm, (random_clear_outside _ _).word (by decide) (by decide)]; exact hl
  refine WP.mono (WP.keep [.r10, .r11] (Q := fun u => u.mem = t.mem ∧
      u.gpr .r10 = p.Q ∧ u.gpr .r11 = BitVec.ofNat 64 p.bytes.length) (by
    xrun [random_ea_sp, htsp, hts.ld (d := Random.oQ) (by decide),
      hts.ld (d := Random.oQLen) (by decide), htq, htl]) rfl) fun u ⟨⟨hum, hup, hul⟩, hku⟩ => ?_
  refine ⟨(hku.gpr (by decide)).trans htsp, hup, hul, hsrc.congrK ?_ (hk.trans hku), hpos, hbound⟩
  rw [hum, hm]
  exact InScr.of_outside (random_clear_outside _ _) (by decide)

private theorem scan_ct : RelCT isa (Two RandomPrepareRegs) Random.significant (fun _ _ => True) := by
  unfold Random.significant
  refine RelCT.seq (two_piece (Ψ := fun p s => ScanPre ⟨p.B, Random.frameBytes, p.Q, p.bytes⟩ s)
    [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide) ?_) ?_
  · intro p s ⟨_, hp, hl, hsrc, hpos, hbound⟩
    refine WP.mono (WP.keep [.rsi, .rcx] (Q := fun t => t.mem = s.mem ∧
      t.gpr .rsi = p.Q ∧ t.gpr .rcx = BitVec.ofNat 64 p.bytes.length)
      (by xrun [hp, hl]) rfl) fun t ⟨⟨hm, ht1, ht2⟩, hk⟩ => ?_
    exact ⟨ht1, ht2, hsrc.congrK (by rw [hm]; exact InScr.refl _ _ _) hk, hpos, hbound⟩
  · refine RelCT.seq (significant_ct.mono ?_ (fun _ _ _ => trivial)) ?_
    · intro s t ⟨p, hs, ht⟩
      exact ⟨⟨p.B, Random.frameBytes, p.Q, p.bytes⟩, hs, ht⟩
    · exact (two_taint (Φ := fun (_ : Unit) (_ : State) => True) []
        (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)).mono
        (fun _ _ _ => ⟨(), trivial, trivial⟩) (fun _ _ _ => trivial)

theorem random_prepare_ct : RelCT isa (Two RandomPreparePre) Random.prepare (fun _ _ => True) := by
  unfold Random.prepare
  refine RelCT.seq (two_piece (Ψ := RandomPrepareRegs) [.rsp] ?_ (by taint_decide)
    (fun _ _ h => header_ok h)) ?_
  · intro p s t hs ht r hr
    rw [List.mem_singleton] at hr
    subst r
    exact hs.2.1.trans ht.2.1.symm
  · refine RelCT.seq (two_post (Ψ := fun p s => s.gpr .rsp = p.B) scan_ct ?_) ?_
    · intro p s ⟨hsp, hp, hl, hsrc, hpos, hbound⟩
      exact WP.mono (random_significant_ok hp hl hsrc hpos hbound)
        (fun _ ⟨_, _, _, _, hk⟩ => (hk.gpr (by decide)).trans hsp)
    · apply two_taint [.rsp] ?_ (by taint_decide)
      intro p s t hs ht r hr
      rw [List.mem_singleton] at hr
      subst r
      exact hs.trans ht.symm

end VG.Proof.Dsa.X86_64

end

end

/-! Saving arguments and preparing q leaks no private key or random-tape bytes. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def RandomSignInitPre (p : RandomPreparePublic) (t : State) : Prop :=
  ∃ s extra, RandomSignABI extra s ∧ t = allocState Random.frameBytes s ∧
    p = ⟨randomBase s, s.gpr .rcx + s.gpr .r9, randomQBytes s⟩

private theorem entry_prepare {p : RandomPreparePublic} {t : State} (hp : RandomSignInitPre p t) :
    WP isa (.block RandomSign.entry) t (RandomPreparePre p) := by
  obtain ⟨s, extra, h, rfl, rfl⟩ := hp
  have hsp : (allocState Random.frameBytes s).gpr .rsp = randomBase s := rfl
  refine WP.mono (random_entry_ok (random_alloc_scr h) hsp (random_incoming_read h))
    fun u ⟨hum, hk⟩ => ?_
  have hsaved : RandomSaved s u.mem := by rw [hum]; exact random_saved_entry s
  have hf : InScr (randomBase s) Random.frameBytes (allocState Random.frameBytes s).mem u.mem := by
    rw [hum]; exact InScr.of_outside (random_entry_outside _ _) (by decide)
  have hv (p : Nat × BitVec 64) (hp : p ∈ randomEntryValues (allocState Random.frameBytes s) (randomBase s)) :
      word u.mem (randomBase s) p.1 = p.2 := by
    rw [hum]; exact random_entry_values _ _ p hp
  have hqu : word u.mem (randomBase s) Random.oQ = s.gpr .rcx + s.gpr .r9 :=
    hv (168, s.gpr .rcx + s.gpr .r9) (by simp [randomEntryValues, allocState, State.setReg])
  have hql : word u.mem (randomBase s) Random.oQLen = BitVec.ofNat 64 (randomQBytes s).length := by
    simpa only [Random.oQLen, random_q_length h, ofNat_toNat64] using
      hsaved (88, stackArg s 0) (by simp [randomSavedValues])
  refine ⟨(random_alloc_scr h).congr hk.2.2, (hk.gpr (by decide)).trans hsp,
    hqu, hql, (random_initial_q h).congrK hf hk, ?_, ?_⟩
  · change 0 < (randomQBytes s).length
    rw [random_q_length h]
    have hl := h.lengths
    unfold Spec.Dsa.lengthsValid at hl
    omega_using [hl]
  · change (randomQBytes s).length < 2 ^ 64
    rw [random_q_length h]
    exact (stackArg s 0).isLt

theorem random_sign_init_ct : RelCT isa (Two RandomSignInitPre)
    (.seq (.block RandomSign.entry) Random.prepare) (fun _ _ => True) := by
  refine RelCT.seq (two_piece (Ψ := RandomPreparePre) [.rsp] ?_ (by taint_decide)
    (fun _ _ h => entry_prepare h)) random_prepare_ct
  intro p s t hs ht r hr
  rw [List.mem_singleton] at hr
  subst r
  obtain ⟨a, _, _, rfl, hpa⟩ := hs
  obtain ⟨b, _, _, rfl, hpb⟩ := ht
  change randomBase a = randomBase b
  exact (congrArg RandomPreparePublic.B hpa).symm.trans (congrArg RandomPreparePublic.B hpb)

end VG.Proof.Dsa.X86_64

end

end

/-! Compose initialization, retries, and publication for valid subgroup moduli. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem random_sign_init_agreement {extra : Nat} {s t : State}
    (hs : RandomSignABI extra s) (ht : RandomSignABI extra t) (hp : RandomSignPublicAgree s t)
    {tsa tsb : List Leak} {u w : State}
    (ea : Exec isa (.seq (.block RandomSign.entry) Random.prepare) (allocState Random.frameBytes s) tsa u)
    (eb : Exec isa (.seq (.block RandomSign.entry) Random.prepare) (allocState Random.frameBytes t) tsb w) : tsa = tsb := by
  have he : (⟨randomBase s, s.gpr .rcx + s.gpr .r9, randomQBytes s⟩ : RandomPreparePublic) =
      ⟨randomBase t, t.gpr .rcx + t.gpr .r9, randomQBytes t⟩ := by
    rw [hp.base, hp.regs .rcx (by decide), hp.regs .r9 (by decide), hp.qbytes]
  exact (random_sign_init_ct _ _ _ _ _ _
    ⟨_, ⟨s, extra, hs, rfl, rfl⟩, t, extra, ht, rfl, he⟩ ea eb).1

theorem random_sign_cmp_zero_ct : RelCT isa (fun _ _ => True) (.block [.alu .cmp .rax (.imm 0)]) (fun _ _ => True) := by
  exact (two_taint (Φ := fun (_ : Unit) (_ : State) => True) []
    (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)).mono
    (fun _ _ _ => ⟨(), trivial, trivial⟩) (fun _ _ _ => trivial)

private theorem test_zero_mx {s : State} :
    WP isa (.block [.alu .cmp .rax (.imm 0)]) s fun t =>
      ((t.mem = s.mem ∧ t.zf = some (s.gpr .rax == 0)) ∧ Keep [.rax] s t) ∧ t.mxcsr = s.mxcsr :=
  WP.mono_mx (by decide) random_sign_test_zero (fun _ h hm => ⟨h, hm⟩)

def randomSignTail (S : Signer) : Prog isa :=
  .seq (.block [.alu .cmp .rax (.imm 0)])
    (.seq (.ite .e (.block [.store (Random.sp Random.oStatus) .rax])
      (.loop (.seq (RandomSign.attempt S.name S.code) randomSignStatusTest) .e)) RandomSign.finish)

private theorem valid_tail (S : Signer) {s t a b : State}
    {hs : RandomSignABI S.stack s} {ht : RandomSignABI S.stack t}
    {hqs : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {hqt : 1 < Spec.Dsa.decodeBE (randomQBytes t)}
    (ha : RandomSignRunning hs hqs 0 8 a) (hb : RandomSignRunning ht hqt 0 8 b)
    (hra : a.gpr .rax = 1) (hrb : b.gpr .rax = 1) (hp : RandomSignPublicAgree s t)
    (htrace : (randomSignRemaining (randomInput s) 0 8).trace = (randomSignRemaining (randomInput t) 0 8).trace)
    (hstatus : (randomSignRemaining (randomInput s) 0 8).status = (randomSignRemaining (randomInput t) 0 8).status)
    (hvs : RandomValid S s) (hvt : RandomValid S t)
    {tsa tsb : List Leak} {u w : State} (ea : Exec isa (randomSignTail S) a tsa u)
    (eb : Exec isa (randomSignTail S) b tsb w) : tsa = tsb := by
  cases ea with
  | seq eac ear => cases ear with
    | seq eai eaf =>
      cases eb with
      | seq ebc ebr => cases ebr with
        | seq ebi ebf =>
          have hcmp := (random_sign_cmp_zero_ct _ _ _ _ _ _ trivial eac ebc).1
          obtain ⟨⟨⟨ham, haz⟩, hka⟩, hmxa⟩ := random_post_of_exec test_zero_mx eac
          obtain ⟨⟨⟨hbm, hbz⟩, hkb⟩, hmxb⟩ := random_post_of_exec test_zero_mx ebc
          have har := ha.congr ham hka hmxa
          have hbr := hb.congr hbm hkb hmxb
          rw [hra] at haz
          rw [hrb] at hbz
          cases eai with
          | iteT hc _ => simp only [eval, haz] at hc; contradiction
          | iteF _ eal =>
            cases ebi with
            | iteT hc _ => simp only [eval, hbz] at hc; contradiction
            | iteF _ ebl =>
              have hloop := (random_sign_loop_ct S hp hvs hvt 8 _ _ _ _ _ _
                ⟨by decide, by decide, 0, har, hbr, htrace⟩ eal ebl).1
              obtain ⟨⟨_, hrunA⟩, hsta, _⟩ := random_post_of_exec (random_sign_loop_correct S har (by decide) (by decide) hvs) eal
              obtain ⟨⟨_, hrunB⟩, hstb, _⟩ := random_post_of_exec (random_sign_loop_correct S hbr (by decide) (by decide) hvt) ebl
              rw [← hstatus] at hstb
              have hfinish := random_finish_agreement hs ht hrunA.finishPre hrunB.finishPre hp hsta hstb eaf ebf
              rw [hcmp, hloop, hfinish]

theorem random_sign_body_valid_ct (S : Signer) {s t : State}
    (hs : RandomSignABI S.stack s) (ht : RandomSignABI S.stack t) (hp : RandomSignPublicAgree s t)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s))
    (htrace : (randomSignRemaining (randomInput s) 0 8).trace = (randomSignRemaining (randomInput t) 0 8).trace)
    (hstatus : (randomSignRemaining (randomInput s) 0 8).status = (randomSignRemaining (randomInput t) 0 8).status)
    (hvs : RandomValid S s) (hvt : RandomValid S t)
    {tsa tsb : List Leak} {u w : State}
    (ea : Exec isa (RandomSign.body S.name S.code) (allocState Random.frameBytes s) tsa u)
    (eb : Exec isa (RandomSign.body S.name S.code) (allocState Random.frameBytes t) tsb w) : tsa = tsb := by
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

end VG.Proof.Dsa.X86_64
