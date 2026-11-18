module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSingle
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignPublic
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCall
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedExp
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallMemory
import VerifiedGarbage.Proof.Dsa.X86_64.RandomMemory
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Impl.Dsa.X86_64.RandomSign
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Order.RelClasses
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
public import Aesop.BuiltinRules
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Impl.Dsa.X86_64.RandomSign
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
meta import Mathlib.Tactic.Finiteness.Attr
meta import Mathlib.Order.RelClasses
meta import Mathlib.Algebra.Group.Nat.Defs
meta import Mathlib.Tactic.Push
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.Attr.Core
meta import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Dsa.X86_64.RandomSignRetryCT`, which only this module used -/

section

/-! Retry control reveals only the signer's low-word success bit and attempt budget. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

structure RandomRetryPublic where
  B : Addr
  success : Bool
  attempts : Nat

def RandomRetryPre (p : RandomRetryPublic) (s : State) : Prop :=
  Scr s p.B Random.frameBytes ∧ s.gpr .rsp = p.B ∧
  (s.gpr .rax).setWidth 32 = (if p.success then 1 else 0) ∧
  word s.mem p.B Random.oAttempts = BitVec.ofNat 64 p.attempts ∧
  0 < p.attempts ∧ p.attempts < 2 ^ 64

def RandomRetryMid (p : RandomRetryPublic) (s : State) : Prop :=
  Scr s p.B Random.frameBytes ∧ s.gpr .rsp = p.B ∧ s.zf = some (!p.success) ∧
  word s.mem p.B Random.oAttempts = BitVec.ofNat 64 p.attempts ∧
  0 < p.attempts ∧ p.attempts < 2 ^ 64

private theorem header_ok {p : RandomRetryPublic} {s : State} (h : RandomRetryPre p s) :
    WP isa (.block [.mov32 .rax (.reg .rax), .store (Random.sp Random.oStatus) .rax,
      .alu .cmp .rax (.imm 0)]) s (RandomRetryMid p) := by
  obtain ⟨hs, hsp, ha, hn, hp, hb⟩ := h
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.mem = s.mem.writeW (off p.B Random.oStatus) (if p.success then (1 : BitVec 64) else 0) ∧
      t.zf = some (!p.success)) (by
      cases hx : p.success <;> xrun [random_ea_sp, hsp, hs.st (d := Random.oStatus) (by decide), hx, ha] <;> rfl) rfl)
    fun t ⟨⟨hm, hz⟩, hk⟩ => ?_
  refine ⟨hs.congr hk.2.2, (hk.gpr (by decide)).trans hsp, hz, ?_, hp, hb⟩
  rw [hm, (writeW_outside _ p.B _ (by decide)).word (by decide) (by decide)]
  exact hn

private theorem decrement_ok {p : RandomRetryPublic} {s : State} (h : RandomRetryMid p s) :
    WP isa (.block [.mov .rax (.mem (Random.sp Random.oAttempts)), .alu .sub .rax (.imm 1),
      .store (Random.sp Random.oAttempts) .rax]) s fun t =>
      t.gpr .rsp = p.B ∧ t.zf = some (decide (p.attempts = 1)) := by
  obtain ⟨hs, hsp, _, hn, hp, hb⟩ := h
  have hz : (BitVec.ofNat 64 (p.attempts - 1) == 0) = decide (p.attempts = 1) := by
    rw [ofNat64_beq_zero (by omega_using [hb])]
    exact decide_eq_decide.mpr (by omega_using [hp])
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (decide (p.attempts = 1)))
    (by xrun [random_ea_sp, hsp, hs.ld (d := Random.oAttempts) (by decide),
      hs.st (d := Random.oAttempts) (by decide), hn, ofNat64_pred hp hb, hz]) rfl)
    fun _ ⟨ht, hk⟩ => ⟨(hk.gpr (by decide)).trans hsp, ht⟩

theorem random_callFinish_ct : RelCT isa (Two RandomRetryPre) RandomSign.callFinish (fun _ _ => True) := by
  unfold RandomSign.callFinish
  refine RelCT.seq (two_piece (Ψ := RandomRetryMid) [.rsp] ?_ (by taint_decide)
    (fun _ _ h => header_ok h)) ?_
  · intro p s t hs ht r hr
    rw [List.mem_singleton] at hr
    subst r
    exact hs.2.1.trans ht.2.1.symm
  · refine two_ite (fun p s t hs ht => by simp only [eval, hs.2.2.1, ht.2.2.1]) ?_ ?_
    · refine RelCT.seq (two_piece (Ψ := fun p s => s.gpr .rsp = p.B ∧
        s.zf = some (decide (p.attempts = 1))) [.rsp] ?_ (by taint_decide)
        (fun _ _ h => decrement_ok h.1)) ?_
      · intro p s t hs ht r hr
        rw [List.mem_singleton] at hr
        subst r
        exact hs.1.2.1.trans ht.1.2.1.symm
      · refine two_ite (fun p s t hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_
        · apply two_taint [.rsp] ?_ (by taint_decide)
          intro p s t hs ht r hr
          rw [List.mem_singleton] at hr
          subst r
          exact hs.1.1.trans ht.1.1.symm
        · exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)
    · exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.RandomSignCallCT`, which only this module used -/

section

/-! Instantiate the supplied-nonce signer's leakage contract at a wrapper call. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

structure RandomSignCallState {extra : Nat} {s : State} (h : RandomSignABI extra s) (t : State) : Prop where
  sp : t.gpr .rsp = randomBase s
  args : ∀ i < 5, word t.mem (randomBase s) (8 * i) = randomCallArg s i
  di : t.gpr .rdi = s.gpr .rdi
  si : t.gpr .rsi = s.gpr .rsi
  dx : t.gpr .rdx = s.gpr .rcx
  cx : t.gpr .rcx = s.gpr .r8
  r8 : t.gpr .r8 = s.gpr .r9
  r9 : t.gpr .r9 = off (randomBase s) Random.oNonce
  rd : t.rd = s.rd
  wr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr
  key : Spec.Rsa.bytesAt t.mem (s.gpr .rcx) (s.gpr .r8).toNat = (randomInput s).key

def randomCallPublicKey (s t : State) : List Nat :=
  Spec.Dsa.publicBytesLeak (s.gpr .r9).toNat (stackArg s 0).toNat
    (Spec.Rsa.bytesAt t.callEntry.mem (s.gpr .rcx) (s.gpr .r8).toNat)

theorem random_call_public {valid : Nat → Nat → List Byte → Bool} {extra : Nat} {s t a b : State}
    {hs : RandomSignABI extra s} {ht : RandomSignABI extra t}
    (ha : RandomSignCallState hs a) (hb : RandomSignCallState ht b) (hp : RandomSignPublicAgree s t)
    (hk : randomCallPublicKey s a = randomCallPublicKey t b)
    (hr : Spec.Dsa.signStatus (randomCallResult s a) = Spec.Dsa.signStatus (randomCallResult t b)) :
    (signContractWith valid abi extra).pub
      (a.callEntry.withRegions (randomCallRd s) (randomCallWr s))
      ((b.callEntry.withRegions (randomCallRd t) (randomCallWr t)).withMx
        (a.callEntry.withRegions (randomCallRd s) (randomCallWr s)).mxcsr) := by
  have hA (i : Nat) (hi : i < 5) :
      stackArg (a.callEntry.withRegions (randomCallRd s) (randomCallWr s)) i = randomCallArg s i :=
    (random_call_stackArg ha.sp _ _ hi).trans (ha.args i hi)
  have hB (i : Nat) (hi : i < 5) :
      stackArg (b.callEntry.withRegions (randomCallRd t) (randomCallWr t)) i = randomCallArg t i :=
    (random_call_stackArg hb.sp _ _ hi).trans (hb.args i hi)
  sig_pub [signContractWith, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop]
  simp only [stackArg_withMx, ha.sp, hb.sp, ha.di, hb.di, ha.si, hb.si, ha.dx, hb.dx, ha.cx, hb.cx, ha.r8, hb.r8, ha.r9, hb.r9,
    hA 0 (by decide), hA 1 (by decide), hA 2 (by decide), hA 3 (by decide), hA 4 (by decide),
    hB 0 (by decide), hB 1 (by decide), hB 2 (by decide), hB 3 (by decide), hB 4 (by decide), randomCallArg]
  refine ⟨?_, ?_, hp.regs .rdi (by decide), hp.regs .rsi (by decide), hp.regs .rcx (by decide),
    hp.regs .r8 (by decide), hp.regs .r9 (by decide), ?_, hp.args 0 (by decide), hp.args 1 (by decide),
    hp.args 2 (by decide), hp.args 5 (by decide), hp.args 6 (by decide)⟩
  · rw [hp.base]
  · simp only [randomCallPublicKey, randomCallResult, State.callEntry_mem, ha.sp, hb.sp] at hk hr
    rw [hk, hr]
  · rw [hp.base]

def RandomSignCallRelated (S : Signer) (a b : State) : Prop :=
  ∃ s t, ∃ hs : RandomSignABI S.stack s, ∃ ht : RandomSignABI S.stack t,
    RandomValid S s ∧ RandomValid S t ∧ RandomSignCallState hs a ∧ RandomSignCallState ht b ∧ RandomSignPublicAgree s t ∧
    randomCallPublicKey s a = randomCallPublicKey t b ∧
    Spec.Dsa.signStatus (randomCallResult s a) = Spec.Dsa.signStatus (randomCallResult t b)

theorem random_signer_ct (S : Signer) : RelCT isa (RandomSignCallRelated S)
    (.call S.name S.code) (fun _ _ => True) := by
  apply VG.X86_64.RelCT.callExMx S.verified.1 S.verified.2.1 S.noMx (fun _ _ h => h)
  intro a b ⟨s, t, hs, ht, hvs, hvt, ha, hb, hp, hk, hr⟩
  obtain ⟨hca, hwa⟩ := random_call_covers hs ha.rd ha.wr
  obtain ⟨hcb, hwb⟩ := random_call_covers ht hb.rd hb.wr
  exact ⟨randomCallRd s, randomCallWr s, randomCallRd t, randomCallWr t,
    random_call_pre_with S hs ha.sp ha.args ha.di ha.si ha.dx ha.cx ha.r8 ha.r9 ha.key hvs,
    random_call_pre_with S ht hb.sp hb.args hb.di hb.si hb.dx hb.cx hb.r8 hb.r9 hb.key hvt,
    random_call_public ha hb hp hk hr, hca, hwa, hcb, hwb,
    ha.sp.trans (hp.base.trans hb.sp.symm)⟩

end VG.Proof.Dsa.X86_64

end

end


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
    exact Offset.sub_base _ (by omega_using [])
  have hm := random_callEntry_bytes hsp
    (((h.stackKey.sub_left hsub).symm).sep (Region.contains_self _ _) (Region.contains_self _ _)) (s.gpr .r8).isLt
  unfold randomCallPublicKey
  rw [hm]
  have hkb : Spec.Rsa.bytesAt t.mem (s.gpr .rcx) (s.gpr .r8).toNat = (randomInput s).key := by
    simpa only [randomInput, bytesAt_length] using FoldedPublic.src_bytesAt hkey
  rw [hkb]
  rfl

theorem random_signer_retry_pre (S : Signer) {s t : State} {fuel : Nat} {h : RandomSignABI S.stack s}
    (hc : RandomSignCallState h t)
    (hn : word t.mem (randomBase s) Random.oAttempts = BitVec.ofNat 64 fuel)
    (hpos : 0 < fuel) (hbound : fuel < 2 ^ 64) (hv : RandomValid S s) :
    WP isa (.call S.name S.code) t
      (RandomRetryPre ⟨randomBase s, (randomCallResult s t).isSome, fuel⟩) := by
  refine WP.mono (random_signer_outcome S h hc.sp hc.args hc.di hc.si hc.dx hc.cx hc.r8 hc.r9 hc.rd hc.wr hc.key hv)
    fun u ⟨_, huw, huc, hf, hstatus, _, _⟩ => ?_
  refine ⟨(random_alloc_scr h).congr (huw.trans hc.wr), (huc .rsp (by decide)).trans hc.sp,
    ?_, (random_frame_words (random_call_frameBytes h hf) (by decide)).trans hn, hpos, hbound⟩
  apply BitVec.eq_of_toNat_eq
  rw [hstatus]
  cases randomCallResult s t <;> rfl

theorem random_callArgs_observe (S : Signer) {s t : State} {h : RandomSignABI S.stack s}
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
    omega_using [hl]
  have hkeyA' : Spec.Rsa.bytesAt a.mem (s.gpr .rcx) (s.gpr .r8).toNat = (randomInput s).key := by
    simpa only [randomInput, bytesAt_length] using FoldedPublic.src_bytesAt hkeyA
  have hres : randomCallResult s a = randomSingleResult s k := by
    rw [random_callResult_plain h hspA]
    have hkey := hkeyA'
    have hdigest : Spec.Rsa.bytesAt a.mem (stackArg s 1) (stackArg s 2).toNat = (randomInput s).digest := by
      simpa only [randomInput, bytesAt_length] using FoldedPublic.src_bytesAt hdigestA
    have hnonceA := (random_outside_bytes hargs
      (show Random.oNonce + (stackArg s 0).toNat ≤ 2 ^ 64 by unfold Random.oNonce; omega_using [hqbound])
      (Or.inr (show 0 + 40 ≤ Random.oNonce by decide))).trans hnonce
    rw [hkey, hdigest, hnonceA]
    rfl
  have hna : word a.mem (randomBase s) Random.oAttempts = BitVec.ofNat 64 fuel :=
    (hargs.word (by decide) (by decide)).trans hr.attempts
  exact ⟨⟨hspA, hw, hdi, hsi, hdx, hcx, h8, h9, hka.2.1.trans hr.rd, hka.2.2.trans hr.wr, hkeyA'⟩,
    hres, random_call_key_source h hspA hkeyA, hna⟩

end VG.Proof.Dsa.X86_64
