module

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Dsa.RandomSign
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignRunning
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCall
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFinish
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignPublishValue
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSample
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallMemory
import VerifiedGarbage.Proof.Dsa.AArch64.CallFinishCT
import VerifiedGarbage.Proof.Dsa.AArch64.RandomMemory
import VerifiedGarbage.Proof.Dsa.AArch64.RandomState
public import VerifiedGarbage.Impl.Dsa.AArch64.RandomSign
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawControl

/-! ### `Dsa.AArch64.RandomSignAttempt`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.RandomSignRetry`, which this module and modules that import it used -/

section

/-! Update the bounded signing-attempt counter after a supplied-nonce call. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def randomRetryMem (m : Mem) (B : Addr) (success : Bool) (attempts : Nat) : Mem :=
  if success then m.writeW (off B Random.oStatus) (1 : BitVec 64)
  else
    let m' := (m.writeW (off B Random.oStatus) (0 : BitVec 64)).writeW
      (off B Random.oAttempts) (BitVec.ofNat 64 (attempts - 1))
    if attempts = 1 then m' else m'.writeW (off B Random.oStatus) (4 : BitVec 64)

theorem random_retryHead_ok {s : State} {B : Addr} (success : Bool)
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (ha : (s.gpr .x0).setWidth 32 = if success then 1 else 0) :
    WP isa (.block (([.ldrSp .x30 RandomSign.oLink, .logic .orr .w .x0 .x0 .x0] : List Instr) ++
      Random.store Random.oStatus .x0)) s fun t =>
      t.mem = s.mem.writeW (off B Random.oStatus) (if success then (1 : BitVec 64) else 0) ∧
      t.gpr .x0 = (if success then (1 : BitVec 64) else 0) ∧
      t.gpr .x30 = word s.mem B RandomSign.oLink ∧ Keep [.x0, .x15, .x30] s t := by
  refine WP.mono (WP.keep [.x0, .x15, .x30] (Q := fun t =>
    t.mem = s.mem.writeW (off B Random.oStatus) (if success then (1 : BitVec 64) else 0) ∧
    t.gpr .x0 = (if success then (1 : BitVec 64) else 0) ∧
    t.gpr .x30 = word s.mem B RandomSign.oLink) ?_ rfl rfl rfl)
    fun t ⟨⟨hm, ha, hl⟩, hk⟩ => ⟨hm, ha, hl, hk⟩
  unfold Random.store
  brun [exec_ldrSp (show RandomSign.oLink % 8 = 0 ∧ RandomSign.oLink < 32768 by decide),
    exec_addSp (show Random.oStatus < 4096 by decide), hsp,
    hs.ld (d := RandomSign.oLink) (by decide), hs.st (d := Random.oStatus) (by decide), exec_logic, State.read, State.write,
    BitVec.or_self, ha]
  cases success <;> exact ⟨rfl, rfl⟩

theorem random_attemptDecrement_ok {s : State} {B : Addr} {attempts : Nat}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hn : word s.mem B Random.oAttempts = BitVec.ofNat 64 attempts)
    (hpos : 0 < attempts) (hbound : attempts < 2 ^ 64) :
    WP isa (.block (([.ldrSp .x0 Random.oAttempts, .subImm .x .x0 .x0 1] : List Instr) ++
      Random.store Random.oAttempts .x0)) s fun t =>
      t.mem = s.mem.writeW (off B Random.oAttempts) (BitVec.ofNat 64 (attempts - 1)) ∧
      t.gpr .x0 = BitVec.ofNat 64 (attempts - 1) ∧ Keep [.x0, .x15] s t := by
  have hp : BitVec.ofNat 64 attempts - 1#64 = BitVec.ofNat 64 (attempts - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  refine WP.mono (WP.keep [.x0, .x15] (Q := fun t =>
    t.mem = s.mem.writeW (off B Random.oAttempts) (BitVec.ofNat 64 (attempts - 1)) ∧
    t.gpr .x0 = BitVec.ofNat 64 (attempts - 1)) ?_ rfl rfl rfl)
    fun t ⟨⟨hm, ha⟩, hk⟩ => ⟨hm, ha, hk⟩
  unfold Random.store
  brun [exec_ldrSp (show Random.oAttempts % 8 = 0 ∧ Random.oAttempts < 32768 by decide),
    exec_addSp (show Random.oAttempts < 4096 by decide), hsp,
    hs.ld (d := Random.oAttempts) (by decide), hs.st (d := Random.oAttempts) (by decide), hn, hp]

theorem random_callFinish_ok {s : State} {B : Addr} {attempts : Nat} (success : Bool)
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (ha : (s.gpr .x0).setWidth 32 = if success then 1 else 0)
    (hn : word s.mem B Random.oAttempts = BitVec.ofNat 64 attempts)
    (hpos : 0 < attempts) (hbound : attempts < 2 ^ 64) :
    WP isa RandomSign.callFinish s fun t =>
      t.mem = randomRetryMem s.mem B success attempts ∧
      t.gpr .x30 = word s.mem B RandomSign.oLink ∧ Keep [.x0, .x15, .x30] s t := by
  unfold RandomSign.callFinish
  refine WP.seq (WP.mono (random_retryHead_ok success hs hsp ha)
    fun u ⟨hum, hua, hul, hku⟩ => ?_)
  cases success with
  | true =>
    refine WP.ite false (by simp [eval, State.read, hua]) (fun h => Bool.noConfusion h)
      (fun _ => WP.block_nil ?_)
    exact ⟨by rw [hum]; rfl, hul, hku⟩
  | false =>
    refine WP.ite true (by simp [eval, State.read, hua]) (fun _ => ?_) (fun h => Bool.noConfusion h)
    have hus := hs.congr hku.wr
    have husp := hku.sp.trans hsp
    have hun : word u.mem B Random.oAttempts = BitVec.ofNat 64 attempts := by
      rw [hum, (writeW_outside _ B _ (by decide)).word (by decide) (by decide), hn]
    refine WP.seq (WP.mono (random_attemptDecrement_ok hus husp hun hpos hbound)
      fun v ⟨hvm, hva, hkv⟩ => ?_)
    have hvl := (hkv.gpr .x30 (by decide)).trans hul
    by_cases h1 : attempts = 1
    · refine WP.ite false (by simp [eval, State.read, hva, h1])
        (fun h => Bool.noConfusion h) (fun _ => WP.block_nil ?_)
      exact ⟨by rw [hvm, hum]; simp only [randomRetryMem, Bool.false_eq_true, ite_false, h1, ite_true],
        hvl, (hku.trans hkv).mono (by decide)⟩
    · have hnz : (BitVec.ofNat 64 (attempts - 1) == 0#64) = false := by
        simp only [beq_eq_false_iff_ne]
        intro he
        have hh := congrArg BitVec.toNat he
        simp only [BitVec.toNat_ofNat] at hh
        omega_using [hsp, hn, hpos, hbound, hul, ha, hua, husp, hun, hva, hvl, h1, he, hh]
      refine WP.ite true (by
        change some (!(v.gpr .x0 == 0#64)) = some true
        rw [hva, hnz]; rfl) (fun _ => ?_) (fun h => Bool.noConfusion h)
      refine WP.mono (random_status_ok 4 (hus.congr hkv.wr) (hkv.sp.trans husp))
        fun t ⟨_, htm, hkt⟩ => ?_
      exact ⟨by rw [htm, hvm, hum]; simp only [randomRetryMem, Bool.false_eq_true, ite_false, h1]; rfl,
        (hkt.gpr .x30 (by decide)).trans hvl, ((hku.trans hkv).trans hkt).mono (by decide)⟩

theorem random_retry_outside (m : Mem) (B : Addr) (success : Bool) (attempts : Nat) :
    Outside B 152 48 m (randomRetryMem m B success attempts) := by
  have step (m : Mem) (d : Nat) (v : BitVec 64) (hd : 152 ≤ d ∧ d + 8 ≤ 200) :
      Outside B 152 48 m (m.writeW (off B d) v) :=
    (writeW_outside _ _ _ (by omega_using [hd])).mono hd.1 hd.2
  cases success with
  | true => exact step _ _ _ (by decide)
  | false =>
    unfold randomRetryMem
    simp only [Bool.false_eq_true, ite_false]
    split
    · exact (step _ _ _ (by decide)).trans (step _ _ _ (by decide))
    · exact ((step _ _ _ (by decide)).trans (step _ _ _ (by decide))).trans (step _ _ _ (by decide))

theorem random_retry_status (m : Mem) (B : Addr) (success : Bool) (attempts : Nat) :
    word (randomRetryMem m B success attempts) B Random.oStatus =
      if success then 1 else if attempts = 1 then 0 else 4 := by
  cases success with
  | true => exact word_writeW_self _ _ _ _
  | false =>
    simp only [randomRetryMem, Bool.false_eq_true, ite_false]
    split
    · rw [(writeW_outside _ B _ (by decide)).word (by decide) (by decide), word_writeW_self]
    · exact word_writeW_self _ _ _ _

theorem random_retry_attempts (m : Mem) (B : Addr) (success : Bool) (attempts : Nat) :
    word (randomRetryMem m B success attempts) B Random.oAttempts =
      if success then word m B Random.oAttempts else BitVec.ofNat 64 (attempts - 1) := by
  cases success with
  | true => exact (writeW_outside _ B _ (by decide)).word (by decide) (by decide)
  | false =>
    simp only [randomRetryMem, Bool.false_eq_true, ite_false]
    split
    · exact word_writeW_self _ _ _ _
    · rw [(writeW_outside _ B _ (by decide)).word (by decide) (by decide), word_writeW_self]

theorem random_retry_word (m : Mem) (B : Addr) (success : Bool) (attempts d : Nat)
    (hd : d + 8 ≤ 2 ^ 64) (ha : d + 8 ≤ 152 ∨ 160 ≤ d) (hs : d + 8 ≤ 192 ∨ 200 ≤ d) :
    word (randomRetryMem m B success attempts) B d = word m B d := by
  have wa (m : Mem) (v : BitVec 64) : word (m.writeW (off B Random.oAttempts) v) B d = word m B d :=
    (writeW_outside _ _ _ (by decide)).word ha hd
  have ws (m : Mem) (v : BitVec 64) : word (m.writeW (off B Random.oStatus) v) B d = word m B d :=
    (writeW_outside _ _ _ (by decide)).word hs hd
  cases success with
  | true => exact ws _ _
  | false =>
    unfold randomRetryMem
    simp only [Bool.false_eq_true, ite_false]
    split <;> simp only [wa, ws]

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.RandomSignSample`, which this module and modules that import it used -/

section

/-! A nonce sample advances consumption while preserving the signing-loop state. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64
open VG.Proof.Dsa.Random

theorem random_sign_sample {extra : Nat} {s t : State} {h : RandomSignABI extra s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {used fuel : Nat}
    (hr : RandomSignRunning h hq used fuel t) :
    WP isa Random.sample t fun u =>
      u.gpr .x0 = BitVec.ofNat 64 (sampleStatus (VG.Proof.Dsa.randomSignDraw (randomInput s) used)) ∧
      word u.mem (randomBase s) Random.oStatus =
        BitVec.ofNat 64 (sampleStatus (VG.Proof.Dsa.randomSignDraw (randomInput s) used)) ∧
      RandomSignRunning h hq (used + (VG.Proof.Dsa.randomSignDraw (randomInput s) used).used) fuel u ∧
      (∀ k, (VG.Proof.Dsa.randomSignDraw (randomInput s) used).scalar = some k →
        Spec.Rsa.bytesAt u.mem (off (randomBase s) Random.oNonce) (s.gpr .x6).toNat =
          Spec.Dsa.encodeBE (s.gpr .x6).toNat k) := by
  obtain ⟨m, draws, hready⟩ := hr.ready
  let C := randomContextOf h m hq
  have he : randomRemaining C used 128 = VG.Proof.Dsa.randomSignDraw (randomInput s) used := by
    unfold randomRemaining VG.Proof.Dsa.randomSignDraw
    change VG.Spec.Dsa.Random.sample (Spec.Dsa.decodeBE (randomQBytes s)) 128 _ = _
    rw [random_q_decode]
    rfl
  refine WP.mono (random_sample_encoded (C := C) hq hready)
    fun u ⟨hstatus, hstatusWord, _, hnonce, hf, ⟨draws', hready'⟩, hk⟩ => ?_
  rw [he] at hstatus hstatusWord hnonce hready'
  have fits : ∀ r ∈ randomWriteRanges, r.1 + r.2 ≤ Random.frameBytes := by decide
  have hf0 := InScr.of_frm hready.frame fits
  have hf1 := InScr.of_frm hf fits
  have hmem : InScr (randomBase s) Random.frameBytes t.mem u.mem :=
    fun x hx => (hf1 x hx).trans (hf0 x hx).symm
  have hw (d : Nat) (hd : d + 8 ≤ 144 ∨ d = 152 ∨ d = 232) : word u.mem (randomBase s) d = word t.mem (randomBase s) d := by
    have sep : ∀ r ∈ randomWriteRanges, d + 8 ≤ r.1 ∨ r.1 + r.2 ≤ d := by
      intro r hmem
      simp only [randomWriteRanges, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl <;> dsimp only <;> omega_using [hd]
    exact (hf.word_eq sep (by omega_using [hd])).trans (hready.frame.word_eq sep (by omega_using [hd])).symm
  have hkv : Keep randomVolatile t u := hk.mono (by decide)
  refine ⟨hstatus, hstatusWord, ⟨⟨m, draws', hready'⟩, hr.saved.congr (fun d _ hd => hw d (Or.inl hd)),
    (hw _ (Or.inr (Or.inl rfl))).trans hr.attempts, hk.rd.trans hr.rd, hk.wr.trans hr.wr,
    hr.key.congrK hmem hk, hr.digest.congrK hmem hk,
    fun r hc => (hkv.gpr r (random_saved_not_volatile hc)).trans (hr.callee r hc),
    fun r hc => (hk.vcs r hc).trans (hr.vectors r hc),
    (hw _ (Or.inr (Or.inr rfl))).trans hr.link⟩, ?_⟩
  intro k hk
  have hn := hnonce k hk
  simpa only [C, randomContextOf, random_q_length h, Random.oNonce] using hn

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.RandomSignSingle`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.RandomSignCallValue`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.RandomSignCallResult`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.RandomSignCallPre`, which this module and modules that import it used -/

section

/-! Establish the supplied-nonce contract at the wrapper's call boundary. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

theorem random_call_pre {extra : Nat} {s t : State} (h : RandomSignABI extra s)
    (hsp : t.sp = randomBase s)
    (hw : ∀ i < 3, word t.mem (randomBase s) (8 * i) = randomCallArg s i)
    (hdi : t.gpr .x0 = s.gpr .x0) (hsi : t.gpr .x1 = s.gpr .x1)
    (hdx : t.gpr .x2 = s.gpr .x3) (hcx : t.gpr .x3 = s.gpr .x4)
    (h8 : t.gpr .x4 = s.gpr .x5) (h9 : t.gpr .x5 = off (randomBase s) Random.oNonce)
    (h6 : t.gpr .x6 = s.gpr .x6) (h7 : t.gpr .x7 = s.gpr .x7) :
    (Spec.Dsa.signContract abi extra).pre (t.callEntry.withRegions (randomCallRd s) (randomCallWr s)) := by
  have hE (i : Nat) (hi : i < 3) :
      stackArg (t.callEntry.withRegions (randomCallRd s) (randomCallWr s)) i = randomCallArg s i :=
    (random_call_stackArg hsp _ _ i).trans (hw i hi)
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs]
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs]
  simp only [hdi, hsi, hdx, hcx, h8, h9, h6, h7, hsp,
    random_call_stackArgAddr hsp, hE 0 (by decide), hE 1 (by decide), hE 2 (by decide)]
  simp only [randomCallArg, randomCallRd, randomCallWr]
  have hl := h.stackLower
  have hb := (s.sp).isLt
  have hq : (s.gpr .x6).toNat ≤ 32 := by
    have hh := h.lengths
    unfold Spec.Dsa.lengthsValid at hh
    omega_using [hh]
  have hk := randomStackBase_toNat h
  have hR : (randomBase s).toNat = (randomStackBase extra s).toNat + extra := by
    rw [random_frameBase extra s, randomStack_offset_toNat h (by omega_using [])]
  have hN : (off (randomBase s) Random.oNonce).toNat =
      (randomStackBase extra s).toNat + (extra + 200) := by
    rw [random_nonceBase extra s, randomStack_offset_toNat h (by omega_using [])]
  have sM : Region.Sub ⟨off (randomBase s) Random.oNonce, (s.gpr .x6).toNat⟩
      (below (s.sp) (extra + 256)) := by
    rw [random_nonceBase extra s]
    exact Offset.sub_base _ (by omega_using [hq])
  have sA : Region.Sub ⟨randomBase s, 24⟩ (below (s.sp) (extra + 256)) := by
    rw [random_frameBase extra s]
    exact Offset.sub_base _ (by omega_using [])
  have sK : Region.Sub (below (randomBase s) extra) (below (s.sp) (extra + 256)) := by
    change Region.Sub ⟨randomBase s - BitVec.ofNat 64 extra, extra⟩ _
    rw [random_calleeBase extra s]
    exact Region.sub_prefix (by omega_using [])
  have dKM : (below (randomBase s) extra).Disjoint
      ⟨off (randomBase s) Random.oNonce, (s.gpr .x6).toNat⟩ := by
    change (⟨randomBase s - BitVec.ofNat 64 extra, extra⟩ : Region).Disjoint _
    rw [random_calleeBase extra s, random_nonceBase extra s]
    exact Offset.base_disjoint _ (by omega_using []) (by omega_using [hl, hq])
  have dKA : (below (randomBase s) extra).Disjoint ⟨randomBase s, 24⟩ := by
    change (⟨randomBase s - BitVec.ofNat 64 extra, extra⟩ : Region).Disjoint _
    rw [random_calleeBase extra s, random_frameBase extra s]
    exact Offset.base_disjoint _ (by omega_using []) (by omega_using [hl])
  refine ⟨?_, by omega_using [hl, hk, hR], trivial, trivial, h.outKey, (h.stackOut.sub_left sM).symm,
    h.outDigest, h.outScratch, (h.stackOut.sub_left sA).symm, h.keyScratch,
    h.stackScratch.sub_left sM, h.digestScratch, (h.stackScratch.sub_left sA).symm,
    ?_, h.outBound, h.keyBound, by omega_using [hl, hq, hk, hN], h.digestBound, h.scratchBound,
    h.lengths, h.outLength, h.keyLength, ?_⟩
  · cases extra <;> simp only <;> omega_using [hR]
  · cases extra with
    | zero => trivial
    | succ n => exact ⟨h.stackOut.sub_left sK, h.stackKey.sub_left sK, dKM,
        h.stackDigest.sub_left sK, h.stackScratch.sub_left sK, dKA⟩
  · have hh := h.scratchLength
    unfold Spec.Dsa.randomSignScratchWords at hh
    omega_using [hh]

end VG.Proof.Dsa.AArch64

end

end

/-! The supplied-nonce call's result, with the wrapper's argument mapping. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

def randomCallResult (s t : State) : Option (List Byte) :=
  Spec.Dsa.signBytes (s.gpr .x5).toNat (s.gpr .x6).toNat
    (Spec.Rsa.bytesAt t.callEntry.mem (s.gpr .x3) (s.gpr .x4).toNat)
    (Spec.Rsa.bytesAt t.callEntry.mem (off (randomBase s) Random.oNonce) (s.gpr .x6).toNat)
    (Spec.Rsa.bytesAt t.callEntry.mem (s.gpr .x7) (stackArg s 0).toNat)

/-- The signer's validity of the wrapper's key, which the signer's contract
asks of the key it is called with. -/
def RandomValid (S : Signer) (s : State) : Prop :=
  S.valid (randomInput s).pLen (randomInput s).qLen (randomInput s).key = true

/-- The signer's contract at the wrapper's call boundary, for a key the
signer accepts. -/
theorem random_call_pre_with (S : Signer) {s t : State} (h : RandomSignABI S.stack s)
    (hsp : t.sp = randomBase s)
    (hw : ∀ i < 3, word t.mem (randomBase s) (8 * i) = randomCallArg s i)
    (hdi : t.gpr .x0 = s.gpr .x0) (hsi : t.gpr .x1 = s.gpr .x1)
    (hdx : t.gpr .x2 = s.gpr .x3) (hcx : t.gpr .x3 = s.gpr .x4)
    (h8 : t.gpr .x4 = s.gpr .x5) (h9 : t.gpr .x5 = off (randomBase s) Random.oNonce)
    (h6 : t.gpr .x6 = s.gpr .x6) (h7 : t.gpr .x7 = s.gpr .x7)
    (hkey : Spec.Rsa.bytesAt t.mem (s.gpr .x3) (s.gpr .x4).toNat = (randomInput s).key)
    (hv : RandomValid S s) :
    (signContractWith S.valid abi S.stack).pre (t.callEntry.withRegions (randomCallRd s) (randomCallWr s)) := by
  refine signWith_of_pre (random_call_pre h hsp hw hdi hsi hdx hcx h8 h9 h6 h7) ?_
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr _ (r := .x4) (by decide), State.callEntry_gpr _ (r := .x6) (by decide),
    State.callEntry_gpr _ (r := .x2) (by decide), State.callEntry_gpr _ (r := .x3) (by decide),
    h8, h6, hdx, hcx, hkey]
  exact hv

theorem random_signer_outcome (S : Signer) {s t : State} (h : RandomSignABI S.stack s)
    (hsp : t.sp = randomBase s)
    (hw : ∀ i < 3, word t.mem (randomBase s) (8 * i) = randomCallArg s i)
    (hdi : t.gpr .x0 = s.gpr .x0) (hsi : t.gpr .x1 = s.gpr .x1)
    (hdx : t.gpr .x2 = s.gpr .x3) (hcx : t.gpr .x3 = s.gpr .x4)
    (h8 : t.gpr .x4 = s.gpr .x5) (h9 : t.gpr .x5 = off (randomBase s) Random.oNonce)
    (h6 : t.gpr .x6 = s.gpr .x6) (h7 : t.gpr .x7 = s.gpr .x7)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr)
    (hkey : Spec.Rsa.bytesAt t.mem (s.gpr .x3) (s.gpr .x4).toNat = (randomInput s).key)
    (hv : RandomValid S s) :
    WP isa (.call S.name S.code) t fun u =>
      u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧
      (∀ r ∈ preserved, r ≠ .x30 → u.gpr r = t.gpr r) ∧
      Frame (randomCallWr s ++ [below (randomBase s) S.stack]) t.mem u.mem ∧
      ((u.gpr .x0).setWidth 32).toNat = Spec.Dsa.signStatus (randomCallResult s t) ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .x0) (s.gpr .x1).toNat =
        (randomCallResult s t).getD (List.replicate (s.gpr .x1).toNat 0) ∧
      ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64 := by
  obtain ⟨hc, hcw⟩ := random_call_covers h hrd hwr
  refine WP.mono (random_signer_call S
    (random_call_pre_with S h hsp hw hdi hsi hdx hcx h8 h9 h6 h7 hkey hv) hc hcw)
    fun u ⟨hur, huw, husp, huc, hf, hp, hv⟩ => ?_
  have hE (i : Nat) (hi : i < 3) :
      stackArg (t.callEntry.withRegions (randomCallRd s) (randomCallWr s)) i = randomCallArg s i :=
    (random_call_stackArg hsp _ _ i).trans (hw i hi)
  sig_post [signContractWith, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs] at hp
  sig_post [signContractWith, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs] at hp
  simp only [hdi, hsi, hdx, hcx, h8, h9, h6, h7, hE 0 (by decide),
    randomCallArg] at hp
  exact ⟨hur, huw, husp, huc, by rw [hsp] at hf; exact hf, hp.1, hp.2, hv⟩

end VG.Proof.Dsa.AArch64

end

end

/-! Setting the link register at call entry leaves the signing inputs unchanged. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

theorem random_callResult_plain {extra : Nat} {s t : State} (_h : RandomSignABI extra s)
    (_hsp : t.sp = randomBase s) :
    randomCallResult s t = Spec.Dsa.signBytes (s.gpr .x5).toNat (s.gpr .x6).toNat
      (Spec.Rsa.bytesAt t.mem (s.gpr .x3) (s.gpr .x4).toNat)
      (Spec.Rsa.bytesAt t.mem (off (randomBase s) Random.oNonce) (s.gpr .x6).toNat)
      (Spec.Rsa.bytesAt t.mem (s.gpr .x7) (stackArg s 0).toNat) := rfl

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.RandomSignArgsSaved`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.RandomSignArgs`, which only this module used -/

section

/-! Set up the supplied-nonce signer's register and stack arguments. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def randomSignOutgoing : List (Nat × Nat) :=
  [(Random.oDigestLen, 0), (Random.oScratch, 8), (Random.oScratchLen, 16)]

theorem random_signOutgoing_frame (m : Mem) (B : Addr) :
    Outside B 0 40 m (randomSlotsMem B m randomSignOutgoing) := by
  apply random_slots_outside
  intro p hp
  simp only [randomSignOutgoing, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

/-- Each outgoing stack word has the original saved argument value. -/
theorem random_signOutgoing_words (m : Mem) (B : Addr) :
    ∀ p ∈ randomSignOutgoing,
      word (randomSlotsMem B m randomSignOutgoing) B p.2 = word m B p.1 := by
  intro p hp
  simp only [randomSignOutgoing, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;>
    simp only [randomSignOutgoing, randomSlotsMem, Random.oDigestLen, Random.oScratch, Random.oScratchLen] <;>
    simp (disch := omega_using []) only [word_writeW_self, random_word_write_other]

theorem random_signCallArgs_ok {s : State} {B : Addr}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B) :
    WP isa (.block RandomSign.callArgs) s fun t =>
      t.gpr .x0 = word s.mem B Random.oOut ∧
      t.gpr .x1 = word s.mem B Random.oOutLen ∧
      t.gpr .x2 = word s.mem B Random.oKey ∧
      t.gpr .x3 = word s.mem B Random.oKeyLen ∧
      t.gpr .x4 = word s.mem B Random.oPLen ∧ t.gpr .x5 = off B Random.oNonce ∧
      t.gpr .x6 = word s.mem B Random.oQLen ∧ t.gpr .x7 = word s.mem B Random.oDigest ∧
      t.mem = randomSlotsMem B s.mem randomSignOutgoing ∧
      Keep [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x15] s t := by
  unfold RandomSign.callArgs
  rw [WP.block_append_iff]
  refine WP.mono (random_copySlots_ok randomSignOutgoing hsp
    (by intro p hp; simp only [randomSignOutgoing, List.mem_cons, List.not_mem_nil, or_false] at hp;
        rcases hp with rfl | rfl | rfl <;> decide)
    (fun p hp => hs.ld (by
      simp only [randomSignOutgoing, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> decide))
    (fun p hp => hs.st (by
      simp only [randomSignOutgoing, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> decide))) fun u ⟨hum, hku⟩ => ?_
  have hus := hs.congr hku.wr
  have husp := hku.sp.trans hsp
  have hw (d : Nat) (hd : 40 ≤ d) (hb : d + 8 ≤ 2 ^ 64) : word u.mem B d = word s.mem B d := by
    rw [hum]
    exact (random_signOutgoing_frame _ _).word (Or.inr hd) hb
  refine WP.mono (WP.keep [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] (Q := fun t =>
      t.gpr .x0 = word s.mem B Random.oOut ∧
      t.gpr .x1 = word s.mem B Random.oOutLen ∧
      t.gpr .x2 = word s.mem B Random.oKey ∧
      t.gpr .x3 = word s.mem B Random.oKeyLen ∧
      t.gpr .x4 = word s.mem B Random.oPLen ∧ t.gpr .x5 = off B Random.oNonce ∧
      t.gpr .x6 = word s.mem B Random.oQLen ∧ t.gpr .x7 = word s.mem B Random.oDigest ∧
      t.mem = u.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, hm⟩, hkt⟩ =>
      ⟨h0, h1, h2, h3, h4, h5, h6, h7, hm.trans hum, (hku.trans hkt).mono (by decide)⟩
  brun [husp, exec_addSp (show Random.oNonce < 4096 by decide),
    exec_ldrSp (show Random.oOut % 8 = 0 ∧ Random.oOut < 32768 by decide),
    hus.ld (d := Random.oOut) (by decide), hw Random.oOut (by decide) (by decide),
    exec_ldrSp (show Random.oOutLen % 8 = 0 ∧ Random.oOutLen < 32768 by decide),
    hus.ld (d := Random.oOutLen) (by decide), hw Random.oOutLen (by decide) (by decide),
    exec_ldrSp (show Random.oKey % 8 = 0 ∧ Random.oKey < 32768 by decide),
    hus.ld (d := Random.oKey) (by decide), hw Random.oKey (by decide) (by decide),
    exec_ldrSp (show Random.oKeyLen % 8 = 0 ∧ Random.oKeyLen < 32768 by decide),
    hus.ld (d := Random.oKeyLen) (by decide), hw Random.oKeyLen (by decide) (by decide),
    exec_ldrSp (show Random.oPLen % 8 = 0 ∧ Random.oPLen < 32768 by decide),
    hus.ld (d := Random.oPLen) (by decide), hw Random.oPLen (by decide) (by decide),
    exec_ldrSp (show Random.oQLen % 8 = 0 ∧ Random.oQLen < 32768 by decide),
    hus.ld (d := Random.oQLen) (by decide), hw Random.oQLen (by decide) (by decide),
    exec_ldrSp (show Random.oDigest % 8 = 0 ∧ Random.oDigest < 32768 by decide),
    hus.ld (d := Random.oDigest) (by decide), hw Random.oDigest (by decide) (by decide)]

end VG.Proof.Dsa.AArch64

end

end


/-! Map the wrapper's saved arguments to the supplied-nonce signing ABI. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_saved_outgoing {s : State} {m : Mem} (h : RandomSaved s m) :
    ∀ i < 3, word (randomSlotsMem (randomBase s) m randomSignOutgoing) (randomBase s) (8 * i) = randomCallArg s i := by
  intro i hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega_using [hi]
  rcases cases with rfl | rfl | rfl
  · exact (random_signOutgoing_words m _ (104, 0) (by decide)).trans
      (h (104, stackArg s 0) (by simp [randomSavedValues]))
  · exact (random_signOutgoing_words m _ (128, 8) (by decide)).trans
      (h (128, stackArg s 3) (by simp [randomSavedValues]))
  · exact (random_signOutgoing_words m _ (136, 16) (by decide)).trans
      (h (136, stackArg s 4) (by simp [randomSavedValues]))

theorem random_callArgs_saved {s t : State} (hs : Scr t (randomBase s) Random.frameBytes)
    (hsp : t.sp = randomBase s) (hv : RandomSaved s t.mem) :
    WP isa (.block RandomSign.callArgs) t fun u =>
      u.gpr .x0 = s.gpr .x0 ∧ u.gpr .x1 = s.gpr .x1 ∧
      u.gpr .x2 = s.gpr .x3 ∧ u.gpr .x3 = s.gpr .x4 ∧
      u.gpr .x4 = s.gpr .x5 ∧ u.gpr .x5 = off (randomBase s) Random.oNonce ∧
      u.gpr .x6 = s.gpr .x6 ∧ u.gpr .x7 = s.gpr .x7 ∧
      (∀ i < 3, word u.mem (randomBase s) (8 * i) = randomCallArg s i) ∧
      RandomSaved s u.mem ∧ Outside (randomBase s) 0 40 t.mem u.mem ∧
      Keep [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x15] t u := by
  refine WP.mono (random_signCallArgs_ok hs hsp) fun u ⟨h0, h1, h2, h3, h4, h5, h6, h7, hm, hk⟩ => ?_
  have hf : Outside (randomBase s) 0 40 t.mem u.mem := by rw [hm]; exact random_signOutgoing_frame _ _
  exact ⟨h0.trans (hv (40, s.gpr .x0) (by simp [randomSavedValues])),
    h1.trans (hv (48, s.gpr .x1) (by simp [randomSavedValues])),
    h2.trans (hv (64, s.gpr .x3) (by simp [randomSavedValues])),
    h3.trans (hv (72, s.gpr .x4) (by simp [randomSavedValues])),
    h4.trans (hv (80, s.gpr .x5) (by simp [randomSavedValues])), h5,
    h6.trans (hv (88, s.gpr .x6) (by simp [randomSavedValues])),
    h7.trans (hv (96, s.gpr .x7) (by simp [randomSavedValues])),
    fun i hi => by rw [hm]; exact random_saved_outgoing hv i hi,
    hv.congr (fun d hd hd' => hf.word (Or.inr hd) (by omega_using [hd'])), hf, hk⟩

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.RandomSignCallRetry`, which only this module used -/

section

/-! Compose supplied-nonce signing with link restoration and bounded retry. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_signer_retry (S : Signer) {s t : State} {attempts : Nat} (h : RandomSignABI S.stack s)
    (hsp : t.sp = randomBase s)
    (hw : ∀ i < 3, word t.mem (randomBase s) (8 * i) = randomCallArg s i)
    (h0 : t.gpr .x0 = s.gpr .x0) (h1 : t.gpr .x1 = s.gpr .x1)
    (h2 : t.gpr .x2 = s.gpr .x3) (h3 : t.gpr .x3 = s.gpr .x4)
    (h4 : t.gpr .x4 = s.gpr .x5) (h5 : t.gpr .x5 = off (randomBase s) Random.oNonce)
    (h6 : t.gpr .x6 = s.gpr .x6) (h7 : t.gpr .x7 = s.gpr .x7)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr)
    (hn : word t.mem (randomBase s) Random.oAttempts = BitVec.ofNat 64 attempts)
    (hlink : word t.mem (randomBase s) RandomSign.oLink = t.gpr .x30)
    (hpos : 0 < attempts) (hbound : attempts < 2 ^ 64)
    (hkey : Spec.Rsa.bytesAt t.mem (s.gpr .x3) (s.gpr .x4).toNat = (randomInput s).key)
    (hv : RandomValid S s) :
    WP isa (.seq (.call S.name S.code) RandomSign.callFinish) t fun u =>
      u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧ (∀ r ∈ preserved, u.gpr r = t.gpr r) ∧
      (∃ m : Mem,
        Frame (randomCallWr s ++ [below (randomBase s) S.stack]) t.mem m ∧
        Spec.Rsa.bytesAt m (s.gpr .x0) (s.gpr .x1).toNat =
          (randomCallResult s t).getD (List.replicate (s.gpr .x1).toNat 0) ∧
        u.mem = randomRetryMem m (randomBase s) (randomCallResult s t).isSome attempts) ∧
      (∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64) := by
  refine WP.seq (WP.mono (random_signer_outcome S h hsp hw h0 h1 h2 h3 h4 h5 h6 h7 hrd hwr hkey hv)
    fun u ⟨hur, huw, husp, huc, hf, hstatus, hout, hv⟩ => ?_)
  have hus : Scr u (randomBase s) Random.frameBytes :=
    (random_alloc_scr h).congr (huw.trans hwr)
  have hun : word u.mem (randomBase s) Random.oAttempts = BitVec.ofNat 64 attempts :=
    (random_frame_words (random_call_frameBytes h hf) (by decide)).trans hn
  have hul : word u.mem (randomBase s) RandomSign.oLink = t.gpr .x30 :=
    (random_frame_words (random_call_frameBytes h hf) (by decide)).trans hlink
  have hra : (u.gpr .x0).setWidth 32 = if (randomCallResult s t).isSome then 1 else 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [hstatus]
    cases randomCallResult s t <;> rfl
  refine WP.mono (random_callFinish_ok (randomCallResult s t).isSome hus
      (husp.trans hsp) hra hun hpos hbound) fun w ⟨hwm, hwl, hkw⟩ => ?_
  refine ⟨hkw.rd.trans hur, hkw.wr.trans huw, hkw.sp.trans husp, ?_,
    ⟨u.mem, hf, hout, hwm⟩, fun r hr => (hkw.vcs r hr).trans (hv r hr)⟩
  intro r hr
  by_cases hl : r = .x30
  · subst r; exact hwl.trans hul
  · exact (hkw.gpr r (by revert hr hl; cases r <;> decide)).trans (huc r hr hl)

end VG.Proof.Dsa.AArch64

end

end

/-! One complete supplied-nonce signing step, including arguments and retry state. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/RandomRestore.lean`, which only this module imported.
section

/-! Resume sampling after a signer call that preserves its inputs and private state. -/
section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

def randomReadySlots : List Nat := [112, 120, 144, 176, 88, 184, 168, 160]

/-- Each sampling invocation tracks its own exact memory effects. The outer
signing loop separately tracks output and arithmetic-scratch writes. -/
theorem RandomReady.restore {C : RandomContext} {used draws : Nat} {s t : State}
    (h : RandomReady C used draws s) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hsp : t.sp = s.sp)
    (hwords : ∀ d ∈ randomReadySlots, word t.mem C.B d = word s.mem C.B d)
    (hrand : ∀ i < C.rand.length, t.mem (C.R + BitVec.ofNat 64 i) = s.mem (C.R + BitVec.ofNat 64 i))
    (hq : ∀ i < C.qBytes.length, t.mem (C.Q + BitVec.ofNat 64 i) = s.mem (C.Q + BitVec.ofNat 64 i))
    (hpad : ∀ i < C.qBytes.length - (VG.Proof.Dsa.significant C.qBytes).1,
      t.mem (off C.B (200 + i)) = s.mem (off C.B (200 + i))) :
    RandomReady { C with initialMem := t.mem } used draws t := by
  refine ⟨h.scr.congr hwr, hsp.trans h.sp,
    (hwords _ (by decide)).trans h.rand,
    (hwords _ (by decide)).trans h.randLen,
    (hwords _ (by decide)).trans h.usedWord,
    (hwords _ (by decide)).trans h.width,
    (hwords _ (by decide)).trans h.qLen,
    (hwords _ (by decide)).trans h.mask,
    (hwords _ (by decide)).trans h.q,
    (hwords _ (by decide)).trans h.draws,
    ⟨fun i hi => by rw [hrd, hwr]; exact h.randSrc.rd i hi,
      fun i hi => (hrand i hi).trans (h.randSrc.val i hi), h.randSrc.out⟩,
    ⟨fun i hi => by rw [hrd, hwr]; exact h.qSrc.rd i hi,
      fun i hi => (hq i hi).trans (h.qSrc.val i hi), h.qSrc.out⟩,
    h.usedBound, Frm.refl _ _ _, fun i hi => (hpad i hi).trans (h.padding i hi)⟩

end VG.Proof.Dsa.AArch64
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/RandomSignResume.lean`, which only this module imported.
section

/-! Restore the complete signing-loop invariant after a supplied-nonce call. -/
section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem RandomSignRunning.after_signer {extra : Nat} {s t a u : State} {m : Mem}
    {h : RandomSignABI extra s} {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {used fuel : Nat}
    (hr : RandomSignRunning h hq used fuel t) (success : Bool)
    (hargs : Outside (randomBase s) 0 40 t.mem a.mem) (hka : Keep randomVolatile t a)
    (hf : Frame (randomCallWr s ++ [below (randomBase s) extra]) a.mem m)
    (hm : u.mem = randomRetryMem m (randomBase s) success fuel)
    (hrd : u.rd = a.rd) (hwr : u.wr = a.wr)
    (hcs : ∀ r ∈ preserved, u.gpr r = a.gpr r)
    (hsp : u.sp = a.sp)
    (hv : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64) :
    RandomSignRunning h hq used (if success then fuel else fuel - 1) u := by
  obtain ⟨cm, draws, hready⟩ := hr.ready
  have hargsF := InScr.of_outside hargs (show 0 + 40 ≤ Random.frameBytes by decide)
  have hpostF : InScr (randomBase s) Random.frameBytes m u.mem := by
    rw [hm]
    exact InScr.of_outside (random_retry_outside _ _ _ _) (by decide)
  have hkeyA := hr.key.congrK hargsF hka
  have hdigestA := hr.digest.congrK hargsF hka
  have hrandA := hready.randSrc.congrK hargsF hka
  have hkeyU := random_call_source hkeyA hf hpostF hrd hwr
    (by simpa only [randomInput, bytesAt_length] using h.outKey.symm)
    (by simpa only [randomInput, bytesAt_length] using h.keyScratch)
    (by simpa only [randomInput, bytesAt_length] using h.stackKey)
    (by simp only [randomInput, bytesAt_length]; exact Nat.le_of_lt (s.gpr .x4).isLt)
  have hdigestU := random_call_source hdigestA hf hpostF hrd hwr
    (by simpa only [randomInput, bytesAt_length] using h.outDigest.symm)
    (by simpa only [randomInput, bytesAt_length] using h.digestScratch)
    (by simpa only [randomInput, bytesAt_length] using h.stackDigest)
    (by simp only [randomInput, bytesAt_length]; exact Nat.le_of_lt (stackArg s 0).isLt)
  have hrandU := random_call_source hrandA hf hpostF hrd hwr
    (by simpa only [randomContextOf, randomInput, bytesAt_length] using h.outRand.symm)
    (by simpa only [randomContextOf, randomInput, bytesAt_length] using h.randScratch)
    (by simpa only [randomContextOf, randomInput, bytesAt_length] using h.stackRand)
    (by simp only [randomContextOf, randomInput, bytesAt_length]; exact Nat.le_of_lt (stackArg s 2).isLt)
  have hqU : Src u (randomBase s) Random.frameBytes (s.gpr .x3 + s.gpr .x5) (randomQBytes s) := by
    have hx := random_src_take (random_src_drop hkeyU (randomInput s).pLen) (randomInput s).qLen
    simpa only [randomQBytes, randomInput, ofNat_toNat64] using hx
  have hword (d : Nat) (hd : 40 ≤ d) (hb : d + 8 ≤ Random.frameBytes)
      (ha : d + 8 ≤ 152 ∨ 160 ≤ d) (hz : d + 8 ≤ 192 ∨ 200 ≤ d) :
      word u.mem (randomBase s) d = word t.mem (randomBase s) d := by
    rw [hm, random_retry_word _ _ _ _ d (by unfold Random.frameBytes at hb; omega) ha hz,
      random_frame_words (random_call_frameBytes h hf) hb, hargs.word (Or.inr hd) (by unfold Random.frameBytes at hb; omega)]
  have hkeepSp : u.sp = t.sp := hsp.trans hka.sp
  have hnew := hready.restore (hrd.trans hka.rd) (hwr.trans hka.wr) hkeepSp
    (by
      intro d hd
      simp only [randomReadySlots, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hword _ (by decide) (by decide) (by decide) (by decide))
    (fun i hi => (hrandU.val i hi).trans (hready.randSrc.val i hi).symm)
    (fun i hi => (hqU.val i hi).trans (hready.qSrc.val i hi).symm)
    (by
      intro i hi
      have hlen := (randomContextOf h cm hq).qlen
      change u.mem (off (randomBase s) (200 + i)) = t.mem (off (randomBase s) (200 + i))
      rw [hm, random_outside_offset (random_retry_outside _ _ _ _) (by omega) (Or.inr (by omega)),
        random_call_frameBytes h hf _ (by unfold Random.frameBytes; omega),
        random_outside_offset hargs (by omega) (Or.inr (by omega))])
  refine ⟨⟨u.mem, draws, hnew⟩, hr.saved.congr (fun d hd hb => hword d hd (by unfold Random.frameBytes; omega)
    (Or.inl (by omega)) (Or.inl (by omega))), ?_, (hrd.trans hka.rd).trans hr.rd,
    (hwr.trans hka.wr).trans hr.wr, hkeyU, hdigestU,
    fun r hc => ((hcs r hc).trans (hka.gpr r (random_saved_not_volatile hc))).trans (hr.callee r hc),
    fun r hc => (hv r hc).trans (hr.vectors r hc),
    (hword _ (by decide) (by decide) (by decide) (by decide)).trans hr.link⟩
  rw [hm, random_retry_attempts, random_frame_words (random_call_frameBytes h hf) (by decide),
    hargs.word (by decide) (by decide), hr.attempts]
  cases success <;> rfl

end VG.Proof.Dsa.AArch64
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def randomSingleResult (s : State) (k : Nat) : Option (List Byte) :=
  Spec.Dsa.signBytes (randomInput s).pLen (randomInput s).qLen (randomInput s).key
    (Spec.Dsa.encodeBE (randomInput s).qLen k) (randomInput s).digest

theorem random_sign_single (S : Signer) {s t : State} {h : RandomSignABI S.stack s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {used fuel k : Nat}
    (hr : RandomSignRunning h hq used fuel t) (hpos : 0 < fuel) (hbound : fuel < 2 ^ 64)
    (hnonce : Spec.Rsa.bytesAt t.mem (off (randomBase s) Random.oNonce) (s.gpr .x6).toNat =
      Spec.Dsa.encodeBE (s.gpr .x6).toNat k) (hval : RandomValid S s) :
    WP isa (.seq (.block RandomSign.callArgs)
      (.seq (.call S.name S.code) RandomSign.callFinish)) t fun u =>
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
    omega_using [hl]
  have hkey : Spec.Rsa.bytesAt a.mem (s.gpr .x3) (s.gpr .x4).toNat = (randomInput s).key := by
    simpa only [randomInput, bytesAt_length] using sourceBytes_eq hkeyA
  have hres : randomCallResult s a = randomSingleResult s k := by
    rw [random_callResult_plain h hspA]
    have hdigest : Spec.Rsa.bytesAt a.mem (s.gpr .x7) (stackArg s 0).toNat = (randomInput s).digest := by
      simpa only [randomInput, bytesAt_length] using sourceBytes_eq hdigestA
    have hnonceA := (random_outside_bytes hargs
      (show Random.oNonce + (s.gpr .x6).toNat ≤ 2 ^ 64 by unfold Random.oNonce; omega_using [hqbound])
      (Or.inr (show 0 + 40 ≤ Random.oNonce by decide))).trans hnonce
    rw [hkey, hdigest, hnonceA]
    rfl
  have hna : word a.mem (randomBase s) Random.oAttempts = BitVec.ofNat 64 fuel :=
    (hargs.word (by decide) (by decide)).trans hr.attempts
  have hlink : word a.mem (randomBase s) RandomSign.oLink = a.gpr .x30 := by
    rw [hargs.word (by decide) (by decide), hr.link,
      hka.gpr .x30 (by decide), hr.callee .x30 (by simp [preserved])]
  refine WP.mono (random_signer_retry S h hspA hw hdi hsi hdx hcx h8 h9 h6 h7
    (hka.rd.trans hr.rd) (hka.wr.trans hr.wr) hna hlink hpos hbound hkey hval)
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

end

end

/-! Execute one randomized signing attempt, including sampling and retries. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64
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
      Spec.Rsa.bytesAt u.mem (s.gpr .x0) (s.gpr .x1).toNat =
        (randomSingleResult s k).getD (List.replicate (s.gpr .x1).toNat 0)

theorem random_sign_test_one {t : State} :
    WP isa (.block [.subImm .x .x4 .x0 1]) t fun u =>
      (u.mem = t.mem ∧ (u.gpr .x4 == 0#64) = (t.gpr .x0 == 1#64)) ∧ Keep [.x0, .x4] t u := by
  refine WP.keep [.x0, .x4] ?_ rfl rfl rfl
  brun []
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, BitVec.sub_eq_iff_eq_add, BitVec.zero_add]


theorem random_sign_attempt (S : Signer) {s t : State} {h : RandomSignABI S.stack s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {used fuel : Nat}
    (hr : RandomSignRunning h hq used fuel t) (hpos : 0 < fuel) (hbound : fuel < 2 ^ 64)
    (hval : RandomValid S s) :
    WP isa (RandomSign.attempt S.name S.code) t (RandomSignAttemptPost h hq used fuel) := by
  unfold RandomSign.attempt
  refine WP.seq (WP.mono (random_sign_sample hr) fun a ⟨ha, hstatus, har, hnonce⟩ => ?_)
  refine WP.seq (WP.mono (random_sign_test_one (t := a)) fun b ⟨⟨hbm, hbz⟩, hkb⟩ => ?_)
  have hbr := har.congr hbm hkb
  rw [ha] at hbz
  cases hc : (VG.Proof.Dsa.randomSignDraw (randomInput s) used).scalar with
  | none =>
    have ht : (BitVec.ofNat 64 (sampleStatus (VG.Proof.Dsa.randomSignDraw (randomInput s) used)) == 1#64) = false := by
      simp only [sampleStatus, hc]
      split <;> rfl
    refine WP.ite false (by
      change some (b.gpr .x4 == 0#64) = _
      rw [hbz, ht]) (fun he => Bool.noConfusion he)
      (fun _ => WP.block_nil ?_)
    simp only [RandomSignAttemptPost, hc]
    exact ⟨hbr, by rw [hbm]; exact hstatus⟩
  | some k =>
    have ht : (BitVec.ofNat 64 (sampleStatus (VG.Proof.Dsa.randomSignDraw (randomInput s) used)) == 1#64) = true := by
      rw [sampleStatus, hc]
      rfl
    refine WP.ite true (by
      change some (b.gpr .x4 == 0#64) = _
      rw [hbz, ht]) (fun _ => ?_) (fun he => Bool.noConfusion he)
    refine WP.mono (random_sign_single S hbr hpos hbound (by rw [hbm]; exact hnonce k hc) hval) fun u hu => ?_
    simpa only [RandomSignAttemptPost, hc] using hu

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.RandomSignInvalid`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.RandomSignFinishResult`, which this module and modules that import it used -/

section

/-! Convert a completed retry loop into the public signature and consumption outputs. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/RandomSignLoop.lean`, which only this module imported.
section

/-! Functional correctness and termination of the outer signing retry loop. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64
open VG.Proof.Dsa.Random
open VG.Proof.Dsa (RandomSignResultRel randomSignRemaining randomSignDraw)

def RandomSignLoopPost {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)) (start : Nat) (result : Spec.Dsa.RandomSignResult) (t : State) : Prop :=
  (∃ fuel, RandomSignRunning h hq (start + result.used) fuel t) ∧
  word t.mem (randomBase s) Random.oStatus = BitVec.ofNat 64 result.status ∧
  (result.status = 1 → Spec.Rsa.bytesAt t.mem (s.gpr .x0) (s.gpr .x1).toNat =
    result.signature.getD (List.replicate (s.gpr .x1).toNat 0))

def RandomSignLoopInv {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)) (start : Nat) (result : Spec.Dsa.RandomSignResult)
    (fuel : Nat) (t : State) : Prop :=
  0 < fuel ∧ fuel ≤ 8 ∧ ∃ used, RandomSignRunning h hq used fuel t ∧
    RandomSignResultRel (randomInput s) start result used fuel

private theorem sample_none_status {draw : VG.Spec.Dsa.Random.Sample} (h : draw.scalar = none) :
    sampleStatus draw ≠ 1 ∧ (BitVec.ofNat 64 (sampleStatus draw) : BitVec 64) ≠ 4 := by
  simp only [sampleStatus, h]
  split <;> decide

private theorem attempt_progress (S : Signer) {s t : State} {h : RandomSignABI S.stack s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {start fuel : Nat} {result : Spec.Dsa.RandomSignResult}
    (hi : RandomSignLoopInv h hq start result fuel t) (hval : RandomValid S s) :
    WP isa (RandomSign.attempt S.name S.code) t fun u =>
      Scr u (randomBase s) Random.frameBytes ∧ u.sp = randomBase s ∧
      ((word u.mem (randomBase s) Random.oStatus ≠ 4 ∧ RandomSignLoopPost h hq start result u) ∨
        (word u.mem (randomBase s) Random.oStatus = 4 ∧ ∃ k < fuel, RandomSignLoopInv h hq start result k u)) := by
  obtain ⟨hpos, hbound, used, hr, hrel⟩ := hi
  cases fuel with
  | zero => omega
  | succ fuel =>
    refine WP.mono (random_sign_attempt S hr hpos (by omega_using [hbound]) hval) fun u hu => ?_
    cases hc : (randomSignDraw (randomInput s) used).scalar with
    | none =>
      simp only [RandomSignAttemptPost, hc] at hu
      obtain ⟨hr', hs⟩ := hu
      obtain ⟨_, _, hready⟩ := hr'.ready
      obtain ⟨_, hstatus, hused⟩ := hrel.sample_none hc
      have hne := sample_none_status hc
      refine ⟨hready.scr, hready.sp, Or.inl ⟨by rw [hs]; exact hne.2,
        ⟨fuel + 1, by rw [hused]; exact hr'⟩, by rw [hs, hstatus], ?_⟩⟩
      intro he
      exact False.elim (hne.1 (hstatus.symm.trans he))
    | some k =>
      simp only [RandomSignAttemptPost, hc] at hu
      cases hs : randomSingleResult s k with
      | some sig =>
        simp only [hs, Option.isSome_some, ite_true] at hu
        obtain ⟨hr', hword, hout⟩ := hu
        obtain ⟨_, _, hready⟩ := hr'.ready
        obtain ⟨hsig, hstatus, hused⟩ := hrel.success hc hs
        refine ⟨hready.scr, hready.sp, Or.inl ⟨by rw [hword]; decide,
          ⟨fuel + 1, by rw [hused]; exact hr'⟩, by rw [hword, hstatus]; rfl,
          fun _ => ?_⟩⟩
        rw [hsig]
        exact hout
      | none =>
        simp only [hs, Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_sub_cancel] at hu
        obtain ⟨hr', hword, _⟩ := hu
        obtain ⟨_, _, hready⟩ := hr'.ready
        have hrel' := hrel.retry hc hs
        by_cases hz : fuel = 0
        · subst fuel
          obtain ⟨_, hstatus, hused⟩ := hrel'.exhausted
          refine ⟨hready.scr, hready.sp, Or.inl ⟨by rw [hword]; decide,
            ⟨0, by rw [hused]; exact hr'⟩, by rw [hword, hstatus]; rfl, ?_⟩⟩
          intro he
          omega
        · have hn : fuel + 1 ≠ 1 := by omega_using [hz]
          refine ⟨hready.scr, hready.sp, Or.inr ⟨by rw [hword, ite_eq_right hn], fuel,
            by omega_using [], by omega_using [hz], by omega_using [hbound], used + (randomSignDraw (randomInput s) used).used, hr', hrel'⟩⟩

theorem random_sign_loop_correct (S : Signer) {s t : State} {h : RandomSignABI S.stack s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {used fuel : Nat}
    (hr : RandomSignRunning h hq used fuel t) (hpos : 0 < fuel) (hbound : fuel ≤ 8) (hval : RandomValid S s) :
    WP isa (.loop (.seq (RandomSign.attempt S.name S.code)
      (.block (Random.statusTest 4))) (.zero .x .x4)) t
      (RandomSignLoopPost h hq used (randomSignRemaining (randomInput s) used fuel)) := by
  apply random_statusLoop_rule _ (randomBase s) (RandomSignLoopInv h hq used (randomSignRemaining (randomInput s) used fuel))
  · intro n a b ⟨hp, hb, k, hk, hrel⟩ hm hkeep
    exact ⟨hp, hb, k, hk.congr hm hkeep, hrel⟩
  · intro a b ⟨⟨n, hn⟩, hs, hout⟩ hm hkeep
    exact ⟨⟨n, hn.congr hm hkeep⟩, by rw [hm]; exact hs, fun h => by rw [hm]; exact hout h⟩
  · intro n a ha
    exact attempt_progress S ha hval
  · exact ⟨hpos, hbound, used, hr, RandomSignResultRel.refl _ _ _⟩

end VG.Proof.Dsa.AArch64
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

structure RandomSignFinishPre (s : State) (used : Nat) (t : State) : Prop where
  scr : Scr t (randomBase s) Random.frameBytes
  sp : t.sp = randomBase s
  saved : RandomSaved s t.mem
  usedWord : word t.mem (randomBase s) Random.oUsed = BitVec.ofNat 64 used
  rd : t.rd = s.rd
  wr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr
  callee : ∀ r ∈ preserved, t.gpr r = s.gpr r
  vectors : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

structure RandomSignBodyPost (s : State) (result : Spec.Dsa.RandomSignResult) (t : State) : Prop where
  sp : t.sp = randomBase s
  rd : t.rd = s.rd
  wr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr
  status : t.gpr .x0 = BitVec.ofNat 64 result.status
  output : Spec.Rsa.bytesAt t.mem (s.gpr .x0) (s.gpr .x1).toNat =
    result.signature.getD (List.replicate (s.gpr .x1).toNat 0)
  used : t.mem.readW (s.gpr .x2) 64 = BitVec.ofNat 64 result.used
  callee : ∀ r ∈ preserved, t.gpr r = s.gpr r
  vectors : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  nonce : ∀ i < 32, t.mem (off (randomBase s) (200 + i)) = 0

private theorem bytes_zero {m : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m (p + BitVec.ofNat 64 i) = 0) :
    Spec.Rsa.bytesAt m p n = List.replicate n 0 := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro i hi _
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
  exact h i (by simpa only [bytesAt_length] using hi)

theorem random_finish_ready_result {extra : Nat} {s t : State} (h : RandomSignABI extra s)
    {result : Spec.Dsa.RandomSignResult} (hr : RandomSignFinishPre s result.used t)
    (hstatus : word t.mem (randomBase s) Random.oStatus = BitVec.ofNat 64 result.status)
    (houtput : result.status = 1 → Spec.Rsa.bytesAt t.mem (s.gpr .x0) (s.gpr .x1).toNat =
      result.signature.getD (List.replicate (s.gpr .x1).toNat 0))
    (hbound : result.status ≤ 2) (hsig : result.status ≠ 1 → result.signature = none) :
    WP isa RandomSign.finish t (RandomSignBodyPost s result) := by
  have houtlen : 0 < (s.gpr .x1).toNat := by
    have hl := h.lengths
    have ho := h.outLength
    unfold Spec.Dsa.lengthsValid at hl
    omega_using [hl, ho]
  have hptr : word t.mem (randomBase s) Random.oUsedPtr = s.gpr .x2 :=
    hr.saved (56, s.gpr .x2) (by simp [randomSavedValues])
  have hframeOut := h.stackOut.sub_left (random_frame_sub h)
  have hframeUsed := h.stackUsed.sub_left (random_frame_sub h)
  have hsep (d : Nat) (hd : d + 8 ≤ Random.frameBytes) :
      Mem.Sep (off (randomBase s) d) 8 (s.gpr .x0) (s.gpr .x1).toNat :=
    (hframeOut.sub_left (Offset.sub_base _ hd)).sep (Region.contains_self _ _) (Region.contains_self _ _)
  have hused : InRegions t.wr (word t.mem (randomBase s) Random.oUsedPtr) 8 := by
    rw [hptr]
    exact ⟨⟨s.gpr .x2, 8⟩, by rw [hr.wr, h.wr]; simp, Region.contains_self _ _⟩
  have hsepUsed : Mem.Sep (off (randomBase s) Random.oStatus) 8 (word t.mem (randomBase s) Random.oUsedPtr) 8 := by
    rw [hptr]
    exact (hframeUsed.sub_left (Offset.sub_base _ (by decide))).sep (Region.contains_self _ _) (Region.contains_self _ _)
  refine WP.mono (random_finish_ok (B := randomBase s) (op := s.gpr .x0) (k := (s.gpr .x1).toNat) hr.scr hr.sp
    (hr.saved (40, s.gpr .x0) (by simp [randomSavedValues]))
    (by simpa only [Random.oOutLen, ofNat_toNat64] using hr.saved (48, s.gpr .x1) (by simp [randomSavedValues]))
    houtlen (s.gpr .x1).isLt
    (fun j hj => ⟨⟨s.gpr .x0, (s.gpr .x1).toNat⟩, by rw [hr.wr, h.wr]; simp,
      contains_byte _ hj (Nat.le_of_lt (s.gpr .x1).isLt)⟩)
    hsep hused hsepUsed)
    fun u ⟨hret, ⟨m, hgood, hbad, hwords, hum⟩, hk⟩ => ?_
  have hpM : word m (randomBase s) Random.oUsedPtr = s.gpr .x2 := (hwords _ (by decide)).trans hptr
  have huM : word m (randomBase s) Random.oUsed = BitVec.ofNat 64 result.used := by
    rw [hwords _ (by decide)]
    exact hr.usedWord
  have hkv : Keep randomVolatile t u := hk.mono (by decide)
  refine ⟨hk.sp.trans hr.sp, hk.rd.trans hr.rd, hk.wr.trans hr.wr,
    hret.trans hstatus, ?_, ?_,
    fun r hc => (hkv.gpr r (random_saved_not_volatile hc)).trans (hr.callee r hc),
    fun r hc => (hk.vcs r hc).trans (hr.vectors r hc), ?_⟩
  · rw [hum, random_publish_output hframeOut.symm (by
      rw [hpM]; exact h.outUsed.sep (Region.contains_self _ _) (Region.contains_self _ _)) (s.gpr .x1).isLt]
    by_cases hs : result.status = 1
    · have hw : word t.mem (randomBase s) Random.oStatus = 1 := by rw [hstatus, hs]; rfl
      rw [hgood hw]
      exact houtput hs
    · have hw : word t.mem (randomBase s) Random.oStatus ≠ 1 := by
        intro he
        rw [hstatus] at he
        have hn := congrArg BitVec.toNat he
        change result.status % 2 ^ 64 = 1 at hn
        omega_using [hbound, hs, hn]
      rw [hsig hs]
      exact bytes_zero (hbad hw)
  · rw [hum, ← hpM, random_publish_used, huM]
  · intro i hi
    rw [hum]
    apply random_publish_nonce_zero _ i hi
    rw [hpM]
    exact (hframeUsed.sub_left (Offset.sub_base _ (by decide))).sep (Region.contains_self _ _) (Region.contains_self _ _)

theorem random_finish_result {extra : Nat} {s t : State} {h : RandomSignABI extra s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {result : Spec.Dsa.RandomSignResult}
    (hp : RandomSignLoopPost h hq 0 result t) (hbound : result.status ≤ 2)
    (hsig : result.status ≠ 1 → result.signature = none) :
    WP isa RandomSign.finish t (RandomSignBodyPost s result) := by
  obtain ⟨⟨fuel, hr⟩, hstatus, houtput⟩ := hp
  obtain ⟨cm, draws, hready⟩ := hr.ready
  exact random_finish_ready_result h
    ⟨hready.scr, hready.sp, hr.saved, (by simpa only [randomContextOf, Nat.zero_add] using hready.usedWord), hr.rd, hr.wr, hr.callee, hr.vectors⟩
    hstatus houtput hbound hsig

end VG.Proof.Dsa.AArch64

end

end

/-! Invalid moduli exit before sampling and publish zero consumption. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_sign_init_invalid {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (hq : ¬ 1 < Spec.Dsa.decodeBE (randomQBytes s)) :
    WP isa (.seq (.block RandomSign.entry) Random.prepare) (allocated Random.frameBytes s) fun t =>
      t.gpr .x0 = 0 ∧ RandomSignFinishPre s 0 t := by
  refine WP.mono (WP.keep randomVolatile (Q := fun t =>
      t.gpr .x0 = 0 ∧ Scr t (randomBase s) Random.frameBytes ∧ t.sp = randomBase s ∧
      RandomSaved s t.mem ∧ word t.mem (randomBase s) Random.oUsed = 0) ?_ rfl rfl rfl)
    fun t ⟨⟨ha, hscr, hsp, hsaved, hu⟩, hk⟩ => ?_
  · have hsp : (allocated Random.frameBytes s).sp = randomBase s := rfl
    refine WP.seq (WP.mono (random_entry_ok (random_alloc_scr h) hsp (random_incoming_read h))
      fun u ⟨hum, hku⟩ => ?_)
    have hus := (random_alloc_scr h).congr hku.wr
    have husp := hku.sp.trans hsp
    have hsaved : RandomSaved s u.mem := by rw [hum]; exact random_saved_entry s
    have hf : InScr (randomBase s) Random.frameBytes (allocated Random.frameBytes s).mem u.mem := by
      rw [hum]; exact InScr.of_outside (random_entry_outside _ _) (by decide)
    have hv (p : Nat × BitVec 64) (hp : p ∈ randomEntryValues (allocated Random.frameBytes s) (randomBase s)) :
        word u.mem (randomBase s) p.1 = p.2 := by
      rw [hum]; exact random_entry_values _ _ p hp
    have hqu : word u.mem (randomBase s) Random.oQ = s.gpr .x3 + s.gpr .x5 :=
      hv (168, s.gpr .x3 + s.gpr .x5) (by simp [randomEntryValues, allocated])
    have huu : word u.mem (randomBase s) Random.oUsed = 0 :=
      hv (144, 0) (by simp [randomEntryValues])
    have hql : word u.mem (randomBase s) Random.oQLen = BitVec.ofNat 64 (randomQBytes s).length := by
      simpa only [Random.oQLen, random_q_length h, ofNat_toNat64] using
        hsaved (88, s.gpr .x6) (by simp [randomSavedValues])
    have hlen : 0 < (randomQBytes s).length := by
      rw [random_q_length h]
      have hl := h.lengths
      unfold Spec.Dsa.lengthsValid at hl
      omega_using [hl]
    refine WP.mono (random_prepare_valid hus husp hqu hql ((random_initial_q h).congrK hf hku)
      hlen (by rw [random_q_length h]; exact (s.gpr .x6).isLt)) fun t ⟨ha, hm, hk⟩ => ?_
    have hw (d : Nat) (hd : d + 8 ≤ 168) : word t.mem (randomBase s) d = word u.mem (randomBase s) d := by
      rw [hm]
      exact (random_prepare_outside _ _ _ _).word (by omega_using [hd]) (by omega_using [hd])
    exact ⟨by rw [ite_eq_right hq] at ha; exact ha, hus.congr hk.wr,
      hk.sp.trans husp, hsaved.congr (fun d _ hd => hw d (by omega_using [hd])),
      (hw 144 (by decide)).trans huu⟩
  · refine ⟨ha, hscr, hsp, hsaved, hu, hk.rd, hk.wr, ?_, ?_⟩
    · intro r hr
      exact hk.gpr r (random_saved_not_volatile hr)
    · intro r hr
      exact hk.vcs r hr

theorem random_invalid_remaining {s : State}
    (hq : ¬ 1 < Spec.Dsa.decodeBE (randomQBytes s)) :
    randomSignRemaining (randomInput s) 0 8 = ⟨none, 0, 0, [4]⟩ := by
  have hle : (Spec.Dsa.privateKeyBytes (randomInput s).pLen (randomInput s).qLen
      (randomInput s).key).params.q ≤ 1 := by rw [← random_q_decode]; omega_using [hq]
  have hd : Spec.Dsa.Random.sample (Spec.Dsa.privateKeyBytes (randomInput s).pLen (randomInput s).qLen
      (randomInput s).key).params.q 128 (randomInput s).rand = ⟨none, 0, [4]⟩ := by
    rw [Spec.Dsa.Random.sample]
    simp only [hle, ite_true]
  unfold randomSignRemaining
  rw [List.drop_zero, randomSignLoop_sample_none _ _ 7 _ _ _ (by rw [hd]), hd]
  rfl

theorem random_sign_invalid_store {s t : State} (hr : RandomSignFinishPre s 0 t)
    (ha : t.gpr .x0 = 0) :
    WP isa (.block (Random.store Random.oStatus .x0)) t fun w =>
      RandomSignFinishPre s 0 w ∧ word w.mem (randomBase s) Random.oStatus = 0 := by
  refine WP.mono (WP.keep [.x15] (Q := fun w =>
      w.mem = t.mem.writeW (off (randomBase s) Random.oStatus) (0 : BitVec 64))
      (by brun [Random.store, hr.sp, hr.scr.st (d := Random.oStatus) (by decide), ha,
        exec_addSp, off]) rfl rfl rfl) fun w ⟨hwm, hk⟩ => ?_
  have hw (d : Nat) (hd : d + 8 ≤ 192) : word w.mem (randomBase s) d = word t.mem (randomBase s) d := by
    rw [hwm, (writeW_outside _ (randomBase s) _ (by decide)).word (by simp only [Random.oStatus]; omega_using [hd]) (by omega_using [hd])]
  refine ⟨⟨hr.scr.congr hk.wr, hk.sp.trans hr.sp,
    hr.saved.congr (fun d _ hd => hw d (by omega_using [hd])), (hw 144 (by decide)).trans hr.usedWord,
    hk.rd.trans hr.rd, hk.wr.trans hr.wr, ?_, ?_⟩, ?_⟩
  · intro r hc
    have hkv := hk.mono (show [.x15] ⊆ randomVolatile by decide)
    exact (hkv.gpr r (random_saved_not_volatile hc)).trans (hr.callee r hc)
  · intro r hc
    exact (hk.vcs r hc).trans (hr.vectors r hc)
  · rw [hwm, word_writeW_self]

theorem random_sign_body_invalid (S : Signer) {s : State} (h : RandomSignABI S.stack s)
    (hq : ¬ 1 < Spec.Dsa.decodeBE (randomQBytes s)) :
    WP isa (RandomSign.body S.name S.code)
      (allocated Random.frameBytes s)
      (RandomSignBodyPost s (randomSignRemaining (randomInput s) 0 8)) := by
  rw [random_invalid_remaining hq]
  unfold RandomSign.body
  apply WP.assoc
  refine WP.seq (WP.mono (random_sign_init_invalid h hq) fun t ⟨ha, hr⟩ => ?_)
  refine WP.seq (WP.ite true (by simp [eval, State.read, ha]) (fun _ => ?_) (fun he => Bool.noConfusion he))
  refine WP.mono (random_sign_invalid_store hr ha) fun w ⟨hwr, hstatus⟩ => ?_
  exact random_finish_ready_result h hwr hstatus (fun he => by contradiction) (by decide) (fun _ => rfl)

end VG.Proof.Dsa.AArch64

end

end

/-! Whole-entry execution, frame restoration, and stack bounds. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/RandomSignBody.lean`, which only this module imported.
section

/-! Compose initialization, bounded retries, and publication for admissible q. -/
section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_remaining_failure (p : VG.Proof.Dsa.RandomSignInput) (used fuel : Nat)
    (hs : (randomSignRemaining p used fuel).status ≠ 1) :
    (randomSignRemaining p used fuel).signature = none := by
  have he := randomSignLoop_success p.pLen p.qLen p.key p.digest fuel (p.rand.drop used)
  cases hc : (randomSignRemaining p used fuel).signature with
  | none => rfl
  | some sig =>
    exact False.elim (hs (he.mpr (by change (randomSignRemaining p used fuel).signature.isSome = true; rw [hc]; rfl)))

theorem random_sign_body_valid (S : Signer) {s : State} (h : RandomSignABI S.stack s)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)) (hval : RandomValid S s) :
    WP isa (RandomSign.body S.name S.code)
      (allocated Random.frameBytes s)
      (RandomSignBodyPost s (randomSignRemaining (randomInput s) 0 8)) := by
  unfold RandomSign.body
  apply WP.assoc
  refine WP.seq (WP.mono (random_sign_init_running h hq) fun t ⟨ha, hr⟩ => ?_)
  refine WP.seq (WP.ite false (by simp [eval, State.read, ha])
    (fun he => Bool.noConfusion he) (fun _ => ?_))
  refine WP.mono (random_sign_loop_correct S hr (by decide) (by decide) hval) fun w hw => ?_
  exact random_finish_result hw (randomSignLoop_status_le _ _ _ _ _ _) (random_remaining_failure _ _ _)

end VG.Proof.Dsa.AArch64
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_sign_sp (S : Signer) :
    (RandomSign.code S.name S.code).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_forall (fun _ => rfl) _

theorem random_sign_depth (S : Signer) :
    16 * (RandomSign.code S.name S.code).aarch64Depth ≤ S.stack + 256 := by
  simp only [RandomSign.code, RandomSign.body, RandomSign.attempt, Code.aarch64Depth,
    show Random.prepare.aarch64Depth = 0 from rfl,
    show Random.sample.aarch64Depth = 0 from rfl,
    show RandomSign.callFinish.aarch64Depth = 0 from rfl,
    show RandomSign.finish.aarch64Depth = 0 from rfl,
    Nat.zero_max, Nat.max_zero]
  change 16 * (S.code.aarch64Depth + 16) ≤ _
  simpa only [Nat.mul_add, show 16 * 16 = 256 from rfl] using Nat.add_le_add_right S.depth 256

theorem random_sign_body (S : Signer) {s : State} (h : RandomSignABI S.stack s) (hval : RandomValid S s) :
    WP isa (RandomSign.body S.name S.code)
      (allocated Random.frameBytes s)
      (RandomSignBodyPost s (randomSignRemaining (randomInput s) 0 8)) := by
  by_cases hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)
  · exact random_sign_body_valid S h hq hval
  · exact random_sign_body_invalid S h hq

theorem random_remaining_bytes {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    randomSignRemaining (randomInput s) 0 8 =
      Spec.Dsa.randomSignBytes (randomInput s).pLen (randomInput s).qLen (randomInput s).key
        (randomInput s).digest (randomInput s).rand := by
  simp only [Spec.Dsa.randomSignBytes, randomInput, bytesAt_length, h.lengths, h.keyLength,
    bne_self_eq_false, decide_true, Bool.not_true, Bool.false_or, Bool.false_eq_true, ite_false,
    randomSignRemaining, List.drop_zero]

structure RandomSignCodePost (s : State) (result : Spec.Dsa.RandomSignResult) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  status : t.gpr .x0 = BitVec.ofNat 64 result.status
  output : Spec.Rsa.bytesAt t.mem (s.gpr .x0) (s.gpr .x1).toNat =
    result.signature.getD (List.replicate (s.gpr .x1).toNat 0)
  used : t.mem.readW (s.gpr .x2) 64 = BitVec.ofNat 64 result.used
  callee : ∀ r ∈ preserved, t.gpr r = s.gpr r
  sp : t.sp = s.sp
  vectors : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem random_sign_code (S : Signer) {s : State} (h : RandomSignABI S.stack s) (hval : RandomValid S s) :
    WP isa (RandomSign.code S.name S.code) s
      (RandomSignCodePost s (randomSignRemaining (randomInput s) 0 8)) := by
  apply random_frame_ok h
  refine WP.mono (random_sign_body S h hval) fun t ht m u f => ?_
  -- The frame's bytes are lost; the outputs are apart from them.
  have hsub := random_frame_sub h
  refine ⟨ht.rd, by change t.wr.tail = _; rw [ht.wr]; rfl, ht.status,
    (List.map_congr_left fun i hi => lost_byte f (h.stackOut.symm.sub_right hsub) (List.mem_range.mp hi)).trans
      ht.output,
    (f.readW (r := ⟨s.gpr .x2, 8⟩) (Region.contains_self _ _)
      (fun R hR => by obtain rfl := List.mem_singleton.mp hR; exact h.stackUsed.symm.sub_right hsub)
      (by decide)).trans ht.used,
    ht.callee, ?_, ht.vectors⟩
  change t.sp + BitVec.ofNat 64 Random.frameBytes = s.sp
  rw [ht.sp, randomBase, BitVec.sub_add_cancel]

end VG.Proof.Dsa.AArch64
