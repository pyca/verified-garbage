module

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignRunning
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCall
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallMemory
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignRetry
import VerifiedGarbage.Proof.Dsa.AArch64.CallFinishCT
import VerifiedGarbage.Proof.Dsa.AArch64.RandomMemory
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.AArch64.RandomState
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignEnv
public import VerifiedGarbage.Impl.Dsa.AArch64.RandomSign
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSample

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
