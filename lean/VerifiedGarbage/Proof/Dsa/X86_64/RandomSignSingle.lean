module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignRunning
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCall

import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignArgsSaved
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallValue
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedExp
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallMemory
import VerifiedGarbage.Proof.Dsa.X86_64.RandomMemory
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.X86_64.RandomState
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignRetry
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallLayout
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallResult
/-! One complete supplied-nonce signing step, including arguments and retry state. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/RandomRestore.lean`, which only this module imported.
section

/-! Resume sampling after a signer call that preserves its inputs and private state. -/
section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

def randomReadySlots : List Nat := [112, 120, 144, 176, 88, 184, 168, 160]

/-- Each sampling invocation tracks its own exact memory effects. The outer
signing loop separately tracks output and arithmetic-scratch writes. -/
theorem RandomReady.restore {C : RandomContext} {used draws : Nat} {s t : State}
    (h : RandomReady C used draws s) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hsp : t.gpr .rsp = s.gpr .rsp)
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

end VG.Proof.Dsa.X86_64
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/RandomSignResume.lean`, which only this module imported.
section

/-! Restore the complete signing-loop invariant after a supplied-nonce call. -/
section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem RandomSignRunning.after_signer {extra : Nat} {s t a u : State} {m : Mem}
    {h : RandomSignABI extra s} {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {used fuel : Nat}
    (hr : RandomSignRunning h hq used fuel t) (success : Bool)
    (hargs : Outside (randomBase s) 0 40 t.mem a.mem) (hka : Keep randomVolatile t a)
    (hf : Frame (randomCallWr s ++ [below (randomBase s) (extra + 8)]) a.mem m)
    (hm : u.mem = randomRetryMem m (randomBase s) success fuel)
    (hrd : u.rd = a.rd) (hwr : u.wr = a.wr)
    (hcs : ∀ r ∈ calleeSaved, u.gpr r = a.gpr r)
    (hmx : u.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10) :
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
    (by simp only [randomInput, bytesAt_length]; exact Nat.le_of_lt (s.gpr .r8).isLt)
  have hdigestU := random_call_source hdigestA hf hpostF hrd hwr
    (by simpa only [randomInput, bytesAt_length] using h.outDigest.symm)
    (by simpa only [randomInput, bytesAt_length] using h.digestScratch)
    (by simpa only [randomInput, bytesAt_length] using h.stackDigest)
    (by simp only [randomInput, bytesAt_length]; exact Nat.le_of_lt (stackArg s 2).isLt)
  have hrandU := random_call_source hrandA hf hpostF hrd hwr
    (by simpa only [randomContextOf, randomInput, bytesAt_length] using h.outRand.symm)
    (by simpa only [randomContextOf, randomInput, bytesAt_length] using h.randScratch)
    (by simpa only [randomContextOf, randomInput, bytesAt_length] using h.stackRand)
    (by simp only [randomContextOf, randomInput, bytesAt_length]; exact Nat.le_of_lt (stackArg s 4).isLt)
  have hqU : Src u (randomBase s) Random.frameBytes (s.gpr .rcx + s.gpr .r9) (randomQBytes s) := by
    have hx := random_src_take (random_src_drop hkeyU (randomInput s).pLen) (randomInput s).qLen
    simpa only [randomQBytes, randomInput, ofNat_toNat64] using hx
  have hword (d : Nat) (hd : 40 ≤ d) (hb : d + 8 ≤ Random.frameBytes)
      (ha : d + 8 ≤ 152 ∨ 160 ≤ d) (hz : d + 8 ≤ 192 ∨ 200 ≤ d) :
      word u.mem (randomBase s) d = word t.mem (randomBase s) d := by
    rw [hm, random_retry_word _ _ _ _ d (by unfold Random.frameBytes at hb; omega) ha hz,
      random_frame_words (random_call_frameBytes h hf) hb, hargs.word (Or.inr hd) (by unfold Random.frameBytes at hb; omega)]
  have hkeepSp : u.gpr .rsp = t.gpr .rsp :=
    (hcs .rsp (by simp [calleeSaved])).trans (hka.gpr (by decide))
  have hnew := hready.restore (hrd.trans hka.2.1) (hwr.trans hka.2.2) hkeepSp
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
    (Or.inl (by omega)) (Or.inl (by omega))), ?_, (hrd.trans hka.2.1).trans hr.rd,
    (hwr.trans hka.2.2).trans hr.wr, hkeyU, hdigestU,
    fun r hc hn => ((hcs r hc).trans (hka.gpr (random_saved_not_volatile hc))).trans (hr.callee r hc hn),
    hmx.trans hr.mxcsr⟩
  rw [hm, random_retry_attempts, random_frame_words (random_call_frameBytes h hf) (by decide),
    hargs.word (by decide) (by decide), hr.attempts]
  cases success <;> rfl

end VG.Proof.Dsa.X86_64
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/RandomSignCallRetry.lean`, which only this module imported.
section

/-! Compose supplied-nonce signing with the bounded-retry update. -/
section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem random_signer_retry (v : Backend) {s t : State} {attempts : Nat} (h : RandomSignABI v.stack s)
    (hsp : t.gpr .rsp = randomBase s)
    (hw : ∀ i < 5, word t.mem (randomBase s) (8 * i) = randomCallArg s i)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rsi)
    (hdx : t.gpr .rdx = s.gpr .rcx) (hcx : t.gpr .rcx = s.gpr .r8)
    (h8 : t.gpr .r8 = s.gpr .r9) (h9 : t.gpr .r9 = off (randomBase s) Random.oNonce)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr)
    (hn : word t.mem (randomBase s) Random.oAttempts = BitVec.ofNat 64 attempts)
    (hpos : 0 < attempts) (hbound : attempts < 2 ^ 64) :
    WP isa (.seq (.call (randomSignerName v) (SignVerify.sign v.sq v.mul)) RandomSign.callFinish) t fun u =>
      u.rd = t.rd ∧ u.wr = t.wr ∧ (∀ r ∈ calleeSaved, u.gpr r = t.gpr r) ∧
      (∃ m : Mem,
        Frame (randomCallWr s ++ [below (randomBase s) (v.stack + 8)]) t.mem m ∧
        Spec.Rsa.bytesAt m (s.gpr .rdi) (s.gpr .rsi).toNat =
          (randomCallResult s t).getD (List.replicate (s.gpr .rsi).toNat 0) ∧
        u.mem = randomRetryMem m (randomBase s) (randomCallResult s t).isSome attempts) ∧
      u.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  refine WP.seq (WP.mono (random_signer_outcome v h hsp hw hdi hsi hdx hcx h8 h9 hrd hwr)
    fun u ⟨hur, huw, huc, hf, hstatus, hout, hmx⟩ => ?_)
  have hus : Scr u (randomBase s) Random.frameBytes :=
    (random_alloc_scr h).congr (huw.trans hwr)
  have husp : u.gpr .rsp = randomBase s := (huc .rsp (by simp [calleeSaved])).trans hsp
  have hun : word u.mem (randomBase s) Random.oAttempts = BitVec.ofNat 64 attempts :=
    (random_frame_words (random_call_frameBytes h hf) (by decide)).trans hn
  have hra : (u.gpr .rax).setWidth 32 = if (randomCallResult s t).isSome then 1 else 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [hstatus]
    cases randomCallResult s t <;> rfl
  refine WP.mono_mx (by decide) (random_callFinish_ok (randomCallResult s t).isSome hus husp hra hun hpos hbound)
    fun w ⟨hwm, hkw⟩ hmxw => ?_
  exact ⟨hkw.2.1.trans hur, hkw.2.2.trans huw, fun r hr =>
    (hkw.gpr (by simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)).trans (huc r hr),
    ⟨u.mem, hf, hout, hwm⟩, by rw [hmxw]; exact hmx⟩

end VG.Proof.Dsa.X86_64
end

end

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
