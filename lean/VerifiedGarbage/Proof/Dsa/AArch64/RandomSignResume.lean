module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignRunning
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallMemory
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignRetry
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomRestore
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallLayout
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.RandomMemory
import VerifiedGarbage.Proof.Bignum.Octets

/-! Restore the complete signing-loop invariant after a supplied-nonce call. -/
@[expose] public section
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
