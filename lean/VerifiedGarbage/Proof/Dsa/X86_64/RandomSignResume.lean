module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignRunning
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallMemory
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignRetry
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomRestore
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallLayout
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.RandomMemory
import VerifiedGarbage.Proof.Bignum.Octets

/-! Restore the complete signing-loop invariant after a supplied-nonce call. -/
@[expose] public section
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
