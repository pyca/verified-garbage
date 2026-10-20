module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallResult
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallMemory
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignRetry
import VerifiedGarbage.Proof.Framework.Omega

/-! Compose supplied-nonce signing with link restoration and bounded retry. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_signer_retry (v : Backend) {s t : State} {attempts : Nat} (h : RandomSignABI v.stack s)
    (hsp : t.sp = randomBase s)
    (hw : ∀ i < 3, word t.mem (randomBase s) (8 * i) = randomCallArg s i)
    (h0 : t.gpr .x0 = s.gpr .x0) (h1 : t.gpr .x1 = s.gpr .x1)
    (h2 : t.gpr .x2 = s.gpr .x3) (h3 : t.gpr .x3 = s.gpr .x4)
    (h4 : t.gpr .x4 = s.gpr .x5) (h5 : t.gpr .x5 = off (randomBase s) Random.oNonce)
    (h6 : t.gpr .x6 = s.gpr .x6) (h7 : t.gpr .x7 = s.gpr .x7)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr)
    (hn : word t.mem (randomBase s) Random.oAttempts = BitVec.ofNat 64 attempts)
    (hlink : word t.mem (randomBase s) RandomSign.oLink = t.gpr .x30)
    (hpos : 0 < attempts) (hbound : attempts < 2 ^ 64) :
    WP isa (.seq (.call (randomSignerName v) (SignVerify.sign v.mul)) RandomSign.callFinish) t fun u =>
      u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧ (∀ r ∈ preserved, u.gpr r = t.gpr r) ∧
      (∃ m : Mem,
        Frame (randomCallWr s ++ [below (randomBase s) v.stack]) t.mem m ∧
        Spec.Rsa.bytesAt m (s.gpr .x0) (s.gpr .x1).toNat =
          (randomCallResult s t).getD (List.replicate (s.gpr .x1).toNat 0) ∧
        u.mem = randomRetryMem m (randomBase s) (randomCallResult s t).isSome attempts) ∧
      (∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64) := by
  refine WP.seq (WP.mono (random_signer_outcome v h hsp hw h0 h1 h2 h3 h4 h5 h6 h7 hrd hwr)
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
  · exact (hkw.gpr r (by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all)).trans (huc r hr hl)

end VG.Proof.Dsa.AArch64
