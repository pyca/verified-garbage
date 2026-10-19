module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallResult
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallMemory
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignRetry
import VerifiedGarbage.Proof.Framework.Omega

/-! Compose supplied-nonce signing with the bounded-retry update. -/
@[expose] public section
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
