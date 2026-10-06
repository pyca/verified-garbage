import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCode
import VerifiedGarbage.Proof.Rsa.X86_64.PubChecked

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Proof.MlKem.X86_64

theorem sat_eq_65537 (e : Nat) : sat e = 65537 ↔ e = 65537 := by
  unfold sat
  split <;> omega

theorem dispatchTest_ok (s : State) {e : Nat} (he : s.gpr .r11 = BitVec.ofNat 64 (sat e)) :
    WP isa (.block [.alu .cmp .r11 (.imm 65537)]) s fun t =>
      t.zf = some (decide (e = 65537)) ∧ t.mem = s.mem ∧ Keep [.r11] s t := by
  have bound : sat e < 2^64 := by have := sat_lt e; omega
  refine WP.mono (WP.keep [.r11] (Q := fun t =>
    t.zf = some (decide (e = 65537)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨hz,hm⟩,hk⟩ => ⟨hz,hm,hk⟩
  xrun [he,show BitVec.signExtend 64 (65537 : BitVec 32) = BitVec.ofNat 64 65537 from rfl,ofNat_sub_beq bound (show 65537 < 2^64 by decide)]
  exact decide_eq_decide.mpr (sat_eq_65537 e)

theorem dispatch_correct (M : Mont)
    (hmx : (Folded.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (hmxOld : (Precomputed.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : pdContract.pre s)
    (he : s.gpr .r11 = BitVec.ofNat 64 (sat (Spec.Rsa.os2ip (eBytes s)))) :
    ∃ tr t, Exec isa (Folded.dispatch M.mm) s tr t ∧ abiPreserved s t ∧ pdContract.post s t := by
  unfold Folded.dispatch
  refine WP.seq (WP.mono_mx (by decide +kernel) (dispatchTest_ok s he)
    fun a ⟨za,ma,ka⟩ mxa => ?_)
  have same : Same s a := Same.of_keep (ka.mono (by simp)) ma
  have preA : pdContract.pre a := (pdPre_same same).symm ▸ h
  have finish : ∀ t, abiPreserved a t ∧ pdContract.post a t →
      abiPreserved s t ∧ pdContract.post s t := by
    intro t ⟨abi,post⟩
    refine ⟨⟨fun r hr => (abi.1 r hr).trans (ka.gpr (by
      simp only [calleeSaved,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)),?_,?_⟩,?_⟩
    · rw [← same.rsp,← same.mem]; exact abi.2.1
    · rw [abi.2.2,mxa]
    · simpa only [pdContract,stackArg_same same,same.rdi,same.rsi,same.rdx,same.rcx,
        same.r8,same.r9,same.mem] using post
  refine WP.ite (decide (Spec.Rsa.os2ip (eBytes s) = 65537))
    (by simp only [eval,za]) (fun hz => ?_) (fun _ => ?_)
  · have e : Spec.Rsa.os2ip (Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat) = 65537 := by
      rw [same.mem,same.r8,same.r9]
      exact of_decide_eq_true hz
    exact WP.mono (code_correct M hmx a preA e) finish
  · exact WP.mono (pdCode_correct M hmxOld a preA) finish

end VG.Proof.Bignum.X86_64.FoldedPublic
