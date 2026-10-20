module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopState
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusHeader
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusWords
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Start the blinded witness loop without consuming a draw. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64

theorem primeLoopInit_ok {P : PrimeParams} {used : Nat} {s : State}
    (h : PrimeState P used s) (hu : used ≤ P.rand.length) :
    WP isa (.block Impl.Dsa.AArch64.Generation.primeLoopInit) s
      (PrimeLoopState P s (primeRest P 1 0 used) 1 0 used) := by
  have h256 := h.ready.ws.h256
  refine WP.mono (WP.keep [.x3] (Q := fun t =>
    t.mem = (s.mem.writeW (off P.B (8 * kI)) (BitVec.ofNat 64 1)).writeW
      (off P.B (8 * kUni)) (BitVec.ofNat 64 0)) (by
      unfold Impl.Dsa.AArch64.Generation.primeLoopInit
      brun [h.ready.ws.x0, hdr_enc (show kI < 32 by decide), hdr_enc (show kUni < 32 by decide),
        h.ready.ws.scr.st (d := 8 * kI) (by simp only [kI, kElen, sFn]; omega),
        h.ready.ws.scr.st (d := 8 * kUni) (by simp only [kUni, kP, sFn]; omega)]
      rfl) rfl rfl rfl) fun t ⟨hm, hk⟩ => ?_
  have hf : Frm P.B [(8 * kI, 8), (8 * kUni, 8)] s.mem t.mem := by
    rw [hm]
    exact (Frm.of_outside (writeW_outside _ P.B _ (d := 8 * kI) (by decide)) (by simp)).trans
      (Frm.of_outside (writeW_outside _ P.B _ (d := 8 * kUni) (by decide)) (by simp))
  have k : Keep mmRegs s t := hk.mono (by decide)
  have hready := (h.ready.write_header (BitVec.ofNat 64 1) P.exponentRoom (i := kI) (by decide)).write_header
    (BitVec.ofNat 64 0) P.exponentRoom (i := kUni) (by decide)
  have ht : ModulusReady t P.B P.Z P.w P.N := hready.of_words P.exponentRoom
    (fun _ _ => by change word t.mem _ _ = _; rw [hm]) hk.wr ((hk.gpr .x0 (by decide)).trans h.ready.ws.x0)
  have hus : word t.mem P.B (8 * kUsed) = BitVec.ofNat 64 used :=
    (hf.word_eq (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> decide)
      (by decide)).trans h.used
  have hpt := h.advance ht hus hf.work k
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> (have := P.z256; simp only [kI, kElen, kUni, kP, sFn]; omega))
    (by
      intro j hj r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj hr
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hr with rfl | rfl <;> decide)
  refine ⟨hpt, ?_, ?_, hu, by decide, by simp, by decide, Or.inl (by decide), rfl,
    hf.work.mono (by simp [drawRoundRanges, sampleRoundRanges]), k⟩
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [hm, word_writeW_self]

end VG.Proof.Dsa.AArch64.Generation
