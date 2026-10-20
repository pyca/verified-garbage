module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopState
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Framework.Omega

/-! # Start DSA's blinded witness loop without consuming a draw -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem primeLoopInit_ok {P : PrimeParams} {mi : BitVec 64} {used : Nat} {s : State}
    (h : PrimeState P mi used s) (hu : used ≤ P.rand.length) :
    WP isa (.block Impl.Dsa.X86_64.Generation.primeLoopInit) s
      (PrimeLoopState P mi s (primeRest P 1 0 used) 1 0 used) := by
  have hs : ∀ i < 32, InRegions s.wr (off P.B (8 * i)) 8 := fun i hi =>
    h.ready.good.scr.st (by have := hdr_lt_slot P.w 8 hi; have := P.dims.z; omega)
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.mem = (s.mem.writeW (off P.B (8 * kI)) (BitVec.ofNat 64 1)).writeW
      (off P.B (8 * kUni)) (BitVec.ofNat 64 0)) (by
    xrun [Impl.Dsa.X86_64.Generation.primeLoopInit, State.ea, hdr, hdrOff, h.ready.good.rdi,
      hs kI (by decide), hs kUni (by decide)]; rfl) rfl) fun t ⟨hm, hk⟩ => ?_
  have hf : Frm P.B [(8 * kI, 8), (8 * kUni, 8)] s.mem t.mem := by
    rw [hm]
    exact (Frm.of_outside (writeW_outside _ P.B _ (d := 8 * kI) (by decide)) (by simp)).trans
      (Frm.of_outside (writeW_outside _ P.B _ (d := 8 * kUni) (by decide)) (by simp))
  have k : Keep mmRegs s t := hk.mono (by decide)
  have ht := h.ready.of_frm P.dims hf k ((k.gpr (by decide)).trans h.ready.good.rdi)
    (by rng_disj) (by rng_disj) (by rng_disj)
  have hus : word t.mem P.B (8 * kUsed) = BitVec.ofNat 64 used := by
    rw [hf.word_eq (by rng_disj) (by decide : 8 * kUsed + 8 ≤ 2 ^ 64)]; exact h.used
  have hpt := h.advance ht hus hf.work k (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only [kI, kElen, kUni, kP, sFn] <;> have := P.z256 <;> omega) (by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> rng_disj)
  refine ⟨hpt, ?_, ?_, hu, by decide, by simp, by decide, Or.inl (by decide), rfl,
    hf.work.mono (by simp [drawRoundRanges, sampleRoundRanges]), k⟩
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [hm, word_writeW_self]

end VG.Proof.Dsa.X86_64.Generation
