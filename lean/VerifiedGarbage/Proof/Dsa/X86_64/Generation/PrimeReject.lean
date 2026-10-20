module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeInput
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFrame
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages

/-! # Trial-division rejection preserves the tape without consuming a witness -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64

theorem primeReject_ok {P : PrimeParams} {mi : BitVec 64} {used : Nat} {s : State}
    (h : PrimeInput P mi used s) :
    WP isa (.block [.mov32 .rax (.imm 3), .store (hdr kStat) .rax]) s fun t =>
      PrimeInput P mi used t ∧ word t.mem P.B (8 * kStat) = BitVec.ofNat 64 3 ∧
      Frm P.B [(8 * kStat, 8)] s.mem t.mem ∧ Keep mmRegs s t := by
  have hz := P.z256
  have hst := h.good.scr.st (d := 8 * kStat) (by change 240 ≤ P.Z; omega)
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.mem = s.mem.writeW (off P.B (8 * kStat)) (BitVec.ofNat 64 3))
    (by xrun [State.ea, hdr, hdrOff, h.good.rdi, hst]; rfl) rfl) fun t ⟨hm, hk⟩ => ?_
  have hf : Frm P.B [(8 * kStat, 8)] s.mem t.mem := by
    rw [hm]; exact Frm.of_outside (writeW_outside _ P.B _ (d := 8 * kStat) (by decide)) (by simp)
  have hg : Good t P.B P.Z P.w mi :=
    ⟨h.good.scr.congr hk.2.2, (hk.gpr (by decide)).trans h.good.rdi,
      by rw [hm]; exact h.good.hdr.store (by decide) (by decide) _⟩
  have hn : wv t.mem P.B (slot P.w aN) P.w = P.N := by
    rw [hf.wv_eq (by rng_disj)
      (by have := P.dims.z; have := h.good.scr.nowrap; simp only [slot, hdrBytes, aN] at *; omega)]
    exact h.n
  have k : Keep mmRegs s t := hk.mono (by decide)
  have ht := h.advance hg hn hf k
    (by simp only [List.mem_singleton, forall_eq]; change 240 ≤ P.Z; omega)
    (by
      intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rng_disj)
  exact ⟨ht, by rw [hm, word_writeW_self], hf, k⟩

end VG.Proof.Dsa.X86_64.Generation
