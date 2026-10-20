module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeInput
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFrame
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Small-prime rejection returns composite without consuming witness bytes. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64

theorem primeReject_ok {P : PrimeParams} {used : Nat} {s : State} (h : PrimeInput P used s) :
    WP isa (.block [movi .x3 3, sth .x3 kStat]) s fun t =>
      PrimeInput P used t ∧ word t.mem P.B (8 * kStat) = BitVec.ofNat 64 3 ∧
      Frm P.B [(8 * kStat, 8)] s.mem t.mem ∧ Keep [.x3] s t := by
  have h256 := h.ws.h256
  refine WP.mono (WP.keep [.x3] (Q := fun t =>
    t.mem = s.mem.writeW (off P.B (8 * kStat)) (BitVec.ofNat 64 3))
    (by
      brun [h.ws.x0, hdr_enc (show kStat < 32 by decide),
        h.ws.scr.st (d := 8 * kStat) (by simp only [kStat, sFn]; omega)]
      rfl) rfl rfl rfl) fun t ⟨hm, hk⟩ => ?_
  have hf : Frm P.B [(8 * kStat, 8)] s.mem t.mem := by
    rw [hm]; exact Frm.of_outside (writeW_outside _ P.B _ (by decide)) (by simp)
  have ht := h.ws.congr' hf (by intro r hr; rw [List.mem_singleton.mp hr]; exact KMut.hdr (by decide)) hk (by decide)
  have hn : wv t.mem P.B (slot P.w aN) P.w = P.N := by
    rw [hf.wv_eq (by intro r hr; rw [List.mem_singleton.mp hr]; right; simp only [slot, hdrBytes, aN, kStat, sFn]; omega_arith)
      (by have := h.ws.scr.nowrap; have := h.ws.sl (show aN < 16 by decide); omega)]
    exact h.n
  have hi := h.advance ht hn hf (hk.mono (by decide))
    (by intro r hr; rw [List.mem_singleton.mp hr]; change 256 ≤ P.Z; exact P.z256)
    (by
      intro j hj r hr; rw [List.mem_singleton.mp hr]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  exact ⟨hi, by rw [hm, word_writeW_self], hf, hk⟩

end VG.Proof.Dsa.AArch64.Generation
