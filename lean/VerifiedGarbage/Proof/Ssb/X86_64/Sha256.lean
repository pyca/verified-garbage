import VerifiedGarbage.Proof.Framework.X86_64.Ssb
import VerifiedGarbage.Proof.Sha256.X86_64.Compress

/-!
# Prototype: SHA-256 compression (x86-64) under speculative store bypass

The compression function keeps the message schedule and the callee-saved
registers in `scratch`, but every value it reloads from there is secret
(only the pointers and the count, in registers, are public), so a stale
reload cannot leak more: it is speculatively constant time for any window.
-/

namespace VG.Proof.Ssb.X86_64.Sha256

open VG.X86_64 VG.Proof.Sha256

theorem compress_specCT : Ssb.SpecCT 64 compressX86_64.pre compressX86_64.pub Impl.Sha256.X86_64.compress :=
  Ssb.specCT (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) (fun _ _ _ _ ⟨h1, h2, h3, h4⟩ =>
    Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4) rfl (by taint_decide)

end VG.Proof.Ssb.X86_64.Sha256
