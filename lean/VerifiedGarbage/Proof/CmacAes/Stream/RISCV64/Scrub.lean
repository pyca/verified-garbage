module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.CmacAes.Stream.RISCV64.Frame
import VerifiedGarbage.Proof.Aes.ScrubLocal

/-!
# Streaming AES-CMAC on RISC-V, without secret residue

`vg_cmac_aes_init`, `vg_cmac_aes_absorb` and `vg_cmac_aes_finish`, each
followed by `Impl.Scrub.RISCV64.scrubTail` (`RISCV64.Scrub.withScrub`), which
clears the caller-saved registers and the stack its frames used, their
2304 bytes of working space with it. Their postconditions read the memory
on return only within the state or the MAC (`RISCV64.Scrub.PostOut`), as on
x86-64 (`Proof/CmacAes/Stream/X86_64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub VG.Proof.Aes.ScrubLocal

/-! ## Postconditions -/

theorem finishOut (stack : Nat) :
    PostOut (Spec.Cmac.aesFinishContract RISCV64.abi stack) (Spec.Cmac.aesFinishSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [st, rd, ct, out], _ =>
      simp only [Spec.Cmac.aesFinishSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      intro key msg hr hro hc hlt
      show Spec.Aes.bytesAt m₂ out 16 = _
      rw [bytesAt_of0 hb.2 (by decide)]
      exact h key msg hr hro hc hlt

theorem initOut (stack : Nat) :
    PostOut (Spec.Cmac.aesInitContract RISCV64.abi stack) (Spec.Cmac.aesInitSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [st, key, kl], _ =>
      simp only [Spec.Cmac.aesInitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      exact Proof.CmacAes.Stream.repr_congr_304 (agree_le hb.1 (by decide)) h

theorem absorbOut (stack : Nat) :
    PostOut (Spec.Cmac.aesAbsorbContract RISCV64.abi stack) (Spec.Cmac.aesAbsorbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [st, rd, ct, dt, ln], _ =>
      simp only [Spec.Cmac.aesAbsorbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      intro key msg hr hro hc hlt
      exact Proof.CmacAes.Stream.repr_congr_304 (agree_le hb.1 (by decide)) (h key msg hr hro hc hlt)

/-! ## The registrations -/

/-- `vg_cmac_aes_init`. -/
def initReg : Registration Spec.Cmac.aesInitApi RISCV64.target :=
  withScrub {
      code := Impl.StackScratch.RISCV64.withStackScratch 2304 .a3 Impl.CmacAes.Stream.RISCV64.init
      verified := Proof.CmacAes.Stream.RISCV64.init_framed }
    (initOut _)

/-- `vg_cmac_aes_absorb`. -/
def absorbReg : Registration Spec.Cmac.aesAbsorbApi RISCV64.target :=
  withScrub {
      code := Impl.StackScratch.RISCV64.withStackScratch 2304 .a5 Impl.CmacAes.Stream.RISCV64.absorb
      verified := Proof.CmacAes.Stream.RISCV64.absorb_framed }
    (absorbOut _)

/-- `vg_cmac_aes_finish`. -/
def finishReg : Registration Spec.Cmac.aesFinishApi RISCV64.target :=
  withScrub {
      code := Impl.StackScratch.RISCV64.withStackScratch 2304 .a4 Impl.CmacAes.Stream.RISCV64.finish
      verified := Proof.CmacAes.Stream.RISCV64.finish_framed }
    (finishOut _)

end VG.Proof.CmacAes.Stream.RISCV64.Scrub
