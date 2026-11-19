module

public import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Argon2 on RISC-V, without secret residue

The postcondition of `vg_argon2` reads the memory on return only within
`out` (`RISCV64.Scrub.PostOut`, as AArch64's `Proof/Argon2/AArch64/Scrub.lean`
proves it): the implementation, followed by `Impl.Scrub.RISCV64.scrubTail`
(`RISCV64.Scrub.withScrub`), returns with the caller-saved registers cleared
and the stack its frames used zeroed. Its arguments on the stack are in the
caller's frame, among the buffers (`writeArgs`), which the caller owns.
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub

theorem deriveOut (stack : Nat) :
    PostOut (Spec.Argon2.deriveContract abi stack) (Spec.Argon2.deriveSig.retBits abi.ptrBits) :=
  postOut_of_local ScrubAbi.plain (sig := Spec.Argon2.deriveSig) fun
    | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, out, outLen], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Argon2.deriveSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      have ho := hb.2.2.2.2.2.2
      change _ = _ at h
      change Spec.Blake2.bytesAt m₂ out _ = _
      rw [← h]
      simp only [Spec.Blake2.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      have := List.mem_range.mp hi
      simp only [ArgWord.ofRaw, show abi.ptrBits = 64 from rfl, BitVec.toNat_setWidth] at this
      have := Nat.mod_le outLen.toNat (2 ^ 64)
      exact (ho _ (Offset.contains_base _ (by simp only [Elem.size] at *; omega_arith) (by omega_arith))).symm

end VG.Proof.Argon2.RISCV64.Scrub
