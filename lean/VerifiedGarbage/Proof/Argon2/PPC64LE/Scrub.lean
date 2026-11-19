module

public import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Verified
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Argon2.PPC64LE.CompressLit

/-!
# Argon2 on PPC64LE, without secret residue

`vg_argon2`, followed by `Impl.Scrub.PPC64LE.scrubTail`
(`PPC64LE.Scrub.scrubOf`), which clears the volatile registers and the 384
bytes of stack its frames use. Its postcondition reads the memory on return
only within `out` (`PPC64LE.Scrub.PostOut`), by RISC-V's proof
(`Proof/Argon2/RISCV64/Scrub.lean`). `scrubOf`'s side condition
(`scrubSide`) is proved at the registration, by the kernel's evaluation of
it when this module is built.
-/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub

/-! ## Postconditions -/

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

/-! ## The registration -/

/-- `Spec.Argon2.deriveApi`. -/
def deriveReg : Registration Spec.Argon2.deriveApi PPC64LE.target :=
  scrubOf {
      code := Impl.Argon2.PPC64LE.Derive.derive
      verified := Proof.Argon2.PPC64LE.Derive.deriveShared_verified }
    384 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (deriveOut _)
    (by dsimp only; lit_decide)

end VG.Proof.Argon2.PPC64LE.Scrub
