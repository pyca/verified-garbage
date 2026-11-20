module

public import VerifiedGarbage.Proof.Argon2.Arm.Derive.Verified
public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Argon2.Arm.CompressLit
meta import VerifiedGarbage.Proof.Argon2.Arm.Derive.Verified
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Argon2.Arm.CompressLit

/-!
# Argon2 on ARMv7, without secret residue

`vg_argon2` keeps its saved registers and locals in frames within the 240
bytes of stack its contract reserves, so its cleanup zeroes those bytes on
return (`Impl.Argon2.Arm.Fn.derive`, `Arm.Scrub.scrubF`), and `Fn.derive`
below states that it returns without secret residue
(`Arm.Scrub.verifiedScrubbedF`). Its postcondition reads the memory on return
only within `out` (`Arm.Scrub.PostOut`), as on RISC-V
(`Proof/Argon2/RISCV64/Scrub.lean`); what the cleanup needs of the code
(`scrubSideF`: its frames within the 240 bytes, no indirect call) the kernel
evaluates when this module is built.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub

theorem deriveOut :
    PostOut (Spec.Argon2.deriveContract abi 240) (Spec.Argon2.deriveSig.retBits abi.ptrBits) :=
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
      simp only [ArgWord.ofRaw, show abi.ptrBits = 32 from rfl, BitVec.toNat_setWidth] at this
      have := Nat.mod_le outLen.toNat (2 ^ 32)
      exact (ho _ (Offset.contains_base _ (by simp only [Elem.size] at *; omega_arith) (by omega_arith))).symm

theorem deriveSide : scrubSideF Impl.Argon2.Arm.Derive.derive 240 [] = true := by lit_decide

end VG.Proof.Argon2.Arm.Scrub

namespace VG.Proof.Argon2.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_argon2`. -/
theorem derive :
    VerifiedScrubbed target Impl.Argon2.Arm.Fn.derive (Spec.Argon2.deriveContract abi 240) 0 :=
  verifiedScrubbedF (api := Spec.Argon2.deriveApi)
    { code := Impl.Argon2.Arm.Derive.derive
      verified := Proof.Argon2.Arm.Derive.deriveShared_verified }
    Scrub.deriveOut Scrub.deriveSide

end VG.Proof.Argon2.Arm.Fn
