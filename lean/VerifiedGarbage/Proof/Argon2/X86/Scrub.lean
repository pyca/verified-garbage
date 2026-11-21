module

public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Proof.Argon2.X86.Derive.Verified
public import VerifiedGarbage.Impl.Argon2.X86.Derive
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Argon2.X86.CompressLit
import VerifiedGarbage.Proof.Blake2.X86.LitB
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Proof.Argon2.X86.Derive.Verified
meta import VerifiedGarbage.Impl.Argon2.X86.Derive
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Argon2.X86.CompressLit
meta import VerifiedGarbage.Proof.Blake2.X86.LitB

/-!
# Argon2 on x86 (32-bit), without secret residue

`vg_argon2` runs in its frames and calls H′, which calls BLAKE2b's streaming
functions and its compression function, within the 244 bytes of stack its
contract reserves. The code as emitted (`Impl.Argon2.X86.Fn.derive`) then
zeroes those bytes below `esp` and clears the registers a callee may change,
and returns without secret residue (`X86.Scrub.verifiedScrubbedAll`), given that
its postcondition reads the memory on return only within `out` (`deriveOut`,
as on AArch64, `Proof/Argon2/AArch64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Argon2.X86.Scrub

open VG VG.X86 VG.X86.Scrub

/-- `vg_argon2`'s postcondition reads the memory on return only within `out`. -/
theorem deriveOut (stack : Nat) :
    PostOut (Spec.Argon2.deriveContract X86.abi stack) (Spec.Argon2.deriveSig.retBits 32) :=
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
      simp only [ArgWord.ofRaw, show X86.abi.ptrBits = 32 from rfl, BitVec.toNat_setWidth] at this
      have := Nat.mod_le outLen.toNat (2 ^ 32)
      have := outLen.isLt
      exact (ho _ (Offset.contains_base _ (by simp only [Elem.size] at *; omega_arith) (by omega_arith))).symm

/-- `vg_argon2` as emitted, cleanup included. -/
theorem derive_scrubbed :
    VerifiedScrubbed target Impl.Argon2.X86.Fn.derive (Spec.Argon2.deriveContract X86.abi 244) 0 :=
  verifiedScrubbedAll (api := Spec.Argon2.deriveApi)
    { code := Impl.Argon2.X86.Derive.derive
      verified := Proof.Argon2.X86.Derive.deriveShared_verified }
    (deriveOut _)

end VG.Proof.Argon2.X86.Scrub
