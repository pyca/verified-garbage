module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Scrypt.Arm.Whole.Verified
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Scrypt.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Scrypt.Arm.Whole.Verified
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Scrypt.Arm.Lit

/-!
# scrypt on ARMv7, without secret residue

`vg_scrypt` calls PBKDF2-HMAC-SHA256 and ROMix from frames, within the 40
bytes of stack its contract reserves (`scrypt_armStack`). Its postcondition
reads the memory on return only within `out` (`Arm.Scrub.PostOut`, as
RISC-V's `Proof/Scrypt/RISCV64/Scrub.lean` proves it, on the arguments' low
32 bits as DSA's `Proof/Dsa/Arm/Scrub.lean` reads them), so it is registered
followed by a wipe of those 40 bytes and of the registers a callee may
change (`Arm.Scrub.scrubRegF`).
-/

@[expose] public section

namespace VG.Proof.Scrypt.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Impl.Scrypt.Arm

/-- The `n` bytes at `o` read the memory only within `⟨o, N⟩`, `n ≤ N`. -/
theorem bytesAt_of {m₁ m₂ : Mem} {o : Addr} {n N : Nat}
    (h : ∀ a, Region.Contains ⟨o, N⟩ a 1 → m₁ a = m₂ a) (hN : n ≤ N) (hn : n < 2 ^ 64) :
    Spec.Scrypt.bytesAt m₂ o n = Spec.Scrypt.bytesAt m₁ o n := by
  unfold Spec.Scrypt.bytesAt
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  exact (h _ (Offset.contains_base _ (by omega_using [this, hN]) (by omega_using [this, hn]))).symm

theorem scryptOut (stack : Nat) :
    PostOut (Spec.Scrypt.scryptContract abi stack) (Spec.Scrypt.scryptSig.retBits abi.ptrBits) :=
  postOut_of_local ScrubAbi.plain (sig := Spec.Scrypt.scryptSig) fun
    | [_, _, _, _, _, _, _, _, _, _, _, out, outLen], m, m₁, m₂, ret, _, hb, h => by
      simp only [Spec.Scrypt.scryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ ret at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ ret
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have hle : (outLen.setWidth abi.ptrBits).toNat ≤ outLen.toNat * 1 := by
        rw [BitVec.toNat_setWidth, Nat.mul_one]; exact Nat.mod_le _ _
      rw [bytesAt_of hb.2.2.2.2.2 hle (by have := outLen.isLt; omega)]
      exact h

theorem roMix_armStack : armStack roMix = 0 := by lit_decide

/-- The frames of `vg_scrypt` use at most the 40 bytes its contract reserves:
16 for PBKDF2's stack arguments and its 24, and 8 for ROMix's. -/
theorem scrypt_armStack :
    armStack (scrypt "vg_pbkdf2_hmac_sha256_scratch" Whole.pbkC) ≤ 40 := by
  have := Whole.pbk_stack
  simp only [scrypt, pbkCall, romixLoop, armStack, roMix_armStack, List.length_cons,
    List.length_nil, Nat.max_le]
  omega_arith

theorem scrypt_noIcall : noIcall (scrypt "vg_pbkdf2_hmac_sha256_scratch" Whole.pbkC) = true := by
  lit_decide

theorem frameOk_40 : FrameOk 40 := by decide

/-- `Spec.Scrypt.scryptApi`. -/
def scryptReg : Registration Spec.Scrypt.scryptApi target :=
  Arm.Scrub.scrubRegF {
      code := scrypt "vg_pbkdf2_hmac_sha256_scratch" Whole.pbkC
      verified := Whole.scrypt_verified }
    scrypt_armStack scrypt_noIcall frameOk_40 (scryptOut _) rfl

end VG.Proof.Scrypt.Arm.Scrub
