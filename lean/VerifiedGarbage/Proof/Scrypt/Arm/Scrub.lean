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
reads the memory on return only within `out` (`Arm.Scrub.PostOut`, by
RISC-V's proof, `Proof/Scrypt/RISCV64/Scrub.lean`), so it is registered
followed by a wipe of those 40 bytes and of the registers a callee may
change (`Arm.Scrub.scrubRegF`).
-/

@[expose] public section

namespace VG.Proof.Scrypt.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Impl.Scrypt.Arm

theorem scryptOut (stack : Nat) :
    PostOut (Spec.Scrypt.scryptContract abi stack) (Spec.Scrypt.scryptSig.retBits abi.ptrBits) :=
  postOut_of_local ScrubAbi.plain (sig := Spec.Scrypt.scryptSig)
    fun vs m m₁ m₂ ret hlen hb h => by
    obtain ⟨pw, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 12) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨pwLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨salt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨saltLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨r, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨b, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨blen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨v, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨vlen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨scratch, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨slen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨outLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    simp only [Spec.Scrypt.scryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    have hby : Spec.Scrypt.bytesAt m₂ out outLen.toNat = Spec.Scrypt.bytesAt m₁ out outLen.toNat := by
      unfold Spec.Scrypt.bytesAt
      refine List.map_congr_left fun i hi => ?_
      have := List.mem_range.mp hi
      exact (hb.2.2.2.2.2 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_using [this])
        (by have := outLen.isLt; omega_arith))).symm
    replace h : Spec.Scrypt.scrypt (Spec.Scrypt.bytesAt m pw pwLen.toNat) (Spec.Scrypt.bytesAt m salt saltLen.toNat)
        (vlen.toNat / r.toNat) r.toNat (blen.toNat / r.toNat) outLen.toNat =
        some (Spec.Scrypt.bytesAt m₁ out outLen.toNat) := h
    show _ = some (Spec.Scrypt.bytesAt m₂ out outLen.toNat)
    rw [hby]; exact h

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
