module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesXts.RISCV64.Unit.Verified
import VerifiedGarbage.Proof.Aes.ScrubLocal

/-!
# XTS-AES on RISC-V, without secret residue

`vg_aes_xts_encrypt_unit` and `vg_aes_xts_decrypt_unit`, each followed by
`Impl.Scrub.RISCV64.scrubTail` (`RISCV64.Scrub.scrubOf`), which clears the
caller-saved registers and the stack its frames used. Their postconditions
read the memory on return only within the data (`RISCV64.Scrub.PostOut`),
as on x86-64 (`Proof/AesXts/X86_64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.AesXts.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub VG.Proof.Aes.ScrubLocal

/-! ## Postconditions -/

theorem len_le1 (x : BitVec 64) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat ≤ x.toNat * Elem.u8.size :=
  Nat.le_of_eq (Nat.mul_one _).symm

theorem encryptUnitOut (stack : Nat) :
    PostOut (Spec.Xts.aesEncryptUnitContract RISCV64.abi stack) (Spec.Xts.aesUnitSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, tsch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Xts.aesUnitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, Spec.Xts.KeySchedules m sch tsch _ key → _ = some (Spec.Aes.bytesAt m₂ dt _)
      intro key hk
      rw [bytesAt_of0 hb.2.2.2.1 (len_le1 ln)]
      exact h key hk

theorem decryptUnitOut (stack : Nat) :
    PostOut (Spec.Xts.aesDecryptUnitContract RISCV64.abi stack) (Spec.Xts.aesUnitSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, tsch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Xts.aesUnitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, Spec.Xts.KeySchedules m sch tsch _ key → _ = some (Spec.Aes.bytesAt m₂ dt _)
      intro key hk
      rw [bytesAt_of0 hb.2.2.2.1 (len_le1 ln)]
      exact h key hk

/-! ## The registrations -/

/-- `vg_aes_xts_encrypt_unit`. -/
def encryptUnitReg : Registration Spec.Xts.aesEncryptUnitApi RISCV64.target :=
  scrubOf {
      code := Impl.AesXts.RISCV64Unit.encrypt
      verified := Proof.AesXts.RISCV64.Unit.encrypt_verified }
    (encryptUnitOut _)

/-- `vg_aes_xts_decrypt_unit`. -/
def decryptUnitReg : Registration Spec.Xts.aesDecryptUnitApi RISCV64.target :=
  scrubOf {
      code := Impl.AesXts.RISCV64Unit.decrypt
      verified := Proof.AesXts.RISCV64.Unit.decrypt_verified }
    (decryptUnitOut _)

end VG.Proof.AesXts.RISCV64.Scrub
