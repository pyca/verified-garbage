module

public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesXts.PPC64LE.Unit.Verified
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Framework.Lit

/-!
# XTS-AES on PPC64LE, without secret residue

`vg_aes_xts_encrypt_unit` and `vg_aes_xts_decrypt_unit`, each followed by
`Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.scrubOf`), which clears the
volatile registers they may write: they have no frames (their working space
is the caller's scratch buffer, and their calls keep the return address in
the link register), so there is no stack to wipe. Their postconditions read
the memory on return only within the data, by RISC-V's proofs
(`Proof/AesXts/RISCV64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.AesXts.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub VG.Proof.Aes.ScrubLocal

/-! ## Postconditions -/

theorem len_le1 (x : BitVec 64) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat ≤ x.toNat * Elem.u8.size :=
  Nat.le_of_eq (Nat.mul_one _).symm

theorem encryptUnitOut (stack : Nat) :
    PostOut (Spec.Xts.aesEncryptUnitContract PPC64LE.abi stack) (Spec.Xts.aesUnitSig.retBits 64) :=
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
    PostOut (Spec.Xts.aesDecryptUnitContract PPC64LE.abi stack) (Spec.Xts.aesUnitSig.retBits 64) :=
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

/-- `Spec.Xts.aesEncryptUnitApi`. -/
def encryptUnitReg : Registration Spec.Xts.aesEncryptUnitApi PPC64LE.target :=
  scrubOf {
      code := Impl.AesXts.PPC64LEUnit.encrypt
      verified := Proof.AesXts.PPC64LE.Unit.encrypt_verified }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17,
        .v18, .v19]⟩
    (encryptUnitOut _)
    (by dsimp only; lit_decide)

/-- `Spec.Xts.aesDecryptUnitApi`. -/
def decryptUnitReg : Registration Spec.Xts.aesDecryptUnitApi PPC64LE.target :=
  scrubOf {
      code := Impl.AesXts.PPC64LEUnit.decrypt
      verified := Proof.AesXts.PPC64LE.Unit.decrypt_verified }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17,
        .v18, .v19]⟩
    (decryptUnitOut _)
    (by dsimp only; lit_decide)

end VG.Proof.AesXts.PPC64LE.Scrub
