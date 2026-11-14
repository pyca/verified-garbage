module

public import VerifiedGarbage.Spec.Ctr.Final
public import VerifiedGarbage.Spec.Cfb.Final
public import VerifiedGarbage.Spec.Ofb.Final
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Aes.X86_64.BlocksVariant
public import VerifiedGarbage.Proof.AesCtr.X86_64.Verified
public import VerifiedGarbage.Proof.AesCtr.X86_64.Final
public import VerifiedGarbage.Proof.AesCfb.X86_64.Final
public import VerifiedGarbage.Proof.AesOfb.X86_64.Final
import VerifiedGarbage.Proof.Aes.X86_64.ModesScrub

/-!
# AES-CTR and the AES final functions on x86-64, without secret residue

`vg_aes_ctr`, `vg_aes_ctr_final`, `vg_aes_cfb128_encrypt_final`,
`vg_aes_cfb128_decrypt_final` and `vg_aes_ofb_final` over each
implementation, each followed by `Impl.Scrub.X86_64.scrub` with every
granule of its stack wiped (`X86_64.RScrub.withScrubAllM`): 8 bytes for
`vg_aes_ctr`, whose working space is its caller's `scratch`, and the final
functions' frames (`save`, which they no longer zero themselves) with the
16 bytes of their calls below them, 80 or 96 bytes. Their postconditions
read the memory on return only within the buffers (`X86_64.Scrub.PostOut`):
the data and the counter or chaining block. The final functions call the
whole-block functions' code as internal functions of their own,
`vg_aes_ctr<suffix>_core`, … (`Impl.AesCtr.X86_64.cryptFinal`).
-/

@[expose] public section

namespace VG.Proof.Aes.X86_64.FinalScrub

open VG.X86_64 VG.X86_64.Scrub VG.Proof.Aes.X86_64.ModesScrub

/-! ## Postconditions -/

theorem ctrOut (stack : Nat) :
    PostOut (Spec.Ctr.aesContract X86_64.abi stack) (Spec.Ctr.aesSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, ctr, dt, ln, sc], _ =>
      simp only [Spec.Ctr.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ ctr 16 = _
      intro key hk
      rw [blocksAt_of0 hb.2.2.1 (len_le ln 16), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ctrFinalOut (stack : Nat) :
    PostOut (Spec.Ctr.aesFinalContract X86_64.abi stack) (Spec.Ctr.aesFinalSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, ctr, dt, ln, sc], _ =>
      simp only [Spec.Ctr.aesFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ ctr 16 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2.1 (len_le1 ln), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbEncryptFinalOut (stack : Nat) :
    PostOut (Spec.Cfb.aesEncryptFinalContract X86_64.abi stack) (Spec.Cfb.aesFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Cfb.aesFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2.1 (len_le1 ln), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbDecryptFinalOut (stack : Nat) :
    PostOut (Spec.Cfb.aesDecryptFinalContract X86_64.abi stack) (Spec.Cfb.aesFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Cfb.aesFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2.1 (len_le1 ln), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ofbFinalOut (stack : Nat) :
    PostOut (Spec.Ofb.aesFinalContract X86_64.abi stack) (Spec.Ofb.aesFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Ofb.aesFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2.1 (len_le1 ln), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

/-! ## The registrations -/

open VG.X86_64.RScrub VG.Proof.Aes.X86_64

/-- `vg_aes_ctr` over `v`. -/
def ctrReg (v : Ctr32Impl) : Registration Spec.Ctr.aesApi X86_64.target :=
  withScrubAllM {
    suffix := v.suffix
    code := Impl.AesCtr.X86_64.crypt v.callee
    stack := 8
    verified := Proof.AesCtr.keyed (Proof.AesCtr.X86_64.crypt_verified v)
    spSafe := Proof.AesCtr.X86_64.crypt_spSafe v } (ctrOut _)

/-- `vg_aes_ctr_final` over `v`. -/
def ctrFinalReg (v : Ctr32Impl) : Registration Spec.Ctr.aesFinalApi X86_64.target :=
  withScrubAllM {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 80 0 (Impl.AesCtr.X86_64.cryptFinal v.callee v.suffix)
    stack := 96
    verified := Proof.AesCtr.final_keyed (Proof.AesCtr.X86_64.cryptFinal_framed v)
    spSafe := Proof.AesCtr.X86_64.cryptFinal_framed_spSafe v } (ctrFinalOut _)

/-- `vg_aes_cfb128_encrypt_final` over `v`. -/
def cfbEncryptFinalReg (v : BlocksImpl) : Registration Spec.Cfb.aesEncryptFinalApi X86_64.target :=
  withScrubAllM {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 64 0 (Impl.AesCfb.X86_64.encryptFinal v.enc v.suffix)
    stack := 80
    verified := Proof.AesCfb.encryptFinal_keyed (Proof.AesCfb.X86_64.encryptFinal_framed v)
    spSafe := Proof.AesCfb.X86_64.encryptFinal_framed_spSafe v } (cfbEncryptFinalOut _)

/-- `vg_aes_cfb128_decrypt_final` over `v`. -/
def cfbDecryptFinalReg (v : BlocksImpl) : Registration Spec.Cfb.aesDecryptFinalApi X86_64.target :=
  withScrubAllM {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 64 0 (Impl.AesCfb.X86_64.decryptFinal v.enc v.suffix)
    stack := 80
    verified := Proof.AesCfb.decryptFinal_keyed (Proof.AesCfb.X86_64.decryptFinal_framed v)
    spSafe := Proof.AesCfb.X86_64.decryptFinal_framed_spSafe v } (cfbDecryptFinalOut _)

/-- `vg_aes_ofb_final` over `v`. -/
def ofbFinalReg (v : BlocksImpl) : Registration Spec.Ofb.aesFinalApi X86_64.target :=
  withScrubAllM {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 64 0 (Impl.AesOfb.X86_64.cryptFinal v.enc v.suffix)
    stack := 80
    verified := Proof.AesOfb.final_keyed (Proof.AesOfb.X86_64.cryptFinal_framed v)
    spSafe := Proof.AesOfb.X86_64.cryptFinal_framed_spSafe v } (ofbFinalOut _)

end VG.Proof.Aes.X86_64.FinalScrub
