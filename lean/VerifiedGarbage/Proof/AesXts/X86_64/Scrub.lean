module

public import VerifiedGarbage.Spec.Xts.Contract
public import VerifiedGarbage.Spec.Xts.OutOfPlace
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Verified
public import VerifiedGarbage.Proof.AesXts.X86_64.UnitTo.Verified
import VerifiedGarbage.Proof.Aes.X86_64.ModesScrub

/-!
# XTS-AES of data units on x86-64, without secret residue

`vg_aes_xts_encrypt_unit`, `vg_aes_xts_decrypt_unit` and their out-of-place
counterparts over an implementation of the whole-block functions
(`AesXts.X86_64.XtsImpl`), each followed by `Impl.Scrub.X86_64.scrubTail`
(`X86_64.Scrub.withScrub`) where the implementation gives the residue
analysis of the instance (`XtsImpl.encUnitRes`, …), and otherwise with its
16 or 24 bytes of stack wiped (`X86_64.RScrub.withScrubOrAll`). Their postconditions
read the memory on return only within the buffers (`X86_64.Scrub.PostOut`):
the data, or the output as long as the input, which the out-of-place
functions' precondition requires.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub VG.Proof.Aes.X86_64.ModesScrub

/-! ## Postconditions -/

theorem encryptUnitOut (stack : Nat) :
    PostOut (Spec.Xts.aesEncryptUnitContract X86_64.abi stack) (Spec.Xts.aesUnitSig.retBits 64) :=
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
    PostOut (Spec.Xts.aesDecryptUnitContract X86_64.abi stack) (Spec.Xts.aesUnitSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, tsch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Xts.aesUnitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, Spec.Xts.KeySchedules m sch tsch _ key → _ = some (Spec.Aes.bytesAt m₂ dt _)
      intro key hk
      rw [bytesAt_of0 hb.2.2.2.1 (len_le1 ln)]
      exact h key hk

theorem encryptUnitToOut (stack : Nat) :
    PostOut (Spec.Xts.aesEncryptUnitToContract X86_64.abi stack) (Spec.Xts.aesUnitToSig.retBits 64) :=
  postOut_of_local_pre (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hpre hb h => by
    match vs, hlen with
    | [sch, tsch, rd, iv, sr, ln, dt, dl, sc], _ =>
      simp only [Spec.Xts.aesUnitToSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      have hdl : ((ArgWord.int X86_64.abi.ptrBits).ofRaw dl).toNat = ((ArgWord.int X86_64.abi.ptrBits).ofRaw ln).toNat :=
        hpre.2.2.2
      show ∀ key, Spec.Xts.KeySchedules m sch tsch _ key → _ = some (Spec.Aes.bytesAt m₂ dt _)
      intro key hk
      rw [bytesAt_of0 hb.2.2.2.2.1 (by rw [← hdl]; exact len_le1 dl)]
      exact h key hk

theorem decryptUnitToOut (stack : Nat) :
    PostOut (Spec.Xts.aesDecryptUnitToContract X86_64.abi stack) (Spec.Xts.aesUnitToSig.retBits 64) :=
  postOut_of_local_pre (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hpre hb h => by
    match vs, hlen with
    | [sch, tsch, rd, iv, sr, ln, dt, dl, sc], _ =>
      simp only [Spec.Xts.aesUnitToSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      have hdl : ((ArgWord.int X86_64.abi.ptrBits).ofRaw dl).toNat = ((ArgWord.int X86_64.abi.ptrBits).ofRaw ln).toNat :=
        hpre.2.2.2
      show ∀ key, Spec.Xts.KeySchedules m sch tsch _ key → _ = some (Spec.Aes.bytesAt m₂ dt _)
      intro key hk
      rw [bytesAt_of0 hb.2.2.2.2.1 (by rw [← hdl]; exact len_le1 dl)]
      exact h key hk

/-! ## The registrations -/

open VG.X86_64.RScrub VG.Proof.AesXts.X86_64

/-- `vg_aes_xts_encrypt_unit` over `v`. -/
def encryptUnitReg (v : XtsImpl) : Registration Spec.Xts.aesEncryptUnitApi X86_64.target :=
  withScrubOrAll {
    suffix := v.suffix
    code := Impl.AesXts.X86_64Unit.encrypt v.xts
    stack := 16
    verified := Unit.encrypt_verified v
    spSafe := Unit.encrypt_spSafe v } (encryptUnitOut _) [] (pubOk_nil _) v.encUnitRes

/-- `vg_aes_xts_decrypt_unit` over `v`. -/
def decryptUnitReg (v : XtsImpl) : Registration Spec.Xts.aesDecryptUnitApi X86_64.target :=
  withScrubOrAll {
    suffix := v.suffix
    code := Impl.AesXts.X86_64Unit.decrypt v.xts
    stack := 16
    verified := Unit.decrypt_verified v
    spSafe := Unit.decrypt_spSafe v } (decryptUnitOut _) [] (pubOk_nil _) v.decUnitRes

/-- `vg_aes_xts_encrypt_unit_to` over `v`. -/
def encryptUnitToReg (v : XtsImpl) : Registration Spec.Xts.aesEncryptUnitToApi X86_64.target :=
  withScrubOrAll {
    suffix := v.suffix
    code := Impl.AesXts.X86_64UnitTo.encrypt v.xts (UnitTo.UnitImpl.of v).xt
    stack := 24
    verified := UnitTo.encrypt_verified (.of v)
    spSafe := UnitTo.encrypt_spSafe (.of v) } (encryptUnitToOut _) [] (pubOk_nil _) v.encUnitToRes

/-- `vg_aes_xts_decrypt_unit_to` over `v`. -/
def decryptUnitToReg (v : XtsImpl) : Registration Spec.Xts.aesDecryptUnitToApi X86_64.target :=
  withScrubOrAll {
    suffix := v.suffix
    code := Impl.AesXts.X86_64UnitTo.decrypt v.xts (UnitTo.UnitImpl.of v).xt
    stack := 24
    verified := UnitTo.decrypt_verified (.of v)
    spSafe := UnitTo.decrypt_spSafe (.of v) } (decryptUnitToOut _) [] (pubOk_nil _) v.decUnitToRes

end VG.Proof.AesXts.X86_64.Scrub
