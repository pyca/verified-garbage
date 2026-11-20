module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall
public import VerifiedGarbage.Impl.AesOfb.X86_64.Fn
public import VerifiedGarbage.Impl.AesCfb8.X86_64.Fn
public import VerifiedGarbage.Impl.AesCfb.X86_64.Fn
public import VerifiedGarbage.Spec.Cfb8.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Aes.X86_64.BlocksVariant
public import VerifiedGarbage.Proof.AesCfb8.X86_64.Verified
public import VerifiedGarbage.Proof.AesCfb.X86_64.Verified
public import VerifiedGarbage.Proof.AesOfb.X86_64.Verified
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.Aes.ScrubLocal

/-!
# AES-CFB8, AES-CFB128 and AES-OFB on x86-64, without secret residue

`vg_aes_cfb8_encrypt`, `vg_aes_cfb8_decrypt`, `vg_aes_cfb128_encrypt`,
`vg_aes_cfb128_decrypt` and `vg_aes_ofb` over an implementation of the AES
block functions (`Aes.X86_64.BlocksImpl`), each followed by
`Impl.Scrub.X86_64.scrubTail` (`X86_64.Scrub.withScrub`) where the
implementation gives the residue analysis of the instance (`cfb8EncRes`,
`cfb8DecRes`, `cfbEncRes`, `cfbDecRes`, `ofbRes`), and otherwise with its 8
bytes of stack wiped (`X86_64.RScrub.withScrubOrAll`). Their postconditions read
the memory on return only within the buffers (`X86_64.Scrub.PostOut`): the
data and the input block. The `_final` functions call the code of the
CFB128 and OFB ones as internal functions of their own,
`vg_aes_cfb128_encrypt<suffix>_core`, … (`Impl.AesCfb.X86_64.final`).
-/

@[expose] public section

namespace VG.Proof.Aes.X86_64.ModesScrub

open VG.X86_64 VG.X86_64.Scrub VG.Proof.Aes.ScrubLocal

/-! ## Locality -/

theorem len_le (x : BitVec 64) (k : Nat) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat * k ≤ x.toNat * k :=
  Nat.le_refl _

theorem len_le1 (x : BitVec 64) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat ≤ x.toNat * Elem.u8.size :=
  Nat.le_of_eq (Nat.mul_one _).symm

/-! ## Postconditions -/

theorem cfb8EncryptOut (stack : Nat) :
    PostOut (Spec.Cfb8.aesEncryptContract X86_64.abi stack) (Spec.Cfb8.aesSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Cfb8.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2.1 (len_le1 ln), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfb8DecryptOut (stack : Nat) :
    PostOut (Spec.Cfb8.aesDecryptContract X86_64.abi stack) (Spec.Cfb8.aesSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Cfb8.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2.1 (len_le1 ln), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbEncryptOut (stack : Nat) :
    PostOut (Spec.Cfb.aesEncryptContract X86_64.abi stack) (Spec.Cfb.aesSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Cfb.aesSig, Spec.Cbc.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [blocksAt_of0 hb.2.2.1 (len_le ln 16), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbDecryptOut (stack : Nat) :
    PostOut (Spec.Cfb.aesDecryptContract X86_64.abi stack) (Spec.Cfb.aesSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Cfb.aesSig, Spec.Cbc.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [blocksAt_of0 hb.2.2.1 (len_le ln 16), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ofbOut (stack : Nat) :
    PostOut (Spec.Ofb.aesContract X86_64.abi stack) (Spec.Ofb.aesSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Ofb.aesSig, Spec.Cbc.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [blocksAt_of0 hb.2.2.1 (len_le ln 16), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

/-! ## The registrations -/

open VG.X86_64.RScrub VG.Proof.Aes.X86_64

/-- `Spec.Cfb8.aesEncryptApi`'s function as emitted over `v` (`Impl.AesCfb8.X86_64.Fn.cfb8Encrypt`) meets its
contract in constant time and returns without secret residue: its code is
its code over a stub, with `v`'s where it calls it (`Fill`). -/
theorem cfb8Encrypt_scrubbed (v : BlocksImpl) :
    VerifiedScrubbed target (Impl.AesCfb8.X86_64.Fn.cfb8Encrypt v.level v.enc)
      (Spec.Cfb8.aesEncryptApi.contract X86_64.abi 8) 0 :=
  verifiedScrubbedAllFill (api := Spec.Cfb8.aesEncryptApi) (ks := 0) (n := fun _ => 0) (a := Impl.AesCfb8.X86_64.encrypt ⟨"", .block []⟩)
    { suffix := v.suffix
      code := Impl.AesCfb8.X86_64.encrypt v.enc
      stack := 8
      verified := Proof.AesCfb8.encrypt_keyed (Proof.AesCfb8.X86_64.encrypt_verified v)
      spSafe := Proof.AesCfb8.X86_64.encrypt_spSafe v }
    v.level (cfb8EncryptOut _) (by have := v.encSide; fill_calls) (Nat.zero_le _) (Nat.le_refl _)

theorem cfb8Encrypt_spSafeFn (v : BlocksImpl) :
    (Impl.AesCfb8.X86_64.Fn.cfb8Encrypt v.level v.enc).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.AesCfb8.X86_64.encrypt_spSafe v)

/-- `Spec.Cfb8.aesDecryptApi`'s function as emitted over `v` (`Impl.AesCfb8.X86_64.Fn.cfb8Decrypt`) meets its
contract in constant time and returns without secret residue: its code is
its code over a stub, with `v`'s where it calls it (`Fill`). -/
theorem cfb8Decrypt_scrubbed (v : BlocksImpl) :
    VerifiedScrubbed target (Impl.AesCfb8.X86_64.Fn.cfb8Decrypt v.level v.enc)
      (Spec.Cfb8.aesDecryptApi.contract X86_64.abi 8) 0 :=
  verifiedScrubbedAllFill (api := Spec.Cfb8.aesDecryptApi) (ks := 0) (n := fun _ => 0) (a := Impl.AesCfb8.X86_64.decrypt ⟨"", .block []⟩)
    { suffix := v.suffix
      code := Impl.AesCfb8.X86_64.decrypt v.enc
      stack := 8
      verified := Proof.AesCfb8.decrypt_keyed (Proof.AesCfb8.X86_64.decrypt_verified v)
      spSafe := Proof.AesCfb8.X86_64.decrypt_spSafe v }
    v.level (cfb8DecryptOut _) (by have := v.encSide; fill_calls) (Nat.zero_le _) (Nat.le_refl _)

theorem cfb8Decrypt_spSafeFn (v : BlocksImpl) :
    (Impl.AesCfb8.X86_64.Fn.cfb8Decrypt v.level v.enc).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.AesCfb8.X86_64.decrypt_spSafe v)

/-- `Spec.Cfb.aesEncryptApi`'s function as emitted over `v` (`Impl.AesCfb.X86_64.Fn.cfbEncrypt`) meets its
contract in constant time and returns without secret residue: its code is
its code over a stub, with `v`'s where it calls it (`Fill`). -/
theorem cfbEncrypt_scrubbed (v : BlocksImpl) :
    VerifiedScrubbed target (Impl.AesCfb.X86_64.Fn.cfbEncrypt v.level v.enc)
      (Spec.Cfb.aesEncryptApi.contract X86_64.abi 8) 0 :=
  verifiedScrubbedAllFill (api := Spec.Cfb.aesEncryptApi) (ks := 0) (n := fun _ => 0) (a := Impl.AesCfb.X86_64.encrypt ⟨"", .block []⟩)
    { suffix := v.suffix
      code := Impl.AesCfb.X86_64.encrypt v.enc
      stack := 8
      verified := Proof.AesCfb.encrypt_keyed (Proof.AesCfb.X86_64.encrypt_verified v)
      spSafe := Proof.AesCfb.X86_64.encrypt_spSafe v }
    v.level (cfbEncryptOut _) (by have := v.encSide; fill_calls) (Nat.zero_le _) (Nat.le_refl _)

theorem cfbEncrypt_spSafeFn (v : BlocksImpl) :
    (Impl.AesCfb.X86_64.Fn.cfbEncrypt v.level v.enc).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.AesCfb.X86_64.encrypt_spSafe v)

/-- `Spec.Cfb.aesDecryptApi`'s function as emitted over `v` (`Impl.AesCfb.X86_64.Fn.cfbDecrypt`) meets its
contract in constant time and returns without secret residue: its code is
its code over a stub, with `v`'s where it calls it (`Fill`). -/
theorem cfbDecrypt_scrubbed (v : BlocksImpl) :
    VerifiedScrubbed target (Impl.AesCfb.X86_64.Fn.cfbDecrypt v.level v.enc)
      (Spec.Cfb.aesDecryptApi.contract X86_64.abi 8) 0 :=
  verifiedScrubbedAllFill (api := Spec.Cfb.aesDecryptApi) (ks := 0) (n := fun _ => 0) (a := Impl.AesCfb.X86_64.decrypt ⟨"", .block []⟩)
    { suffix := v.suffix
      code := Impl.AesCfb.X86_64.decrypt v.enc
      stack := 8
      verified := Proof.AesCfb.decrypt_keyed (Proof.AesCfb.X86_64.decrypt_verified v)
      spSafe := Proof.AesCfb.X86_64.decrypt_spSafe v }
    v.level (cfbDecryptOut _) (by have := v.encSide; fill_calls) (Nat.zero_le _) (Nat.le_refl _)

theorem cfbDecrypt_spSafeFn (v : BlocksImpl) :
    (Impl.AesCfb.X86_64.Fn.cfbDecrypt v.level v.enc).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.AesCfb.X86_64.decrypt_spSafe v)

/-- `Spec.Ofb.aesApi`'s function as emitted over `v` (`Impl.AesOfb.X86_64.Fn.ofb`) meets its
contract in constant time and returns without secret residue: its code is
its code over a stub, with `v`'s where it calls it (`Fill`). -/
theorem ofb_scrubbed (v : BlocksImpl) :
    VerifiedScrubbed target (Impl.AesOfb.X86_64.Fn.ofb v.level v.enc)
      (Spec.Ofb.aesApi.contract X86_64.abi 8) 0 :=
  verifiedScrubbedAllFill (api := Spec.Ofb.aesApi) (ks := 0) (n := fun _ => 0) (a := Impl.AesOfb.X86_64.crypt ⟨"", .block []⟩)
    { suffix := v.suffix
      code := Impl.AesOfb.X86_64.crypt v.enc
      stack := 8
      verified := Proof.AesOfb.keyed (Proof.AesOfb.X86_64.crypt_verified v)
      spSafe := Proof.AesOfb.X86_64.crypt_spSafe v }
    v.level (ofbOut _) (by have := v.encSide; fill_calls) (Nat.zero_le _) (Nat.le_refl _)

theorem ofb_spSafeFn (v : BlocksImpl) :
    (Impl.AesOfb.X86_64.Fn.ofb v.level v.enc).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.AesOfb.X86_64.crypt_spSafe v)

end VG.Proof.Aes.X86_64.ModesScrub
