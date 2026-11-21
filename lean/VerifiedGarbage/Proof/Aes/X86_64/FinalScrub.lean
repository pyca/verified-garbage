module

public import VerifiedGarbage.Impl.AesCtr.X86_64.Fn
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall
public import VerifiedGarbage.Impl.AesOfb.X86_64.Fn
public import VerifiedGarbage.Impl.AesCfb.X86_64.Fn
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
import VerifiedGarbage.Proof.Aes.ScrubLocal

/-!
# AES-CTR and the AES final functions on x86-64, without secret residue

`vg_aes_ctr`, `vg_aes_ctr_final`, `vg_aes_cfb128_encrypt_final`,
`vg_aes_cfb128_decrypt_final` and `vg_aes_ofb_final` over each
implementation, each followed by `Impl.Scrub.X86_64.scrubWith` with every
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

open VG.X86_64 VG.X86_64.Scrub VG.Proof.Aes.X86_64.ModesScrub VG.Proof.Aes.ScrubLocal

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

/-- `Spec.Ctr.aesApi`'s function as emitted over `v` (`Impl.AesCtr.X86_64.Fn.ctr`) meets its
contract in constant time and returns without secret residue: its code is
its code over a stub, with `v`'s where it calls it (`Fill`). -/
theorem ctr_scrubbed (v : Ctr32Impl) :
    VerifiedScrubbed target (Impl.AesCtr.X86_64.Fn.ctr v.level v.callee)
      (Spec.Ctr.aesApi.contract X86_64.abi 8) 0 :=
  verifiedScrubbedAllFill (api := Spec.Ctr.aesApi) (ks := 0) (n := fun _ => 0) (a := Impl.AesCtr.X86_64.crypt ⟨"", .block [], v.callee.scrOff⟩)
    { suffix := v.suffix
      code := Impl.AesCtr.X86_64.crypt v.callee
      stack := 8
      verified := Proof.AesCtr.keyed (Proof.AesCtr.X86_64.crypt_verified v)
      spSafe := Proof.AesCtr.X86_64.crypt_spSafe v }
    v.level (ctrOut _) (by have := v.side; fill_calls) (Nat.zero_le _) (Nat.le_refl _)
    (ha := by rcases v.scrOk with h | h <;> rw [h] <;> lit_decide)

theorem ctr_spSafeFn (v : Ctr32Impl) :
    (Impl.AesCtr.X86_64.Fn.ctr v.level v.callee).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.AesCtr.X86_64.crypt_spSafe v)

/-- `Spec.Ctr.aesFinalApi`'s function as emitted over `v` (`Impl.AesCtr.X86_64.Fn.ctrFinal`) meets its
contract in constant time and returns without secret residue: its code is
its code over a stub, with `v`'s where it calls it (`Fill`). -/
theorem ctrFinal_scrubbed (v : Ctr32Impl) :
    VerifiedScrubbed target (Impl.AesCtr.X86_64.Fn.ctrFinal v.level v.callee v.suffix)
      (Spec.Ctr.aesFinalApi.contract X86_64.abi 96) 0 :=
  verifiedScrubbedAllFill (api := Spec.Ctr.aesFinalApi) (ks := 0) (n := fun _ => 0) (a := Impl.StackScratch.X86_64.withStackArgScratch 80 0 (Impl.AesCtr.X86_64.cryptFinal ⟨"", .block [], v.callee.scrOff⟩ ""))
    { suffix := v.suffix
      code := Impl.StackScratch.X86_64.withStackArgScratch 80 0 (Impl.AesCtr.X86_64.cryptFinal v.callee v.suffix)
      stack := 96
      verified := Proof.AesCtr.final_keyed (Proof.AesCtr.X86_64.cryptFinal_framed v)
      spSafe := Proof.AesCtr.X86_64.cryptFinal_framed_spSafe v }
    v.level (ctrFinalOut _) (by have := v.side; fill_calls) (Nat.zero_le _) (Nat.le_refl _)
    (ha := by rcases v.scrOk with h | h <;> rw [h] <;> lit_decide)

theorem ctrFinal_spSafeFn (v : Ctr32Impl) :
    (Impl.AesCtr.X86_64.Fn.ctrFinal v.level v.callee v.suffix).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.AesCtr.X86_64.cryptFinal_framed_spSafe v)

/-- `Spec.Cfb.aesEncryptFinalApi`'s function as emitted over `v` (`Impl.AesCfb.X86_64.Fn.cfbEncryptFinal`) meets its
contract in constant time and returns without secret residue: its code is
its code over a stub, with `v`'s where it calls it (`Fill`). -/
theorem cfbEncryptFinal_scrubbed (v : BlocksImpl) :
    VerifiedScrubbed target (Impl.AesCfb.X86_64.Fn.cfbEncryptFinal v.level v.enc v.suffix)
      (Spec.Cfb.aesEncryptFinalApi.contract X86_64.abi 80) 0 :=
  verifiedScrubbedAllFill (api := Spec.Cfb.aesEncryptFinalApi) (ks := 0) (n := fun _ => 0) (a := Impl.StackScratch.X86_64.withStackArgScratch 64 0 (Impl.AesCfb.X86_64.encryptFinal ⟨"", .block []⟩ ""))
    { suffix := v.suffix
      code := Impl.StackScratch.X86_64.withStackArgScratch 64 0 (Impl.AesCfb.X86_64.encryptFinal v.enc v.suffix)
      stack := 80
      verified := Proof.AesCfb.encryptFinal_keyed (Proof.AesCfb.X86_64.encryptFinal_framed v)
      spSafe := Proof.AesCfb.X86_64.encryptFinal_framed_spSafe v }
    v.level (cfbEncryptFinalOut _) (by have := v.encSide; fill_calls) (Nat.zero_le _) (Nat.le_refl _)

theorem cfbEncryptFinal_spSafeFn (v : BlocksImpl) :
    (Impl.AesCfb.X86_64.Fn.cfbEncryptFinal v.level v.enc v.suffix).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.AesCfb.X86_64.encryptFinal_framed_spSafe v)

/-- `Spec.Cfb.aesDecryptFinalApi`'s function as emitted over `v` (`Impl.AesCfb.X86_64.Fn.cfbDecryptFinal`) meets its
contract in constant time and returns without secret residue: its code is
its code over a stub, with `v`'s where it calls it (`Fill`). -/
theorem cfbDecryptFinal_scrubbed (v : BlocksImpl) :
    VerifiedScrubbed target (Impl.AesCfb.X86_64.Fn.cfbDecryptFinal v.level v.enc v.suffix)
      (Spec.Cfb.aesDecryptFinalApi.contract X86_64.abi 80) 0 :=
  verifiedScrubbedAllFill (api := Spec.Cfb.aesDecryptFinalApi) (ks := 0) (n := fun _ => 0) (a := Impl.StackScratch.X86_64.withStackArgScratch 64 0 (Impl.AesCfb.X86_64.decryptFinal ⟨"", .block []⟩ ""))
    { suffix := v.suffix
      code := Impl.StackScratch.X86_64.withStackArgScratch 64 0 (Impl.AesCfb.X86_64.decryptFinal v.enc v.suffix)
      stack := 80
      verified := Proof.AesCfb.decryptFinal_keyed (Proof.AesCfb.X86_64.decryptFinal_framed v)
      spSafe := Proof.AesCfb.X86_64.decryptFinal_framed_spSafe v }
    v.level (cfbDecryptFinalOut _) (by have := v.encSide; fill_calls) (Nat.zero_le _) (Nat.le_refl _)

theorem cfbDecryptFinal_spSafeFn (v : BlocksImpl) :
    (Impl.AesCfb.X86_64.Fn.cfbDecryptFinal v.level v.enc v.suffix).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.AesCfb.X86_64.decryptFinal_framed_spSafe v)

/-- `Spec.Ofb.aesFinalApi`'s function as emitted over `v` (`Impl.AesOfb.X86_64.Fn.ofbFinal`) meets its
contract in constant time and returns without secret residue: its code is
its code over a stub, with `v`'s where it calls it (`Fill`). -/
theorem ofbFinal_scrubbed (v : BlocksImpl) :
    VerifiedScrubbed target (Impl.AesOfb.X86_64.Fn.ofbFinal v.level v.enc v.suffix)
      (Spec.Ofb.aesFinalApi.contract X86_64.abi 80) 0 :=
  verifiedScrubbedAllFill (api := Spec.Ofb.aesFinalApi) (ks := 0) (n := fun _ => 0) (a := Impl.StackScratch.X86_64.withStackArgScratch 64 0 (Impl.AesOfb.X86_64.cryptFinal ⟨"", .block []⟩ ""))
    { suffix := v.suffix
      code := Impl.StackScratch.X86_64.withStackArgScratch 64 0 (Impl.AesOfb.X86_64.cryptFinal v.enc v.suffix)
      stack := 80
      verified := Proof.AesOfb.final_keyed (Proof.AesOfb.X86_64.cryptFinal_framed v)
      spSafe := Proof.AesOfb.X86_64.cryptFinal_framed_spSafe v }
    v.level (ofbFinalOut _) (by have := v.encSide; fill_calls) (Nat.zero_le _) (Nat.le_refl _)

theorem ofbFinal_spSafeFn (v : BlocksImpl) :
    (Impl.AesOfb.X86_64.Fn.ofbFinal v.level v.enc v.suffix).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.AesOfb.X86_64.cryptFinal_framed_spSafe v)

end VG.Proof.Aes.X86_64.FinalScrub
