module

public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesXts.X86.Unit.Verified
public import VerifiedGarbage.Spec.Xts.Contract
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Impl.AesXts.X86Unit
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.AesXts.X86.Unit.Verified
meta import VerifiedGarbage.Spec.Xts.Contract
meta import VerifiedGarbage.Proof.Aes.ScrubLocal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Impl.AesXts.X86Unit

/-!
# XTS-AES on x86 (32-bit), without secret residue

`vg_aes_xts_encrypt_unit` and `vg_aes_xts_decrypt_unit` read the memory on
return only within the data unit (`encryptUnitOut`, `decryptUnitOut`), as on
PPC64LE (`Proof/AesXts/PPC64LE/Scrub.lean`): what the scrub of their frames
and calls needs (`X86.Scrub.PostOut`).

Each as emitted (`Impl.AesXts.X86Unit.Fn`) zeroes the stack of its
contract below `esp` and clears the registers, and returns without secret
residue (`X86.Scrub.verifiedScrubbedAll`: `encryptUnit_scrubbed`,
`decryptUnit_scrubbed`). What that needs of the code (`scrubFSide`) holds
whatever the implementation of the whole-block functions (`XtsImpl`;
`encrypt_scrub`, `decrypt_scrub`): from the code with stub whole-block
functions, whose code is `.block []`, which the kernel evaluates once over
the 28 bytes of a call's frame and return address (`encrypt_side`,
`decrypt_side`), the implementation's own facts (`XtsImpl.encScrub`,
`decScrub`, and their stacks, 24 bytes at most), and `Fill`, which
`fill_calls` proves by walking only the unit functions' code.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.Aes.ScrubLocal

/-- A length argument, which the contract reads as its low 32 bits, is at
most the bytes of the buffer `Sig.bufs` gives it. -/
private theorem len_le1 (x : BitVec 64) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat ≤ x.toNat * Elem.u8.size := by
  show (x.setWidth 32).toNat ≤ x.toNat * 1
  rw [BitVec.toNat_setWidth, Nat.mul_one]
  exact Nat.mod_le _ _

theorem encryptUnitOut (stack : Nat) :
    PostOut (Spec.Xts.aesEncryptUnitContract abi stack) (Spec.Xts.aesUnitSig.retBits 32) :=
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
    PostOut (Spec.Xts.aesDecryptUnitContract abi stack) (Spec.Xts.aesUnitSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, tsch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Xts.aesUnitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, Spec.Xts.KeySchedules m sch tsch _ key → _ = some (Spec.Aes.bytesAt m₂ dt _)
      intro key hk
      rw [bytesAt_of0 hb.2.2.2.1 (len_le1 ln)]
      exact h key hk

/-! ## What the scrub needs of the code -/

/-- A whole-block function with no code. -/
def stubXts : Impl.Aes.X86.Blocks := ⟨"", .block []⟩

-- The unit functions' own code, with the stubs, as literals for the kernel's evaluation.
materialize_code encryptStub := Impl.AesXts.X86Unit.encrypt stubXts
materialize_code decryptStub := Impl.AesXts.X86Unit.decrypt stubXts stubXts

theorem encrypt_side : scrubFSide (Impl.AesXts.X86Unit.encrypt stubXts) [] 28 = true := by
  lit_decide

theorem decrypt_side : scrubFSide (Impl.AesXts.X86Unit.decrypt stubXts stubXts) [] 28 = true := by
  lit_decide

theorem encrypt_fill (e : Impl.Aes.X86.Blocks) (he : calleeSide e.code 24 = true) :
    Fill 24 (Impl.AesXts.X86Unit.encrypt stubXts) (Impl.AesXts.X86Unit.encrypt e) := by
  fill_calls

theorem decrypt_fill (e d : Impl.Aes.X86.Blocks) (he : calleeSide e.code 24 = true)
    (hd : calleeSide d.code 24 = true) :
    Fill 24 (Impl.AesXts.X86Unit.decrypt stubXts stubXts) (Impl.AesXts.X86Unit.decrypt e d) := by
  fill_calls

/-- `scrubFSide` of `vg_aes_xts_encrypt_unit`, whatever the implementation. -/
theorem encrypt_scrub (v : XtsImpl) : scrubFSide (Impl.AesXts.X86Unit.encrypt v.enc) [] 52 = true :=
  scrubFSide_of_fill (encrypt_fill _ (calleeSide_of_le v.encStack v.encScrub)) encrypt_side

/-- `scrubFSide` of `vg_aes_xts_decrypt_unit`, whatever the implementation. -/
theorem decrypt_scrub (v : XtsImpl) : scrubFSide (Impl.AesXts.X86Unit.decrypt v.enc v.dec) [] 52 = true :=
  scrubFSide_of_fill (decrypt_fill _ _ (calleeSide_of_le v.encStack v.encScrub)
    (calleeSide_of_le v.decStack v.decScrub)) decrypt_side

/-! ## The functions as emitted -/

/-- `vg_aes_xts_encrypt_unit` over `v` as emitted (`Impl.AesXts.X86Unit.Fn.encrypt`)
meets its contract in constant time and returns without secret residue. -/
theorem encryptUnit_scrubbed (v : XtsImpl) :
    VerifiedScrubbed X86.target (Impl.AesXts.X86Unit.Fn.encrypt v.enc)
      (Spec.Xts.aesEncryptUnitContract X86.abi 52) 0 :=
  verifiedScrubbedAll (api := Spec.Xts.aesEncryptUnitApi) {
      suffix := v.suffix
      code := Impl.AesXts.X86Unit.encrypt v.enc
      verified := Unit.encrypt_verified v
      spSafe := Unit.encrypt_spSafe v }
    (encryptUnitOut _) (W := 52) (hs := encrypt_scrub v)

/-- `vg_aes_xts_decrypt_unit` over `v` as emitted (`Impl.AesXts.X86Unit.Fn.decrypt`)
meets its contract in constant time and returns without secret residue. -/
theorem decryptUnit_scrubbed (v : XtsImpl) :
    VerifiedScrubbed X86.target (Impl.AesXts.X86Unit.Fn.decrypt v.enc v.dec)
      (Spec.Xts.aesDecryptUnitContract X86.abi 52) 0 :=
  verifiedScrubbedAll (api := Spec.Xts.aesDecryptUnitApi) {
      suffix := v.suffix
      code := Impl.AesXts.X86Unit.decrypt v.enc v.dec
      verified := Unit.decrypt_verified v
      spSafe := Unit.decrypt_spSafe v }
    (decryptUnitOut _) (W := 52) (hs := decrypt_scrub v)

/-- `Impl.AesXts.X86Unit.Fn.encrypt` writes `esp` only in its frames and calls. -/
theorem encryptUnit_fnSpSafe (v : XtsImpl) :
    (Impl.AesXts.X86Unit.Fn.encrypt v.enc).all (fun i => !X86.isa.writesSp i) = true :=
  scrubAll_spSafe (Unit.encrypt_spSafe v)

/-- `Impl.AesXts.X86Unit.Fn.decrypt` writes `esp` only in its frames and calls. -/
theorem decryptUnit_fnSpSafe (v : XtsImpl) :
    (Impl.AesXts.X86Unit.Fn.decrypt v.enc v.dec).all
      (fun i => !X86.isa.writesSp i) = true :=
  scrubAll_spSafe (Unit.decrypt_spSafe v)

end VG.Proof.AesXts.X86.Scrub
