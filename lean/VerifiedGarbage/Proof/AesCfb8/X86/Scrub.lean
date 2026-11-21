module

public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesCfb8.X86.Verified
public import VerifiedGarbage.Spec.Cfb8.Contract
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Impl.AesCfb8.X86
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.AesCfb8.X86.Verified
meta import VerifiedGarbage.Spec.Cfb8.Contract
meta import VerifiedGarbage.Proof.Aes.ScrubLocal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Impl.AesCfb8.X86

/-!
# AES-CFB8 on x86 (32-bit), without secret residue

`vg_aes_cfb8_encrypt` and `vg_aes_cfb8_decrypt` read the memory on return
only within the data and the IV (`encryptOut`, `decryptOut`), as on PPC64LE
(`Proof/Aes/PPC64LE/Scrub.lean`): what the scrub of their frames and calls
needs (`X86.Scrub.PostOut`).

Each as emitted (`Impl.AesCfb8.X86.Fn`) zeroes its 24 bytes of stack below
`esp` and clears the registers, and returns without secret residue
(`X86.Scrub.verifiedScrubbedAll`: `encrypt_scrubbed`, `decrypt_scrubbed`).
What that needs of the code (`scrubFSide`) holds whatever the implementation
of the block function (`encrypt_scrub`, `decrypt_scrub`): from CFB8's code
with a stub block function, whose code is `.block []`, which the kernel
evaluates once (`encrypt_side`, `decrypt_side`), the implementation's own
facts (`BlocksImpl.encScrub`, its stack), and `Fill`, which `fill_calls`
proves by walking only CFB8's code.
-/

@[expose] public section

namespace VG.Proof.AesCfb8.X86.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.Aes.ScrubLocal

/-- A length argument, which the contract reads as its low 32 bits, is at
most the bytes of the buffer `Sig.bufs` gives it. -/
private theorem len_le1 (x : BitVec 64) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat ≤ x.toNat * Elem.u8.size := by
  show (x.setWidth 32).toNat ≤ x.toNat * 1
  rw [BitVec.toNat_setWidth, Nat.mul_one]
  exact Nat.mod_le _ _

theorem encryptOut (stack : Nat) :
    PostOut (Spec.Cfb8.aesEncryptContract abi stack) (Spec.Cfb8.aesSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Cfb8.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2.1 (len_le1 ln), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem decryptOut (stack : Nat) :
    PostOut (Spec.Cfb8.aesDecryptContract abi stack) (Spec.Cfb8.aesSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Cfb8.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2.1 (len_le1 ln), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

/-! ## What the scrub needs of the code -/

open Proof.Aes.X86 (BlocksImpl)

/-- A block function with no code. -/
def stubBlocks : Impl.Aes.X86.Blocks := ⟨"", .block []⟩

-- CFB8's own code, with the stub, as literals for the kernel's evaluation.
materialize_code encryptStub := Impl.AesCfb8.X86.encrypt stubBlocks
materialize_code decryptStub := Impl.AesCfb8.X86.decrypt stubBlocks

theorem encrypt_side : scrubFSide (Impl.AesCfb8.X86.encrypt stubBlocks) [] 24 = true := by
  lit_decide

theorem decrypt_side : scrubFSide (Impl.AesCfb8.X86.decrypt stubBlocks) [] 24 = true := by
  lit_decide

theorem encrypt_fill (b : Impl.Aes.X86.Blocks) (hb : calleeSide b.code 0 = true) :
    Fill 0 (Impl.AesCfb8.X86.encrypt stubBlocks) (Impl.AesCfb8.X86.encrypt b) := by
  fill_calls

theorem decrypt_fill (b : Impl.Aes.X86.Blocks) (hb : calleeSide b.code 0 = true) :
    Fill 0 (Impl.AesCfb8.X86.decrypt stubBlocks) (Impl.AesCfb8.X86.decrypt b) := by
  fill_calls

/-- `scrubFSide` of `vg_aes_cfb8_encrypt`, whatever the implementation. -/
theorem encrypt_scrub (v : BlocksImpl) : scrubFSide (Impl.AesCfb8.X86.encrypt v.enc) [] 24 = true :=
  scrubFSide_of_fill (encrypt_fill _ (calleeSide_of_eq v.encStack v.encScrub)) encrypt_side

/-- `scrubFSide` of `vg_aes_cfb8_decrypt`, whatever the implementation. -/
theorem decrypt_scrub (v : BlocksImpl) : scrubFSide (Impl.AesCfb8.X86.decrypt v.enc) [] 24 = true :=
  scrubFSide_of_fill (decrypt_fill _ (calleeSide_of_eq v.encStack v.encScrub)) decrypt_side

/-! ## The functions as emitted -/

/-- `vg_aes_cfb8_encrypt` over `v` as emitted (`Impl.AesCfb8.X86.Fn.encrypt`)
meets its contract in constant time and returns without secret residue. -/
theorem encrypt_scrubbed (v : BlocksImpl) :
    VerifiedScrubbed X86.target (Impl.AesCfb8.X86.Fn.encrypt v.enc)
      (Spec.Cfb8.aesEncryptContract X86.abi 24) 0 :=
  verifiedScrubbedAll (api := Spec.Cfb8.aesEncryptApi) {
      suffix := v.suffix
      code := Impl.AesCfb8.X86.encrypt v.enc
      verified := Proof.AesCfb8.encrypt_keyed (encrypt_verified v)
      spSafe := encrypt_spSafe v }
    (encryptOut _) (W := 24) (hs := encrypt_scrub v)

/-- `vg_aes_cfb8_decrypt` over `v` as emitted (`Impl.AesCfb8.X86.Fn.decrypt`)
meets its contract in constant time and returns without secret residue. -/
theorem decrypt_scrubbed (v : BlocksImpl) :
    VerifiedScrubbed X86.target (Impl.AesCfb8.X86.Fn.decrypt v.enc)
      (Spec.Cfb8.aesDecryptContract X86.abi 24) 0 :=
  verifiedScrubbedAll (api := Spec.Cfb8.aesDecryptApi) {
      suffix := v.suffix
      code := Impl.AesCfb8.X86.decrypt v.enc
      verified := Proof.AesCfb8.decrypt_keyed (decrypt_verified v)
      spSafe := decrypt_spSafe v }
    (decryptOut _) (W := 24) (hs := decrypt_scrub v)

/-- `Impl.AesCfb8.X86.Fn.encrypt` writes `esp` only in its frames and calls. -/
theorem encrypt_fnSpSafe (v : BlocksImpl) :
    (Impl.AesCfb8.X86.Fn.encrypt v.enc).all (fun i => !X86.isa.writesSp i) = true :=
  scrubAll_spSafe (encrypt_spSafe v)

/-- `Impl.AesCfb8.X86.Fn.decrypt` writes `esp` only in its frames and calls. -/
theorem decrypt_fnSpSafe (v : BlocksImpl) :
    (Impl.AesCfb8.X86.Fn.decrypt v.enc).all (fun i => !X86.isa.writesSp i) = true :=
  scrubAll_spSafe (decrypt_spSafe v)

end VG.Proof.AesCfb8.X86.Scrub
