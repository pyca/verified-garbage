module

public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesXts.X86.Unit.Verified
public import VerifiedGarbage.Spec.Xts.Contract
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

/-!
# XTS-AES on x86 (32-bit), without secret residue

`vg_aes_xts_encrypt_unit` and `vg_aes_xts_decrypt_unit` read the memory on
return only within the data unit (`encryptUnitOut`, `decryptUnitOut`), as on
PPC64LE (`Proof/AesXts/PPC64LE/Scrub.lean`): what the scrub of their frames
and calls needs (`X86.Scrub.PostOut`).

Each is registered with `X86.Scrub.scrubFOf` (`encryptUnitReg`,
`decryptUnitReg`), which zeroes the stack of its contract below `esp` and
clears the registers. What that needs of the code (`scrubFSide`) holds
whatever the implementation of the block functions (`encrypt_scrub`,
`decrypt_scrub`): from XTS's code with stub block functions, whose code is
`.block []`, which the kernel evaluates once (`encrypt_side`,
`decrypt_side`), the implementation's own facts (`BlocksImpl.encScrub`,
`decScrub`, their stacks), and `Fill`, which `fill_calls` proves by walking
only XTS's code.
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

open Proof.Aes.X86 (BlocksImpl)

/-- A block function with no code. -/
def stubBlocks : Impl.Aes.X86.Blocks := ⟨"", .block []⟩

/-- `vg_aes_xts_encrypt` over `b`, by the name `sfx` ends. -/
abbrev xE (b : Impl.Aes.X86.Blocks) (sfx : String) : Impl.Aes.X86.Blocks :=
  ⟨"vg_aes_xts_encrypt" ++ sfx, Impl.AesXts.X86.encrypt b⟩

/-- `vg_aes_xts_decrypt` over `b`, by the name `sfx` ends. -/
abbrev xD (b : Impl.Aes.X86.Blocks) (sfx : String) : Impl.Aes.X86.Blocks :=
  ⟨"vg_aes_xts_decrypt" ++ sfx, Impl.AesXts.X86.decrypt b⟩

-- XTS's own code, with the stubs, as literals for the kernel's evaluation.
materialize_code encryptStub := Impl.AesXts.X86Unit.encrypt (xE stubBlocks "")
materialize_code decryptStub := Impl.AesXts.X86Unit.decrypt (xE stubBlocks "") (xD stubBlocks "")

theorem encrypt_side : scrubFSide (Impl.AesXts.X86Unit.encrypt (xE stubBlocks "")) [] 52 = true := by
  lit_decide

theorem decrypt_side :
    scrubFSide (Impl.AesXts.X86Unit.decrypt (xE stubBlocks "") (xD stubBlocks "")) [] 52 = true := by
  lit_decide

theorem encrypt_fill (e : Impl.Aes.X86.Blocks) (sfx : String) (he : calleeSide e.code 0 = true) :
    Fill 0 (Impl.AesXts.X86Unit.encrypt (xE stubBlocks "")) (Impl.AesXts.X86Unit.encrypt (xE e sfx)) := by
  fill_calls

theorem decrypt_fill (e d : Impl.Aes.X86.Blocks) (sfx : String) (he : calleeSide e.code 0 = true)
    (hd : calleeSide d.code 0 = true) :
    Fill 0 (Impl.AesXts.X86Unit.decrypt (xE stubBlocks "") (xD stubBlocks ""))
      (Impl.AesXts.X86Unit.decrypt (xE e sfx) (xD d sfx)) := by
  fill_calls

/-- `scrubFSide` of `vg_aes_xts_encrypt_unit`, whatever the implementation. -/
theorem encrypt_scrub (v : BlocksImpl) :
    scrubFSide (Impl.AesXts.X86Unit.encrypt (Unit.xtsE v)) [] 52 = true :=
  scrubFSide_of_fill (encrypt_fill _ _ (calleeSide_of_eq v.encStack v.encScrub)) encrypt_side

/-- `scrubFSide` of `vg_aes_xts_decrypt_unit`, whatever the implementation. -/
theorem decrypt_scrub (v : BlocksImpl) :
    scrubFSide (Impl.AesXts.X86Unit.decrypt (Unit.xtsE v) (Unit.xtsD v)) [] 52 = true :=
  scrubFSide_of_fill (decrypt_fill _ _ _ (calleeSide_of_eq v.encStack v.encScrub)
    (calleeSide_of_eq v.decStack v.decScrub)) decrypt_side

/-! ## The registrations -/

/-- `vg_aes_xts_encrypt_unit` over `v`, without secret residue. -/
def encryptUnitReg (v : BlocksImpl) : Registration Spec.Xts.aesEncryptUnitApi target :=
  scrubFOf {
      suffix := v.suffix
      code := Impl.AesXts.X86Unit.encrypt (Unit.xtsE v)
      verified := Unit.encrypt_verified v
      spSafe := Unit.encrypt_spSafe v }
    (encryptUnitOut _) (W := 52) (hs := encrypt_scrub v)

/-- `vg_aes_xts_decrypt_unit` over `v`, without secret residue. -/
def decryptUnitReg (v : BlocksImpl) : Registration Spec.Xts.aesDecryptUnitApi target :=
  scrubFOf {
      suffix := v.suffix
      code := Impl.AesXts.X86Unit.decrypt (Unit.xtsE v) (Unit.xtsD v)
      verified := Unit.decrypt_verified v
      spSafe := Unit.decrypt_spSafe v }
    (decryptUnitOut _) (W := 52) (hs := decrypt_scrub v)

end VG.Proof.AesXts.X86.Scrub
