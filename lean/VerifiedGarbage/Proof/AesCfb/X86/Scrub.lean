module

public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesCfb.X86.Verified
public import VerifiedGarbage.Proof.AesCfb.X86.Final
public import VerifiedGarbage.Spec.Cfb.Contract
public import VerifiedGarbage.Spec.Cfb.Final
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.AesCfb.X86.Verified
meta import VerifiedGarbage.Proof.AesCfb.X86.Final
meta import VerifiedGarbage.Spec.Cfb.Contract
meta import VerifiedGarbage.Spec.Cfb.Final
meta import VerifiedGarbage.Proof.Aes.ScrubLocal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# AES-CFB128 on x86 (32-bit), without secret residue

`vg_aes_cfb128_encrypt`, `vg_aes_cfb128_decrypt` and their `_final` forms
read the memory on return only within the data and the IV (`encryptOut`,
`decryptOut`, `encryptFinalOut`, `decryptFinalOut`), as on PPC64LE
(`Proof/Aes/PPC64LE/Scrub.lean`): what the scrub of their frames and calls
needs (`X86.Scrub.PostOut`).

Each is registered with `X86.Scrub.scrubFOf`, which zeroes the stack of its
contract below `esp` and clears the registers. What that needs of the code
(`scrubFSide`) holds whatever the implementation of the block function
(`encrypt_scrub`, …): from CFB's code with a stub block function, whose
code is `.block []`, which the kernel evaluates once (`encrypt_side`, …),
the implementation's own facts (`BlocksImpl.encScrub`, its stack), and
`Fill`, which `fill_calls` proves by walking only CFB's code. The `_final`
forms call the whole-segment code as `vg_aes_cfb128_encrypt_core` and
`vg_aes_cfb128_decrypt_core` (`Impl.AesCfb.X86.encryptFinal`), unscrubbed.
-/

@[expose] public section

namespace VG.Proof.AesCfb.X86.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.Aes.ScrubLocal

/-- A count of elements of `k` bytes, which the contract reads as its low 32
bits, spans at most the bytes of the buffer `Sig.bufs` gives it. -/
private theorem len_le (x : BitVec 64) (k : Nat) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat * k ≤ x.toNat * k := by
  show (x.setWidth 32).toNat * k ≤ x.toNat * k
  rw [BitVec.toNat_setWidth]
  exact Nat.mul_le_mul_right _ (Nat.mod_le _ _)

private theorem len_le1 (x : BitVec 64) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat ≤ x.toNat * Elem.u8.size := by
  have := len_le x 1
  rwa [Nat.mul_one] at this

theorem encryptOut (stack : Nat) :
    PostOut (Spec.Cfb.aesEncryptContract abi stack) (Spec.Cfb.aesSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Cfb.aesSig, Spec.Cbc.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [blocksAt_of0 hb.2.2.1 (len_le ln 16), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem decryptOut (stack : Nat) :
    PostOut (Spec.Cfb.aesDecryptContract abi stack) (Spec.Cfb.aesSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Cfb.aesSig, Spec.Cbc.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [blocksAt_of0 hb.2.2.1 (len_le ln 16), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem encryptFinalOut (stack : Nat) :
    PostOut (Spec.Cfb.aesEncryptFinalContract abi stack) (Spec.Cfb.aesFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Cfb.aesFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2.1 (len_le1 ln), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem decryptFinalOut (stack : Nat) :
    PostOut (Spec.Cfb.aesDecryptFinalContract abi stack) (Spec.Cfb.aesFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Cfb.aesFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2.1 (len_le1 ln), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

/-! ## What the scrub needs of the code -/

open Impl.StackScratch.X86 (withStackScratchWiped)
open Proof.Aes.X86 (BlocksImpl)

/-- A block function with no code. -/
def stubBlocks : Impl.Aes.X86.Blocks := ⟨"", .block []⟩

-- CFB's own code, with the stub, as literals for the kernel's evaluation.
materialize_code encryptStub := Impl.AesCfb.X86.encrypt stubBlocks
materialize_code decryptStub := Impl.AesCfb.X86.decrypt stubBlocks
materialize_code encryptFinalStub := withStackScratchWiped 48 6 4 (Impl.AesCfb.X86.encryptFinal stubBlocks "")
materialize_code decryptFinalStub := withStackScratchWiped 48 6 4 (Impl.AesCfb.X86.decryptFinal stubBlocks "")

theorem encrypt_side : scrubFSide (Impl.AesCfb.X86.encrypt stubBlocks) [] 24 = true := by
  lit_decide

theorem decrypt_side : scrubFSide (Impl.AesCfb.X86.decrypt stubBlocks) [] 24 = true := by
  lit_decide

theorem encryptFinal_side :
    scrubFSide (withStackScratchWiped 48 6 4 (Impl.AesCfb.X86.encryptFinal stubBlocks "")) [] 100 = true := by
  lit_decide

theorem decryptFinal_side :
    scrubFSide (withStackScratchWiped 48 6 4 (Impl.AesCfb.X86.decryptFinal stubBlocks "")) [] 100 = true := by
  lit_decide

theorem encrypt_fill (b : Impl.Aes.X86.Blocks) (hb : calleeSide b.code 0 = true) :
    Fill 0 (Impl.AesCfb.X86.encrypt stubBlocks) (Impl.AesCfb.X86.encrypt b) := by
  fill_calls

theorem decrypt_fill (b : Impl.Aes.X86.Blocks) (hb : calleeSide b.code 0 = true) :
    Fill 0 (Impl.AesCfb.X86.decrypt stubBlocks) (Impl.AesCfb.X86.decrypt b) := by
  fill_calls

theorem encryptFinal_fill (b : Impl.Aes.X86.Blocks) (sfx : String) (hb : calleeSide b.code 0 = true) :
    Fill 0 (withStackScratchWiped 48 6 4 (Impl.AesCfb.X86.encryptFinal stubBlocks ""))
      (withStackScratchWiped 48 6 4 (Impl.AesCfb.X86.encryptFinal b sfx)) := by
  fill_calls

theorem decryptFinal_fill (b : Impl.Aes.X86.Blocks) (sfx : String) (hb : calleeSide b.code 0 = true) :
    Fill 0 (withStackScratchWiped 48 6 4 (Impl.AesCfb.X86.decryptFinal stubBlocks ""))
      (withStackScratchWiped 48 6 4 (Impl.AesCfb.X86.decryptFinal b sfx)) := by
  fill_calls

/-- `scrubFSide` of `vg_aes_cfb128_encrypt`, whatever the implementation. -/
theorem encrypt_scrub (v : BlocksImpl) : scrubFSide (Impl.AesCfb.X86.encrypt v.enc) [] 24 = true :=
  scrubFSide_of_fill (encrypt_fill _ (calleeSide_of_eq v.encStack v.encScrub)) encrypt_side

/-- `scrubFSide` of `vg_aes_cfb128_decrypt`, whatever the implementation. -/
theorem decrypt_scrub (v : BlocksImpl) : scrubFSide (Impl.AesCfb.X86.decrypt v.enc) [] 24 = true :=
  scrubFSide_of_fill (decrypt_fill _ (calleeSide_of_eq v.encStack v.encScrub)) decrypt_side

/-- `scrubFSide` of `vg_aes_cfb128_encrypt_final`, whatever the implementation. -/
theorem encryptFinal_scrub (v : BlocksImpl) :
    scrubFSide (withStackScratchWiped 48 6 4 (Impl.AesCfb.X86.encryptFinal v.enc v.suffix)) [] 100 = true :=
  scrubFSide_of_fill (encryptFinal_fill _ _ (calleeSide_of_eq v.encStack v.encScrub)) encryptFinal_side

/-- `scrubFSide` of `vg_aes_cfb128_decrypt_final`, whatever the implementation. -/
theorem decryptFinal_scrub (v : BlocksImpl) :
    scrubFSide (withStackScratchWiped 48 6 4 (Impl.AesCfb.X86.decryptFinal v.enc v.suffix)) [] 100 = true :=
  scrubFSide_of_fill (decryptFinal_fill _ _ (calleeSide_of_eq v.encStack v.encScrub)) decryptFinal_side

/-! ## The registrations -/

/-- `vg_aes_cfb128_encrypt` over `v`, without secret residue. -/
def encryptReg (v : BlocksImpl) : Registration Spec.Cfb.aesEncryptApi target :=
  scrubFOf {
      suffix := v.suffix
      code := Impl.AesCfb.X86.encrypt v.enc
      verified := Proof.AesCfb.encrypt_keyed (encrypt_verified v)
      spSafe := encrypt_spSafe v }
    (encryptOut _) (W := 24) (hs := encrypt_scrub v)

/-- `vg_aes_cfb128_decrypt` over `v`, without secret residue. -/
def decryptReg (v : BlocksImpl) : Registration Spec.Cfb.aesDecryptApi target :=
  scrubFOf {
      suffix := v.suffix
      code := Impl.AesCfb.X86.decrypt v.enc
      verified := Proof.AesCfb.decrypt_keyed (decrypt_verified v)
      spSafe := decrypt_spSafe v }
    (decryptOut _) (W := 24) (hs := decrypt_scrub v)

/-- `vg_aes_cfb128_encrypt_final` over `v`, without secret residue. -/
def encryptFinalReg (v : BlocksImpl) : Registration Spec.Cfb.aesEncryptFinalApi target :=
  scrubFOf {
      suffix := v.suffix
      code := withStackScratchWiped 48 6 4 (Impl.AesCfb.X86.encryptFinal v.enc v.suffix)
      verified := Proof.AesCfb.encryptFinal_keyed (encryptFinal_framed v)
      spSafe := encryptFinal_framed_spSafe v }
    (encryptFinalOut _) (W := 100) (hs := encryptFinal_scrub v)

/-- `vg_aes_cfb128_decrypt_final` over `v`, without secret residue. -/
def decryptFinalReg (v : BlocksImpl) : Registration Spec.Cfb.aesDecryptFinalApi target :=
  scrubFOf {
      suffix := v.suffix
      code := withStackScratchWiped 48 6 4 (Impl.AesCfb.X86.decryptFinal v.enc v.suffix)
      verified := Proof.AesCfb.decryptFinal_keyed (decryptFinal_framed v)
      spSafe := decryptFinal_framed_spSafe v }
    (decryptFinalOut _) (W := 100) (hs := decryptFinal_scrub v)

end VG.Proof.AesCfb.X86.Scrub
