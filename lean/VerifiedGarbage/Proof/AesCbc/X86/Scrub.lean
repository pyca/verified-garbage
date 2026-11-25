module

public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesCbc.X86.Wiped
public import VerifiedGarbage.Spec.Cbc.Contract
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Impl.AesCbc.X86.Wiped
import VerifiedGarbage.Proof.AesCbc.X86.Decrypt
import VerifiedGarbage.Proof.Aes.X86.Chain
import VerifiedGarbage.Proof.AesEcb.Wipe
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.AesCbc.X86.Wiped
meta import VerifiedGarbage.Spec.Cbc.Contract
meta import VerifiedGarbage.Proof.AesEcb.Wipe
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Impl.AesCbc.X86.Wiped

/-!
# AES-CBC on x86 (32-bit), without secret residue

`vg_aes_cbc_encrypt` and `vg_aes_cbc_decrypt` read the memory on return only
within the IV, the data and `scratch` (`encryptOut`, `decryptOut`): what the
scrub of their frames and calls needs (`X86.Scrub.PostOut`).

Which code is emitted for an implementation `v` of the block functions
(`Impl.AesCbc.X86.Fn`), with its stack (`cbcStack`), as
`Proof/AesCbc/X86/Wiped.lean` chooses it: the CBC code (`encryptCode v`)
where it writes nothing in `scratch`, with its stack (24 bytes; in
decryption, `decStack`); otherwise the
call of it, then of `vg_zeroize` on the bytes of `scratch` it writes, with
48 more. Each zeroes that stack below `esp` and clears the registers, and returns
without secret residue (`X86.Scrub.verifiedScrubbedAll`), which
`encrypt_wipes` and `decrypt_wipes` prove by cases, of the contract that says
which bytes of `scratch` are zero (`encZeroed`, `decZeroed`): it implies the
specification's (`encrypt_scrubbed`, `decrypt_scrubbed`), and that which bytes
those are is public (`encrypt_public`, `decrypt_public`). What that
needs of the code (`scrubFSide`) holds whatever the implementation: the CBC
code around a chain (`Chain.of`) and AES-NI's decryption (`hardware`) are
closed terms, which the kernel evaluates (`ni_side`, `ssse3_callee`,
`dec_callee`); for any other, the CBC code around a stub block
function, whose code is `.block []` (`encZ_side`, `decZ_side`), and the
call with a stub (`wipedStub`), whose callee and the instructions that pass
`vg_zeroize` its length (`zeroArgs`) are `.block []`, which the kernel
evaluates once, the implementation's own facts (`BlocksImpl.encScrub`,
`decScrub`, their stacks), and `Fill`, which `fill_calls` proves by walking
only CBC's code.
-/

@[expose] public section

namespace VG.Proof.AesCbc.X86.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.AesCbc.Wipe VG.Proof.AesCbc.X86.Wiped
open Proof.Aes.X86 (BlocksImpl)
open Impl.Aes.X86 (Chain)
open Impl.CallWipe.X86 (frameSize copyArgs zeroArgs restoreRet)

/-! ## Postconditions -/

/-- The postcondition of `vg_aes_cbc_encrypt` reads the memory on return only
within the buffers. -/
theorem encryptOut (S : Nat → Bool) (stack : Nat) :
    PostOut (wipedContract encPost S abi stack) (Spec.Cbc.aesSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (wipedPost_ret _ _ S (encPost_ret _))

/-- The postcondition of `vg_aes_cbc_decrypt` reads the memory on return only
within the buffers. -/
theorem decryptOut (S : Nat → Bool) (stack : Nat) :
    PostOut (wipedContract decPost S abi stack) (Spec.Cbc.aesSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (wipedPost_ret _ _ S (decPost_ret _))

/-! ## What the scrub needs of the code -/

/-- A block function with no code. -/
def stubBlocks : Impl.Aes.X86.Blocks := ⟨"", .block []⟩

/-- `Impl.AesCbc.X86.Wiped.wiped _ body n` with no name, and `.block []`
where it passes `vg_zeroize` its length `n`. -/
def wipedStub (body : Prog isa) : Prog isa :=
  .frame (.alloc (frameSize 6))
    (.seq (.block (copyArgs (frameSize 6) 6))
      (.seq (.call "" body)
        (.seq (.block [])
          (.seq (.call "vg_zeroize" Impl.Zeroize.X86.zeroize) (.block (restoreRet 6))))))
    (.free (frameSize 6))

-- CBC's own code, with the stubs, as literals for the kernel's evaluation.
materialize_code decryptNiLit := Impl.AesCbc.X86.Decrypt.decrypt
materialize_code encZStub := Impl.AesCbc.X86.encryptZ stubBlocks
materialize_code decZStub := Impl.AesCbc.X86.Groups.framed stubBlocks true
materialize_code encWStub := wipedStub (Impl.AesCbc.X86.encryptZ stubBlocks)
materialize_code decWStub := wipedStub (Impl.AesCbc.X86.Groups.framed stubBlocks true)
materialize_code holeWStub := wipedStub (.block [])

theorem ni_side : scrubFSide (Impl.AesCbc.X86.encryptChain Chain.aesNi) [] 24 = true := by
  lit_decide

theorem ssse3_callee : calleeSide (Impl.AesCbc.X86.encryptChain Chain.ssse3) 24 = true := by
  lit_decide

theorem dec_callee : calleeSide Impl.AesCbc.X86.Decrypt.decrypt 24 = true := by
  lit_decide

theorem encZ_side : scrubFSide (Impl.AesCbc.X86.encryptZ stubBlocks) [] 24 = true := by
  lit_decide

theorem decZ_side : scrubFSide (Impl.AesCbc.X86.Groups.framed stubBlocks true) [] 1108 = true := by
  lit_decide

theorem encW_side : scrubFSide (wipedStub (Impl.AesCbc.X86.encryptZ stubBlocks)) [] 72 = true := by
  lit_decide

theorem decW_side : scrubFSide (wipedStub (Impl.AesCbc.X86.Groups.framed stubBlocks true)) [] 1156 = true := by
  lit_decide

theorem holeW_side : scrubFSide (wipedStub (.block [])) [] 48 = true := by
  lit_decide

/-- The instructions that pass `vg_zeroize` its length, whatever it is. -/
theorem zeroArgs_side (n k : Nat) : calleeSide (.block (zeroArgs 6 5 n)) k = true := rfl

theorem encZ_fill (b : Impl.Aes.X86.Blocks) (hb : calleeSide b.code 0 = true) :
    Fill 0 (Impl.AesCbc.X86.encryptZ stubBlocks) (Impl.AesCbc.X86.encryptZ b) := by
  fill_calls

theorem decZ_fill (b : Impl.Aes.X86.Blocks) (hb : calleeSide b.code 0 = true) :
    Fill 0 (Impl.AesCbc.X86.Groups.framed stubBlocks true) (Impl.AesCbc.X86.Groups.framed b true) := by
  fill_calls

theorem encW_fill (b : Impl.Aes.X86.Blocks) (sfx : String) (n : Nat) (hb : calleeSide b.code 0 = true)
    (hz : calleeSide (.block (zeroArgs 6 5 n)) 0 = true) :
    Fill 0 (wipedStub (Impl.AesCbc.X86.encryptZ stubBlocks))
      (Impl.AesCbc.X86.Wiped.encrypt (Impl.AesCbc.X86.encryptZ b) sfx n) := by
  fill_calls

theorem decW_fill (b : Impl.Aes.X86.Blocks) (sfx : String) (n : Nat) (hb : calleeSide b.code 0 = true)
    (hz : calleeSide (.block (zeroArgs 6 5 n)) 0 = true) :
    Fill 0 (wipedStub (Impl.AesCbc.X86.Groups.framed stubBlocks true))
      (Impl.AesCbc.X86.Wiped.decrypt (Impl.AesCbc.X86.Groups.framed b true) sfx n) := by
  fill_calls

theorem holeW_fill (body : Prog isa) (sfx : String) (n : Nat) (hb : calleeSide body 24 = true)
    (hz : calleeSide (.block (zeroArgs 6 5 n)) 24 = true) :
    Fill 24 (wipedStub (.block [])) (Impl.AesCbc.X86.Wiped.decrypt body sfx n) := by
  fill_calls

theorem encHoleW_fill (body : Prog isa) (sfx : String) (n : Nat) (hb : calleeSide body 24 = true)
    (hz : calleeSide (.block (zeroArgs 6 5 n)) 24 = true) :
    Fill 24 (wipedStub (.block [])) (Impl.AesCbc.X86.Wiped.encrypt body sfx n) := by
  fill_calls

/-- `scrubFSide` of the CBC encryption code, where it writes nothing in
`scratch` (with a chain, AES-NI's). -/
theorem encFree_scrub (v : BlocksImpl) (h : encWritten v = 0) : scrubFSide (encryptCode v) [] 24 = true := by
  cases hc : Chain.of v.enc.name with
  | some c =>
    rw [encWritten_some hc] at h
    rw [encryptCode_some hc]
    rcases Proof.Aes.X86.Chain.of_cases hc with rfl | rfl
    · exact ni_side
    · exact absurd h (by decide)
  | none =>
    rw [encryptCode_none hc]
    exact scrubFSide_of_fill (encZ_fill _ (calleeSide_of_eq v.encStack v.encScrub)) encZ_side

/-- `scrubFSide` of the call of the CBC encryption code, then of
`vg_zeroize`, where it writes in `scratch`. -/
theorem encWiped_scrub (v : BlocksImpl) (h : ¬encWritten v = 0) :
    scrubFSide (Impl.AesCbc.X86.Wiped.encrypt (encryptCode v) v.suffix (encWritten v)) [] 72 = true := by
  cases hc : Chain.of v.enc.name with
  | some c =>
    have hd : calleeSide (encryptCode v) 24 = true := by
      rw [encWritten_some hc] at h
      rw [encryptCode_some hc]
      rcases Proof.Aes.X86.Chain.of_cases hc with rfl | rfl
      · exact absurd rfl h
      · exact ssse3_callee
    exact scrubFSide_of_fill (encHoleW_fill _ _ _ hd (zeroArgs_side _ _)) holeW_side
  | none =>
    rw [encryptCode_none hc]
    exact scrubFSide_of_fill (encW_fill _ _ _ (calleeSide_of_eq v.encStack v.encScrub) (zeroArgs_side _ _))
      encW_side

/-- `scrubFSide` of the CBC decryption code, where it writes nothing in
`scratch` (never with AES-NI). -/
theorem decFree_scrub (v : BlocksImpl) (h : decWritten v = 0) :
    scrubFSide (decryptCode v) [] (decStack v) = true := by
  have hw : ¬hardware v = true := fun hw => by rw [decWritten, ite_eq_left hw] at h; exact absurd h (by decide)
  rw [decryptCode, decStack, ite_eq_right hw, ite_eq_right hw]
  exact scrubFSide_of_fill (decZ_fill _ (calleeSide_of_eq v.decStack v.decScrub)) decZ_side

/-- `scrubFSide` of the call of the CBC decryption code, then of
`vg_zeroize`. -/
theorem decWiped_scrub (v : BlocksImpl) :
    scrubFSide (Impl.AesCbc.X86.Wiped.decrypt (decryptCode v) v.suffix (decWritten v)) [] (decStack v + 48) = true := by
  by_cases hw : hardware v = true
  · have hd : calleeSide (decryptCode v) 24 = true := by rw [decryptCode, ite_eq_left hw]; exact dec_callee
    rw [decStack, ite_eq_left hw]
    exact scrubFSide_of_fill (holeW_fill _ _ _ hd (zeroArgs_side _ _)) holeW_side
  · rw [decryptCode, decStack, ite_eq_right hw, ite_eq_right hw]
    exact scrubFSide_of_fill (decW_fill _ _ _ (calleeSide_of_eq v.decStack v.decScrub) (zeroArgs_side _ _))
      decW_side

/-! ## The functions as emitted -/

/-- The stack of `vg_aes_cbc_encrypt` and `vg_aes_cbc_decrypt` whose CBC
code writes the first `w` bytes of `scratch` and uses `k` bytes of stack:
`k` where the code is the CBC code itself, 48 more for the call wiping
`scratch` (`Impl.AesCbc.X86.Fn`). -/
def cbcStack (w k : Nat) : Nat := if w = 0 then k else k + 48

/-- `vg_aes_cbc_encrypt` over `v` as emitted (`Impl.AesCbc.X86.Fn.encrypt`)
meets its contract in constant time and returns without secret residue. -/
theorem encrypt_wipes (v : BlocksImpl) :
    VerifiedScrubbed X86.target (Impl.AesCbc.X86.Fn.encrypt (encryptCode v) v.suffix (encWritten v))
      (wipedContract encPost (encZeroed v) X86.abi (cbcStack (encWritten v) 24)) 0 := by
  unfold Impl.AesCbc.X86.Fn.encrypt cbcStack
  by_cases h : encWritten v = 0
  · rw [ite_eq_left h, ite_eq_left h]
    exact verifiedScrubbedAll (api := wipedApi encPost (encZeroed v)) {
        suffix := v.suffix
        code := encryptCode v
        stack := 24
        verified := encrypt_free v h
        spSafe := encryptCode_spSafe v }
      (encryptOut _ _) (W := 24) (hs := encFree_scrub v h)
  · rw [ite_eq_right h, ite_eq_right h]
    exact verifiedScrubbedAll (api := wipedApi encPost (encZeroed v)) {
        suffix := v.suffix
        code := Impl.AesCbc.X86.Wiped.encrypt (encryptCode v) v.suffix (encWritten v)
        stack := 72
        verified := encrypt_verified v
        spSafe := encrypt_spSafe v }
      (encryptOut _ _) (W := 72) (hs := encWiped_scrub v h)

theorem encrypt_scrubbed (v : BlocksImpl) :
    VerifiedScrubbed X86.target (Impl.AesCbc.X86.Fn.encrypt (encryptCode v) v.suffix (encWritten v))
      (Spec.Cbc.aesEncryptContract X86.abi (cbcStack (encWritten v) 24)) 0 :=
  encrypt_imp (encrypt_wipes v) id

theorem encrypt_public (v : BlocksImpl) :
    Spec.Cbc.aesScratchOut.Of X86.abi (Impl.AesCbc.X86.Fn.encrypt (encryptCode v) v.suffix (encWritten v))
      (Spec.Cbc.aesEncryptContract X86.abi (cbcStack (encWritten v) 24)) :=
  scratch_public (encrypt_wipes v)

/-- `vg_aes_cbc_encrypt` over `v` as emitted writes `esp` only in its frames and calls. -/
theorem encrypt_fnSpSafe (v : BlocksImpl) :
    (Impl.AesCbc.X86.Fn.encrypt (encryptCode v) v.suffix (encWritten v)).all
      (fun i => !X86.isa.writesSp i) = true := by
  unfold Impl.AesCbc.X86.Fn.encrypt
  split
  · exact scrubAll_spSafe (encryptCode_spSafe v)
  · exact scrubAll_spSafe (encrypt_spSafe v)

/-- `vg_aes_cbc_decrypt` over `v` as emitted (`Impl.AesCbc.X86.Fn.decrypt`)
meets its contract in constant time and returns without secret residue. -/
theorem decrypt_wipes (v : BlocksImpl) :
    VerifiedScrubbed X86.target (Impl.AesCbc.X86.Fn.decrypt (decryptCode v) v.suffix (decWritten v) (decStack v))
      (wipedContract decPost (decZeroed v) X86.abi (cbcStack (decWritten v) (decStack v))) 0 := by
  unfold Impl.AesCbc.X86.Fn.decrypt cbcStack
  by_cases h : decWritten v = 0
  · rw [ite_eq_left h, ite_eq_left h]
    exact verifiedScrubbedAll (api := wipedApi decPost (decZeroed v)) {
        suffix := v.suffix
        code := decryptCode v
        stack := decStack v
        verified := decrypt_free v h
        spSafe := decryptCode_spSafe v }
      (decryptOut _ _) (W := decStack v) (hs := decFree_scrub v h)
  · rw [ite_eq_right h, ite_eq_right h]
    exact verifiedScrubbedAll (api := wipedApi decPost (decZeroed v)) {
        suffix := v.suffix
        code := Impl.AesCbc.X86.Wiped.decrypt (decryptCode v) v.suffix (decWritten v)
        stack := decStack v + 48
        verified := decrypt_verified v
        spSafe := decrypt_spSafe v }
      (decryptOut _ _) (W := decStack v + 48) (hs := decWiped_scrub v)

theorem decrypt_scrubbed (v : BlocksImpl) :
    VerifiedScrubbed X86.target (Impl.AesCbc.X86.Fn.decrypt (decryptCode v) v.suffix (decWritten v) (decStack v))
      (Spec.Cbc.aesDecryptContract X86.abi (cbcStack (decWritten v) (decStack v))) 0 :=
  decrypt_imp (decrypt_wipes v) id

theorem decrypt_public (v : BlocksImpl) :
    Spec.Cbc.aesScratchOut.Of X86.abi (Impl.AesCbc.X86.Fn.decrypt (decryptCode v) v.suffix (decWritten v) (decStack v))
      (Spec.Cbc.aesDecryptContract X86.abi (cbcStack (decWritten v) (decStack v))) :=
  scratch_public (decrypt_wipes v)

/-- `vg_aes_cbc_decrypt` over `v` as emitted writes `esp` only in its frames and calls. -/
theorem decrypt_fnSpSafe (v : BlocksImpl) :
    (Impl.AesCbc.X86.Fn.decrypt (decryptCode v) v.suffix (decWritten v) (decStack v)).all
      (fun i => !X86.isa.writesSp i) = true := by
  unfold Impl.AesCbc.X86.Fn.decrypt
  split
  · exact scrubAll_spSafe (decryptCode_spSafe v)
  · exact scrubAll_spSafe (decrypt_spSafe v)

end VG.Proof.AesCbc.X86.Scrub
