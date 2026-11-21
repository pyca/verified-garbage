module

public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesCbc.X86.Wiped
public import VerifiedGarbage.Spec.Cbc.Contract
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Impl.AesCbc.X86.Wiped
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
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Impl.AesCbc.X86.Wiped

/-!
# AES-CBC on x86 (32-bit), without secret residue

`vg_aes_cbc_encrypt` and `vg_aes_cbc_decrypt` read the memory on return only
within the IV, the data and `scratch` (`encryptOut`, `decryptOut`), as on
PPC64LE (`Proof/Aes/PPC64LE/Scrub.lean`): what the scrub of their frames and
calls needs (`X86.Scrub.PostOut`).

Which code is emitted for an implementation `v` of the block functions
(`Impl.AesCbc.X86.Fn`), with its stack (`cbcStack`), as
`Proof/AesCbc/X86/Wiped.lean` chooses it: the CBC code (`encryptCode v`)
where it writes nothing in `scratch`, with 24 bytes of stack; otherwise the
call of it, then of `vg_zeroize` on the bytes of `scratch` it writes, with
72. Each zeroes that stack below `esp` and clears the registers, and returns
without secret residue (`X86.Scrub.verifiedScrubbedAll`), which
`encrypt_scrubbed` and `decrypt_scrubbed` prove by cases. What that
needs of the code (`scrubFSide`) holds whatever the implementation: the CBC
code for AES-NI (`hardware`) is a closed term, which the kernel evaluates
(`ni_side`, `dec_callee`); for any other, the CBC code around a stub block
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
open Impl.CallWipe.X86 (frameSize copyArgs zeroArgs restoreRet)

/-! ## Postconditions -/

/-- The postcondition of `vg_aes_cbc_encrypt` reads the memory on return only
within the buffers. -/
theorem encryptOut (stack : Nat) :
    PostOut (Spec.Cbc.aesEncryptContract abi stack) (Spec.Cbc.aesSig.retBits 32) := by
  rw [Proof.AesCbc.Wipe.encrypt_eq]
  exact postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
    rw [bufs_eq] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
    obtain ⟨h1, h2⟩ := h
    have hd := AesEcb.agree_of hb.2.2.1
    have hb' : Spec.Cbc.blocksAt m₂ d (e.setWidth abi.ptrBits).toNat = Spec.Cbc.blocksAt m₁ d (e.setWidth abi.ptrBits).toNat :=
      blocksAt_congr fun i hi => hd i (by have := AesEcb.n_le (pb := abi.ptrBits) e; omega_using [hi, this])
    have hc := AesEcb.bytesAt_congr (AesEcb.agree_of hb.2.1)
    refine ⟨fun key hk => ?_, fun z hz => ?_⟩
    · obtain ⟨h1a, h1b⟩ := h1 key hk
      exact ⟨hb'.trans h1a, hc.trans h1b⟩
    · rw [← hb.2.2.2 z hz]
      exact h2 z hz

/-- The postcondition of `vg_aes_cbc_decrypt` reads the memory on return only
within the buffers. -/
theorem decryptOut (stack : Nat) :
    PostOut (Spec.Cbc.aesDecryptContract abi stack) (Spec.Cbc.aesSig.retBits 32) := by
  rw [Proof.AesCbc.Wipe.decrypt_eq]
  exact postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
    rw [bufs_eq] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
    obtain ⟨h1, h2⟩ := h
    have hd := AesEcb.agree_of hb.2.2.1
    have hb' : Spec.Cbc.blocksAt m₂ d (e.setWidth abi.ptrBits).toNat = Spec.Cbc.blocksAt m₁ d (e.setWidth abi.ptrBits).toNat :=
      blocksAt_congr fun i hi => hd i (by have := AesEcb.n_le (pb := abi.ptrBits) e; omega_using [hi, this])
    have hc := AesEcb.bytesAt_congr (AesEcb.agree_of hb.2.1)
    refine ⟨fun key hk => ?_, fun z hz => ?_⟩
    · obtain ⟨h1a, h1b⟩ := h1 key hk
      exact ⟨hb'.trans h1a, hc.trans h1b⟩
    · rw [← hb.2.2.2 z hz]
      exact h2 z hz

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
materialize_code encryptNiLit := Impl.AesCbc.X86.encryptNi
materialize_code decryptNiLit := Impl.AesCbc.X86.Decrypt.decrypt
materialize_code encZStub := Impl.AesCbc.X86.encryptZ stubBlocks
materialize_code decZStub := Impl.AesCbc.X86.decryptZ stubBlocks
materialize_code encWStub := wipedStub (Impl.AesCbc.X86.encryptZ stubBlocks)
materialize_code decWStub := wipedStub (Impl.AesCbc.X86.decryptZ stubBlocks)
materialize_code holeWStub := wipedStub (.block [])

theorem ni_side : scrubFSide Impl.AesCbc.X86.encryptNi [] 24 = true := by
  lit_decide

theorem dec_callee : calleeSide Impl.AesCbc.X86.Decrypt.decrypt 24 = true := by
  lit_decide

theorem encZ_side : scrubFSide (Impl.AesCbc.X86.encryptZ stubBlocks) [] 24 = true := by
  lit_decide

theorem decZ_side : scrubFSide (Impl.AesCbc.X86.decryptZ stubBlocks) [] 24 = true := by
  lit_decide

theorem encW_side : scrubFSide (wipedStub (Impl.AesCbc.X86.encryptZ stubBlocks)) [] 72 = true := by
  lit_decide

theorem decW_side : scrubFSide (wipedStub (Impl.AesCbc.X86.decryptZ stubBlocks)) [] 72 = true := by
  lit_decide

theorem holeW_side : scrubFSide (wipedStub (.block [])) [] 48 = true := by
  lit_decide

/-- The instructions that pass `vg_zeroize` its length, whatever it is. -/
theorem zeroArgs_side (n k : Nat) : calleeSide (.block (zeroArgs 6 5 n)) k = true := rfl

theorem encZ_fill (b : Impl.Aes.X86.Blocks) (hb : calleeSide b.code 0 = true) :
    Fill 0 (Impl.AesCbc.X86.encryptZ stubBlocks) (Impl.AesCbc.X86.encryptZ b) := by
  fill_calls

theorem decZ_fill (b : Impl.Aes.X86.Blocks) (hb : calleeSide b.code 0 = true) :
    Fill 0 (Impl.AesCbc.X86.decryptZ stubBlocks) (Impl.AesCbc.X86.decryptZ b) := by
  fill_calls

theorem encW_fill (b : Impl.Aes.X86.Blocks) (sfx : String) (n : Nat) (hb : calleeSide b.code 0 = true)
    (hz : calleeSide (.block (zeroArgs 6 5 n)) 0 = true) :
    Fill 0 (wipedStub (Impl.AesCbc.X86.encryptZ stubBlocks))
      (Impl.AesCbc.X86.Wiped.encrypt (Impl.AesCbc.X86.encryptZ b) sfx n) := by
  fill_calls

theorem decW_fill (b : Impl.Aes.X86.Blocks) (sfx : String) (n : Nat) (hb : calleeSide b.code 0 = true)
    (hz : calleeSide (.block (zeroArgs 6 5 n)) 0 = true) :
    Fill 0 (wipedStub (Impl.AesCbc.X86.decryptZ stubBlocks))
      (Impl.AesCbc.X86.Wiped.decrypt (Impl.AesCbc.X86.decryptZ b) sfx n) := by
  fill_calls

theorem holeW_fill (body : Prog isa) (sfx : String) (n : Nat) (hb : calleeSide body 24 = true)
    (hz : calleeSide (.block (zeroArgs 6 5 n)) 24 = true) :
    Fill 24 (wipedStub (.block [])) (Impl.AesCbc.X86.Wiped.decrypt body sfx n) := by
  fill_calls

/-- `scrubFSide` of the CBC encryption code, where it writes nothing in
`scratch`, whatever the implementation. -/
theorem encFree_scrub (v : BlocksImpl) : scrubFSide (encryptCode v) [] 24 = true := by
  by_cases hw : hardware v = true
  · rw [encryptCode, ite_eq_left hw]; exact ni_side
  · rw [encryptCode, ite_eq_right hw]
    exact scrubFSide_of_fill (encZ_fill _ (calleeSide_of_eq v.encStack v.encScrub)) encZ_side

/-- `scrubFSide` of the call of the CBC encryption code, then of
`vg_zeroize`, where it writes in `scratch`. -/
theorem encWiped_scrub (v : BlocksImpl) (h : ¬encWritten v = 0) :
    scrubFSide (Impl.AesCbc.X86.Wiped.encrypt (encryptCode v) v.suffix (encWritten v)) [] 72 = true := by
  have hw : ¬hardware v = true := fun hw => h (by rw [encWritten, ite_eq_left hw])
  rw [encryptCode, ite_eq_right hw]
  exact scrubFSide_of_fill (encW_fill _ _ _ (calleeSide_of_eq v.encStack v.encScrub) (zeroArgs_side _ _))
    encW_side

/-- `scrubFSide` of the CBC decryption code, where it writes nothing in
`scratch` (never with AES-NI). -/
theorem decFree_scrub (v : BlocksImpl) (h : decWritten v = 0) : scrubFSide (decryptCode v) [] 24 = true := by
  have hw : ¬hardware v = true := fun hw => by rw [decWritten, ite_eq_left hw] at h; exact absurd h (by decide)
  rw [decryptCode, ite_eq_right hw]
  exact scrubFSide_of_fill (decZ_fill _ (calleeSide_of_eq v.decStack v.decScrub)) decZ_side

/-- `scrubFSide` of the call of the CBC decryption code, then of
`vg_zeroize`. -/
theorem decWiped_scrub (v : BlocksImpl) :
    scrubFSide (Impl.AesCbc.X86.Wiped.decrypt (decryptCode v) v.suffix (decWritten v)) [] 72 = true := by
  by_cases hw : hardware v = true
  · have hd : calleeSide (decryptCode v) 24 = true := by rw [decryptCode, ite_eq_left hw]; exact dec_callee
    exact scrubFSide_of_fill (holeW_fill _ _ _ hd (zeroArgs_side _ _)) holeW_side
  · rw [decryptCode, ite_eq_right hw]
    exact scrubFSide_of_fill (decW_fill _ _ _ (calleeSide_of_eq v.decStack v.decScrub) (zeroArgs_side _ _))
      decW_side

/-! ## The functions as emitted -/

/-- The stack of `vg_aes_cbc_encrypt` and `vg_aes_cbc_decrypt` whose CBC
code writes the first `w` bytes of `scratch`: 24 bytes where the code is
the CBC code itself, 72 for the call wiping `scratch`
(`Impl.AesCbc.X86.Fn`). -/
def cbcStack (w : Nat) : Nat := if w = 0 then 24 else 72

/-- `vg_aes_cbc_encrypt` over `v` as emitted (`Impl.AesCbc.X86.Fn.encrypt`)
meets its contract in constant time and returns without secret residue. -/
theorem encrypt_scrubbed (v : BlocksImpl) :
    VerifiedScrubbed X86.target (Impl.AesCbc.X86.Fn.encrypt (encryptCode v) v.suffix (encWritten v))
      (Spec.Cbc.aesEncryptContract X86.abi (cbcStack (encWritten v))) 0 := by
  unfold Impl.AesCbc.X86.Fn.encrypt cbcStack
  by_cases h : encWritten v = 0
  · rw [ite_eq_left h, ite_eq_left h]
    exact verifiedScrubbedAll (api := Spec.Cbc.aesEncryptApi) {
        suffix := v.suffix
        code := encryptCode v
        stack := 24
        verified := encrypt_free v h
        spSafe := encryptCode_spSafe v }
      (encryptOut _) (W := 24) (hs := encFree_scrub v)
  · rw [ite_eq_right h, ite_eq_right h]
    exact verifiedScrubbedAll (api := Spec.Cbc.aesEncryptApi) {
        suffix := v.suffix
        code := Impl.AesCbc.X86.Wiped.encrypt (encryptCode v) v.suffix (encWritten v)
        stack := 72
        verified := encrypt_verified v
        spSafe := encrypt_spSafe v }
      (encryptOut _) (W := 72) (hs := encWiped_scrub v h)

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
theorem decrypt_scrubbed (v : BlocksImpl) :
    VerifiedScrubbed X86.target (Impl.AesCbc.X86.Fn.decrypt (decryptCode v) v.suffix (decWritten v))
      (Spec.Cbc.aesDecryptContract X86.abi (cbcStack (decWritten v))) 0 := by
  unfold Impl.AesCbc.X86.Fn.decrypt cbcStack
  by_cases h : decWritten v = 0
  · rw [ite_eq_left h, ite_eq_left h]
    exact verifiedScrubbedAll (api := Spec.Cbc.aesDecryptApi) {
        suffix := v.suffix
        code := decryptCode v
        stack := 24
        verified := decrypt_free v h
        spSafe := decryptCode_spSafe v }
      (decryptOut _) (W := 24) (hs := decFree_scrub v h)
  · rw [ite_eq_right h, ite_eq_right h]
    exact verifiedScrubbedAll (api := Spec.Cbc.aesDecryptApi) {
        suffix := v.suffix
        code := Impl.AesCbc.X86.Wiped.decrypt (decryptCode v) v.suffix (decWritten v)
        stack := 72
        verified := decrypt_verified v
        spSafe := decrypt_spSafe v }
      (decryptOut _) (W := 72) (hs := decWiped_scrub v)

/-- `vg_aes_cbc_decrypt` over `v` as emitted writes `esp` only in its frames and calls. -/
theorem decrypt_fnSpSafe (v : BlocksImpl) :
    (Impl.AesCbc.X86.Fn.decrypt (decryptCode v) v.suffix (decWritten v)).all
      (fun i => !X86.isa.writesSp i) = true := by
  unfold Impl.AesCbc.X86.Fn.decrypt
  split
  · exact scrubAll_spSafe (decryptCode_spSafe v)
  · exact scrubAll_spSafe (decrypt_spSafe v)

end VG.Proof.AesCbc.X86.Scrub
