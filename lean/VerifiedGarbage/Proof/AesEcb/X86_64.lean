module

public import VerifiedGarbage.Impl.AesEcb.X86_64.Fn
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.AesEcb.Wipe
public import VerifiedGarbage.Proof.Aes.X86_64.BlocksVariant
public import VerifiedGarbage.Proof.Framework.X86_64.CallWipe
public import VerifiedGarbage.Proof.Zeroize.X86_64Impl
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr

/-!
# AES-ECB on x86-64

`vg_aes_ecb_encrypt` and `vg_aes_ecb_decrypt`, for each implementation `v`
of the blocks functions (`BlocksImpl`) and `z` of `vg_zeroize`
(`ZeroizeImpl`): where `v`'s function writes nothing in `scratch`
(`v.encWritten = 0`), its code (`encrypt_free`, `Verified.ecb_of_unwritten`);
otherwise a call of it, then of `z` on the first `v.encWritten` bytes of
`scratch`, the only ones it writes (`encrypt_verified`:
`Verified.callWipeTail'`, with the side conditions of
`Proof/AesEcb/Wipe.lean`, with 24 bytes of stack, the frame and the return
address). Likewise for decryption.

Which of these are emitted, for each `v` and `z` (`Artifacts/AesEcb/X86_64.lean`):
`v`'s code alone, where it writes nothing in `scratch`,
once (with the `z` of no suffix); the call wiped with `z` where `v` needs
AVX, only with the `z` that needs it (so the instance has `v`'s suffix and
needs no more than `v`'s features); and otherwise the call wiped with each
`z`, named by both suffixes. `v`'s code alone is followed by
`Impl.Scrub.X86_64.scrubSel` (`X86_64.Scrub.verifiedScrubbedSel`) where `v` gives its
residue analysis (`BlocksImpl.ecbEncRes`); every other instance returns
with its whole stack wiped (`Impl.Scrub.X86_64.scrubAll`, at most 24 bytes).
Their postconditions read the memory on return only within the data and
`scratch` (`wipedOut`). Each is proven to leave the bytes of `scratch` that it
writes zero, and the others as they were (`*_wipes`), which implies its
contract (`*_scrubbed`) and that which bytes those are is public (`*_public`).
-/

@[expose] public section

namespace VG.Proof.AesEcb.X86_64

open VG VG.X86_64 VG.Proof.Aes.X86_64 VG.Proof.Zeroize.X86_64 VG.X86_64.Scrub

theorem enc_verified (v : BlocksImpl) :
    Verified target v.enc.code (Proof.Aes.encryptBlocksRoundsContract abi) :=
  Verified.of_correct v.encOk v.encCt AesNi.encryptBlocks_implies

theorem dec_verified (v : BlocksImpl) :
    Verified target v.dec.code (Proof.Aes.decryptBlocksRoundsContract abi) :=
  Verified.of_correct v.decOk v.decCt AesNi.decryptBlocks_implies

theorem args_length : ∀ s vals,
    abi.args ((Spec.Aes.blocksSig.words abi.ptrBits).map (·.bits abi.ptrBits)) = some vals →
      (vals s).length = (Spec.Aes.blocksSig.words abi.ptrBits).length := by
  intro s vals hv
  obtain rfl := Option.some.inj (hv.symm.trans (rfl : abi.args _ = some (regArgs Spec.Aes.blocksSig)))
  exact regArgs_length Spec.Aes.blocksSig s (by decide)

/-- A state satisfying the ECB contracts' precondition. -/
theorem sat (post : Spec.Aes.blocksSig.Post 64) :
    ∃ s, (Spec.Aes.blocksSig.contract abi (pre 64) post false 24 none).pre s := by
  implies_sat [Spec.Aes.blocksSig, pre, X86_64.abi, X86_64.argRegs] [Proof.Aes.X86_64.blocksSat]
    using Proof.Aes.X86_64.blocksSat

/-- A call of the blocks function `b`, then of `z` on the first `n` bytes of
`scratch` (the fifth argument, in `r8`). -/
def wiped (z : ZeroizeImpl) (n : Nat) (b : Impl.Aes.X86_64.Blocks) : Prog isa :=
  Impl.CallWipe.X86_64.callWipe .r8 n b.name b.code z.name z.code

theorem wiped_spSafe {z : ZeroizeImpl} {n : Nat} {b : Impl.Aes.X86_64.Blocks}
    (h : b.code.all (fun i => !isa.writesSp i) = true) :
    (wiped z n b).all (fun i => !isa.writesSp i) = true :=
  callWipe_spSafe h z.spSafe

/-- `vg_aes_ecb_encrypt` for `v`, where its blocks function writes nothing in
`scratch`: that function's code. -/
theorem encrypt_free (v : BlocksImpl) (h : v.encWritten = 0) :
    Verified target v.enc.code (wipedContract enc 0 abi 0) :=
  Verified.ecb_of_unwritten (Proof.Aes.encryptBlocks_keyed (enc_verified v)) (h ▸ v.encWrittenOk)
    args_length

/-- `vg_aes_ecb_decrypt` for `v`, where its blocks function writes nothing in
`scratch`. -/
theorem decrypt_free (v : BlocksImpl) (h : v.decWritten = 0) :
    Verified target v.dec.code (wipedContract dec 0 abi 0) :=
  Verified.ecb_of_unwritten (Proof.Aes.decryptBlocks_keyed (dec_verified v)) (h ▸ v.decWrittenOk)
    args_length

/-- `vg_aes_ecb_encrypt` for `v`: its blocks function, then `z` on the bytes
of `scratch` it writes. -/
theorem encrypt_verified (v : BlocksImpl) (z : ZeroizeImpl) :
    Verified target (wiped z v.encWritten v.enc) (wipedContract enc v.encWritten abi 24) :=
  Verified.callWipeTail' (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("data", .slice true (.array .u8 16) "n")]) (ps₂ := []) (nm := "scratch") (e := .u64) (k := 256)
    (i := 4)
    (Verified.tail_of_written (Proof.Aes.encryptBlocks_keyed (enc_verified v)) v.encWrittenOk args_length)
    z.verified (by decide) rfl rfl rfl (by have := v.encWrittenLe; simp only [Elem.size]; omega_using [this])
    (by have := v.encWrittenLe; omega_using [this]) (by decide) v.encSpSafe (by rw [v.encNoStack]) z.spSafe z.noMx
    (by rw [z.xd]) (Nat.le_refl _) (pre_local 64) (postTail_local 64 _ _) (postTail_out 64 _ v.encWrittenLe)
    (wipedTail 64 _ _) (sat _)

/-- `vg_aes_ecb_decrypt` for `v`, with `z`. -/
theorem decrypt_verified (v : BlocksImpl) (z : ZeroizeImpl) :
    Verified target (wiped z v.decWritten v.dec) (wipedContract dec v.decWritten abi 24) :=
  Verified.callWipeTail' (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("data", .slice true (.array .u8 16) "n")]) (ps₂ := []) (nm := "scratch") (e := .u64) (k := 256)
    (i := 4)
    (Verified.tail_of_written (Proof.Aes.decryptBlocks_keyed (dec_verified v)) v.decWrittenOk args_length)
    z.verified (by decide) rfl rfl rfl (by have := v.decWrittenLe; simp only [Elem.size]; omega_using [this])
    (by have := v.decWrittenLe; omega_using [this]) (by decide) v.decSpSafe (by rw [v.decNoStack]) z.spSafe z.noMx
    (by rw [z.xd]) (Nat.le_refl _) (pre_local 64) (postTail_local 64 _ _) (postTail_out 64 _ v.decWrittenLe)
    (wipedTail 64 _ _) (sat _)

theorem encrypt_spSafe (v : BlocksImpl) (z : ZeroizeImpl) :
    (wiped z v.encWritten v.enc).all (fun i => !isa.writesSp i) = true := wiped_spSafe v.encSpSafe

theorem decrypt_spSafe (v : BlocksImpl) (z : ZeroizeImpl) :
    (wiped z v.decWritten v.dec).all (fun i => !isa.writesSp i) = true := wiped_spSafe v.decSpSafe

/-- The postcondition of `vg_aes_ecb_encrypt` and `vg_aes_ecb_decrypt` reads the
memory on return only within the buffers. -/
theorem wipedOut (g : List Byte → Spec.Aes.State → Spec.Aes.State) (w stack : Nat) :
    Scrub.PostOut (wipedContract g w abi stack) (Spec.Aes.blocksSig.retBits 64) :=
  Scrub.postOut_of_local (leak := none) Scrub.ScrubAbi.plain (ecbPost_out _ g w)

/-- `vg_aes_ecb_encrypt` as `v`'s encryption alone, where it writes no
scratch space, as emitted (`Impl.AesEcb.X86_64.Fn.plain`). -/
theorem encryptPlain_wipes (v : BlocksImpl) (h : v.encWritten = 0) :
    VerifiedScrubbed target (Impl.AesEcb.X86_64.Fn.plain v.level v.enc) (wipedContract enc 0 abi 0) 0 :=
  verifiedScrubbedAllSide (api := wipedApi enc 0)
    { code := v.enc.code, verified := encrypt_free v h, spSafe := v.encSpSafe }
    v.level (wipedOut enc 0 _) (calleeSide_mono (Nat.le_refl _) (Nat.zero_le _) v.encSide) (Nat.le_refl _)

theorem encryptPlain_scrubbed (v : BlocksImpl) (h : v.encWritten = 0) :
    VerifiedScrubbed target (Impl.AesEcb.X86_64.Fn.plain v.level v.enc) (Spec.AesEcb.encryptApi.contract abi 0) 0 :=
  encrypt_imp (encryptPlain_wipes v h) id

theorem encryptPlain_public (v : BlocksImpl) (h : v.encWritten = 0) :
    Spec.AesEcb.scratchOut.Of abi (Impl.AesEcb.X86_64.Fn.plain v.level v.enc) (Spec.AesEcb.encryptApi.contract abi 0) :=
  scratch_public (encryptPlain_wipes v h)

/-- `vg_aes_ecb_decrypt` as `v`'s decryption alone, as emitted. -/
theorem decryptPlain_wipes (v : BlocksImpl) (h : v.decWritten = 0) :
    VerifiedScrubbed target (Impl.AesEcb.X86_64.Fn.plain v.level v.dec) (wipedContract dec 0 abi 0) 0 :=
  verifiedScrubbedAllSide (api := wipedApi dec 0)
    { code := v.dec.code, verified := decrypt_free v h, spSafe := v.decSpSafe }
    v.level (wipedOut dec 0 _) (calleeSide_mono (Nat.le_refl _) (Nat.zero_le _) v.decSide) (Nat.le_refl _)

theorem decryptPlain_scrubbed (v : BlocksImpl) (h : v.decWritten = 0) :
    VerifiedScrubbed target (Impl.AesEcb.X86_64.Fn.plain v.level v.dec) (Spec.AesEcb.decryptApi.contract abi 0) 0 :=
  decrypt_imp (decryptPlain_wipes v h) id

theorem decryptPlain_public (v : BlocksImpl) (h : v.decWritten = 0) :
    Spec.AesEcb.scratchOut.Of abi (Impl.AesEcb.X86_64.Fn.plain v.level v.dec) (Spec.AesEcb.decryptApi.contract abi 0) :=
  scratch_public (decryptPlain_wipes v h)

/-- `vg_aes_ecb_encrypt` as `v`'s encryption, then the zeroing with `z` of
the scratch space it writes, as emitted (`Impl.AesEcb.X86_64.Fn.wiped`): its code is its code
over a stub, with `v`'s and `z`'s where it calls them (`Fill`). -/
theorem encryptWiped_wipes (v : BlocksImpl) (z : ZeroizeImpl) :
    VerifiedScrubbed target (Impl.AesEcb.X86_64.Fn.wiped (v.level.join z.level) v.encWritten v.enc z.name z.code)
      (wipedContract enc v.encWritten abi 24) 0 :=
  have := calleeSide_mono (level_join_left v.level z.level) (Nat.le_refl _) v.encSide
  have := calleeSide_mono (level_join_right v.level z.level) (Nat.le_refl _) z.side
  verifiedScrubbedAllFill (api := wipedApi enc v.encWritten) (ks := 0) (n := fun _ => 0)
    (a := Impl.CallWipe.X86_64.callWipe .r8 v.encWritten "" (.block []) "" (.block []))
    { code := wiped z v.encWritten v.enc, stack := 24, verified := encrypt_verified v z,
      spSafe := encrypt_spSafe v z }
    _ (wipedOut enc _ _) (by unfold wiped; fill_calls) (Nat.zero_le _) (Nat.le_refl _)
    (ha := by rcases v.writtenOk.1 with h | h <;> rw [h] <;> lit_decide)

theorem encryptWiped_scrubbed (v : BlocksImpl) (z : ZeroizeImpl) :
    VerifiedScrubbed target (Impl.AesEcb.X86_64.Fn.wiped (v.level.join z.level) v.encWritten v.enc z.name z.code)
      (Spec.AesEcb.encryptApi.contract abi 24) 0 :=
  encrypt_imp (encryptWiped_wipes v z) id

theorem encryptWiped_public (v : BlocksImpl) (z : ZeroizeImpl) :
    Spec.AesEcb.scratchOut.Of abi (Impl.AesEcb.X86_64.Fn.wiped (v.level.join z.level) v.encWritten v.enc z.name z.code)
      (Spec.AesEcb.encryptApi.contract abi 24) :=
  scratch_public (encryptWiped_wipes v z)

/-- `vg_aes_ecb_decrypt` as `v`'s decryption, then the zeroing with `z`. -/
theorem decryptWiped_wipes (v : BlocksImpl) (z : ZeroizeImpl) :
    VerifiedScrubbed target (Impl.AesEcb.X86_64.Fn.wiped (v.level.join z.level) v.decWritten v.dec z.name z.code)
      (wipedContract dec v.decWritten abi 24) 0 :=
  have := calleeSide_mono (level_join_left v.level z.level) (Nat.le_refl _) v.decSide
  have := calleeSide_mono (level_join_right v.level z.level) (Nat.le_refl _) z.side
  verifiedScrubbedAllFill (api := wipedApi dec v.decWritten) (ks := 0) (n := fun _ => 0)
    (a := Impl.CallWipe.X86_64.callWipe .r8 v.decWritten "" (.block []) "" (.block []))
    { code := wiped z v.decWritten v.dec, stack := 24, verified := decrypt_verified v z,
      spSafe := decrypt_spSafe v z }
    _ (wipedOut dec _ _) (by unfold wiped; fill_calls) (Nat.zero_le _) (Nat.le_refl _)
    (ha := by rcases v.writtenOk.2 with h | h <;> rw [h] <;> lit_decide)

theorem decryptWiped_scrubbed (v : BlocksImpl) (z : ZeroizeImpl) :
    VerifiedScrubbed target (Impl.AesEcb.X86_64.Fn.wiped (v.level.join z.level) v.decWritten v.dec z.name z.code)
      (Spec.AesEcb.decryptApi.contract abi 24) 0 :=
  decrypt_imp (decryptWiped_wipes v z) id

theorem decryptWiped_public (v : BlocksImpl) (z : ZeroizeImpl) :
    Spec.AesEcb.scratchOut.Of abi (Impl.AesEcb.X86_64.Fn.wiped (v.level.join z.level) v.decWritten v.dec z.name z.code)
      (Spec.AesEcb.decryptApi.contract abi 24) :=
  scratch_public (decryptWiped_wipes v z)

/-! The code as emitted keeps `rsp`: the artifacts' `spSafe`. -/

theorem encryptPlain_spSafeFn (v : BlocksImpl) :
    (Impl.AesEcb.X86_64.Fn.plain v.level v.enc).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe v.encSpSafe

theorem encryptWiped_spSafeFn (v : BlocksImpl) (z : ZeroizeImpl) :
    (Impl.AesEcb.X86_64.Fn.wiped (v.level.join z.level) v.encWritten v.enc z.name z.code).all
      (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (encrypt_spSafe v z)

theorem decryptPlain_spSafeFn (v : BlocksImpl) :
    (Impl.AesEcb.X86_64.Fn.plain v.level v.dec).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe v.decSpSafe

theorem decryptWiped_spSafeFn (v : BlocksImpl) (z : ZeroizeImpl) :
    (Impl.AesEcb.X86_64.Fn.wiped (v.level.join z.level) v.decWritten v.dec z.name z.code).all
      (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (decrypt_spSafe v z)

end VG.Proof.AesEcb.X86_64
