module

public import VerifiedGarbage.Proof.AesEcb.Wipe
public import VerifiedGarbage.Proof.Aes.X86_64.BlocksVariant
public import VerifiedGarbage.Proof.Framework.X86_64.CallWipe
public import VerifiedGarbage.Proof.Zeroize.X86_64Impl
import VerifiedGarbage.Proof.Framework.Contract

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
-/

@[expose] public section

namespace VG.Proof.AesEcb.X86_64

open VG VG.X86_64 VG.Proof.Aes.X86_64 VG.Proof.Zeroize.X86_64

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
    Verified target v.enc.code (Spec.AesEcb.encryptContract abi 0) :=
  Verified.ecb_of_unwritten (Proof.Aes.encryptBlocks_keyed (enc_verified v)) (h ▸ v.encWrittenOk)
    args_length

/-- `vg_aes_ecb_decrypt` for `v`, where its blocks function writes nothing in
`scratch`. -/
theorem decrypt_free (v : BlocksImpl) (h : v.decWritten = 0) :
    Verified target v.dec.code (Spec.AesEcb.decryptContract abi 0) :=
  Verified.ecb_of_unwritten (Proof.Aes.decryptBlocks_keyed (dec_verified v)) (h ▸ v.decWrittenOk)
    args_length

/-- `vg_aes_ecb_encrypt` for `v`: its blocks function, then `z` on the bytes
of `scratch` it writes. -/
theorem encrypt_verified (v : BlocksImpl) (z : ZeroizeImpl) :
    Verified target (wiped z v.encWritten v.enc) (Spec.AesEcb.encryptContract abi 24) :=
  Verified.callWipeTail' (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("data", .slice true (.array .u8 16) "n")]) (ps₂ := []) (nm := "scratch") (e := .u64) (k := 256)
    (i := 4)
    (Verified.tail_of_written (Proof.Aes.encryptBlocks_keyed (enc_verified v)) v.encWrittenOk args_length)
    z.verified (by decide) rfl rfl rfl (by have := v.encWrittenLe; simp only [Elem.size]; omega)
    (by have := v.encWrittenLe; omega) (by decide) v.encSpSafe (by rw [v.encNoStack]) z.spSafe
    (by rw [z.xd]) (Nat.le_refl _) (pre_local 64) (postTail_local 64 _ _) (postTail_out 64 _ v.encWrittenLe)
    (wipedTail 64 _ _) (sat _)

/-- `vg_aes_ecb_decrypt` for `v`, with `z`. -/
theorem decrypt_verified (v : BlocksImpl) (z : ZeroizeImpl) :
    Verified target (wiped z v.decWritten v.dec) (Spec.AesEcb.decryptContract abi 24) :=
  Verified.callWipeTail' (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("data", .slice true (.array .u8 16) "n")]) (ps₂ := []) (nm := "scratch") (e := .u64) (k := 256)
    (i := 4)
    (Verified.tail_of_written (Proof.Aes.decryptBlocks_keyed (dec_verified v)) v.decWrittenOk args_length)
    z.verified (by decide) rfl rfl rfl (by have := v.decWrittenLe; simp only [Elem.size]; omega)
    (by have := v.decWrittenLe; omega) (by decide) v.decSpSafe (by rw [v.decNoStack]) z.spSafe
    (by rw [z.xd]) (Nat.le_refl _) (pre_local 64) (postTail_local 64 _ _) (postTail_out 64 _ v.decWrittenLe)
    (wipedTail 64 _ _) (sat _)

theorem encrypt_spSafe (v : BlocksImpl) (z : ZeroizeImpl) :
    (wiped z v.encWritten v.enc).all (fun i => !isa.writesSp i) = true := wiped_spSafe v.encSpSafe

theorem decrypt_spSafe (v : BlocksImpl) (z : ZeroizeImpl) :
    (wiped z v.decWritten v.dec).all (fun i => !isa.writesSp i) = true := wiped_spSafe v.decSpSafe

end VG.Proof.AesEcb.X86_64
