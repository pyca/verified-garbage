module

public import VerifiedGarbage.Proof.AesEcb.Wipe
public import VerifiedGarbage.Impl.AesEcb.X86
public import VerifiedGarbage.Proof.Aes.X86.BlocksVariant
public import VerifiedGarbage.Proof.Framework.X86.CallWipe
public import VerifiedGarbage.Proof.Zeroize.X86
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.AesEcb.Wipe
meta import VerifiedGarbage.Impl.AesEcb.X86
meta import VerifiedGarbage.Proof.Aes.X86.BlocksVariant
meta import VerifiedGarbage.Proof.Framework.X86.CallWipe
meta import VerifiedGarbage.Proof.Zeroize.X86
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# AES-ECB on x86

`vg_aes_ecb_encrypt` and `vg_aes_ecb_decrypt` (`Impl/AesEcb/X86.lean`), for
each implementation `v` of the blocks functions (`BlocksImpl`), call it,
then zero the whole of `scratch` (2048 bytes, which the blocks functions'
proofs do not bound) with `vg_zeroize`: `Verified.callWipe'`, with the side
conditions of `Proof/AesEcb/Wipe.lean`, with 32 bytes of stack (the frame
and the return address).
-/

@[expose] public section

namespace VG.Proof.AesEcb.X86

open VG VG.X86 VG.Proof.Aes.X86

theorem zeroize_noSp : NoSp Impl.Zeroize.X86.zeroize := NoSp.of_all (by lit_decide)

theorem zeroize_stack : stackUse Impl.Zeroize.X86.zeroize ≤ 0 := by lit_decide

theorem enc_verified (v : BlocksImpl) :
    Verified X86.target v.enc.code (Proof.Aes.encryptBlocksRoundsContract X86.abi) :=
  Verified.of_correct v.encOk v.encCt
    (by
      have a0 : arg blocksSat 0 = 0x1000 := by decide
      have a1 : arg blocksSat 1 = 10 := by decide
      have a2 : arg blocksSat 2 = 0x3000 := by decide
      have a3 : arg blocksSat 3 = 0 := by decide
      have a4 : arg blocksSat 4 = 0x4000 := by decide
      have e : argAddr blocksSat 0 = 0x8004 := by decide
      have esp : blocksSat.gpr .esp = 0x8000 := rfl
      sig_implies [Proof.Aes.encryptBlocksRoundsContract, Spec.Aes.blocksSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Proof.Aes.blocksX86] [a0, a1, a2, a3, a4, e, esp] using blocksSat)

theorem dec_verified (v : BlocksImpl) :
    Verified X86.target v.dec.code (Proof.Aes.decryptBlocksRoundsContract X86.abi) :=
  Verified.of_correct v.decOk v.decCt
    (by
      have a0 : arg blocksSat 0 = 0x1000 := by decide
      have a1 : arg blocksSat 1 = 10 := by decide
      have a2 : arg blocksSat 2 = 0x3000 := by decide
      have a3 : arg blocksSat 3 = 0 := by decide
      have a4 : arg blocksSat 4 = 0x4000 := by decide
      have e : argAddr blocksSat 0 = 0x8004 := by decide
      have esp : blocksSat.gpr .esp = 0x8000 := rfl
      sig_implies [Proof.Aes.decryptBlocksRoundsContract, Spec.Aes.blocksSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Proof.Aes.blocksX86] [a0, a1, a2, a3, a4, e, esp] using blocksSat)

/-- A state satisfying the ECB contracts' precondition. -/
theorem sat : ∃ s, (Spec.Aes.blocksSig.contract X86.abi (pre 32) (ecbPost 32 enc) false 32).pre s := by
  have a0 : arg blocksSat 0 = 0x1000 := by decide
  have a1 : arg blocksSat 1 = 10 := by decide
  have a2 : arg blocksSat 2 = 0x3000 := by decide
  have a3 : arg blocksSat 3 = 0 := by decide
  have a4 : arg blocksSat 4 = 0x4000 := by decide
  have e : argAddr blocksSat 0 = 0x8004 := by decide
  have esp : blocksSat.gpr .esp = 0x8000 := rfl
  implies_sat [Spec.Aes.blocksSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, pre]
    [a0, a1, a2, a3, a4, e, esp] using blocksSat

/-- The ECB contracts' precondition does not depend on the postcondition. -/
theorem sat' (post : Spec.Aes.blocksSig.Post 32) :
    ∃ s, (Spec.Aes.blocksSig.contract X86.abi (pre 32) post false 32).pre s := sat

/-- `vg_aes_ecb_encrypt` for `v`. -/
theorem encrypt_verified (v : BlocksImpl) :
    Verified X86.target (Impl.AesEcb.X86.wiped v.enc) (Spec.AesEcb.encryptContract X86.abi 32) :=
  Verified.callWipe' (sig := Spec.Aes.blocksSig) (stack := 0) (zst := 0)
    (pre := pre 32) (post := post 32 enc) (post' := ecbPost 32 enc)
    (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("data", .slice true (.array .u8 16) "n")]) (ps₂ := []) (i := 4) (j := 4)
    (Proof.Aes.encryptBlocks_keyed (enc_verified v)) Proof.Zeroize.X86.verified
    (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) v.encNosp (by rw [v.encStack])
    zeroize_noSp zeroize_stack (by decide)
    (pre_local 32) (post_local 32 _) (post_out 32 _) (AesEcb.wiped 32 _) (sat' _)

/-- `vg_aes_ecb_decrypt` for `v`. -/
theorem decrypt_verified (v : BlocksImpl) :
    Verified X86.target (Impl.AesEcb.X86.wiped v.dec) (Spec.AesEcb.decryptContract X86.abi 32) :=
  Verified.callWipe' (sig := Spec.Aes.blocksSig) (stack := 0) (zst := 0)
    (pre := pre 32) (post := post 32 dec) (post' := ecbPost 32 dec)
    (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("data", .slice true (.array .u8 16) "n")]) (ps₂ := []) (i := 4) (j := 4)
    (Proof.Aes.decryptBlocks_keyed (dec_verified v)) Proof.Zeroize.X86.verified
    (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) v.decNosp (by rw [v.decStack])
    zeroize_noSp zeroize_stack (by decide)
    (pre_local 32) (post_local 32 _) (post_out 32 _) (AesEcb.wiped 32 _) (sat' _)

theorem zeroize_spSafe : Impl.Zeroize.X86.zeroize.all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (by lit_decide)

/-- `wiped b` writes `esp` only in its frame and calls, if `b`'s code does
only in its frames. -/
theorem wiped_spSafe {b : Impl.Aes.X86.Blocks} (h : b.code.all (fun i => !isa.writesSp i) = true) :
    (Impl.AesEcb.X86.wiped b).all (fun i => !isa.writesSp i) = true := by
  have hz := zeroize_spSafe
  simp only [isa] at h hz
  simp only [Impl.AesEcb.X86.wiped, Impl.CallWipe.X86.callWipe, Code.all, isa, h, hz, Bool.true_and]
  decide

theorem encrypt_spSafe (v : BlocksImpl) :
    (Impl.AesEcb.X86.wiped v.enc).all (fun i => !isa.writesSp i) = true := wiped_spSafe v.encSpSafe

theorem decrypt_spSafe (v : BlocksImpl) :
    (Impl.AesEcb.X86.wiped v.dec).all (fun i => !isa.writesSp i) = true := wiped_spSafe v.decSpSafe

end VG.Proof.AesEcb.X86
