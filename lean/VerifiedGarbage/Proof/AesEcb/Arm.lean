module

public import VerifiedGarbage.Proof.AesEcb.Wipe
public import VerifiedGarbage.Proof.Aes.Arm.Blocks
public import VerifiedGarbage.Proof.Framework.Arm.CallWipeStack
public import VerifiedGarbage.Proof.Zeroize.Arm

/-!
# AES-ECB on ARMv7

`vg_aes_ecb_encrypt` and `vg_aes_ecb_decrypt` call `vg_aes_encrypt_blocks`
and `vg_aes_decrypt_blocks`, which write `scratch` (their fifth argument,
the word on the stack), by `callWipeStack`, which copies that word into its
frame for the call, then zeroes the first `scratchUsed` bytes of `scratch`,
the only ones the blocks functions write (`Proof.Aes.Arm.Ecb.blocks_scratch`:
their slots and the bitsliced round keys), with `vg_zeroize`, with 24 bytes
of stack: `Verified.callWipeStackTail'`, with the side conditions of
`Proof/AesEcb/Wipe.lean`.
-/

@[expose] public section

namespace VG.Proof.AesEcb.Arm

open VG VG.Arm VG.Arm.FrameStack
open VG.Impl.Aes.Arm (scratchUsed)

/-- A call of `name`, whose code is `body`, then of `vg_zeroize` on the
first `scratchUsed` bytes of `scratch`. -/
def wiped (name : String) (body : Prog isa) : Prog isa :=
  Impl.CallWipe.ArmStack.callWipeStack 1 0 scratchUsed name body "vg_zeroize" Impl.Zeroize.Arm.zeroize

/-- `vg_aes_ecb_encrypt`. -/
def encrypt : Prog isa := wiped "vg_aes_encrypt_blocks" Impl.Aes.Arm.encryptBlocks

/-- `vg_aes_ecb_decrypt`. -/
def decrypt : Prog isa := wiped "vg_aes_decrypt_blocks" Impl.Aes.Arm.decryptBlocks

theorem sat (g : List Byte → Spec.Aes.State → Spec.Aes.State) :
    ∃ s, (Spec.Aes.blocksSig.contract abi (pre 32) (ecbPost 32 g) false 24 none).pre s := by
  implies_sat [Spec.Aes.blocksSig, pre, Arm.abi] [Proof.Aes.Arm.Ecb.sat] using Proof.Aes.Arm.Ecb.sat

theorem args_length : ∀ s vals,
    Arm.abi.args ((Spec.Aes.blocksSig.words Arm.abi.ptrBits).map (·.bits Arm.abi.ptrBits)) = some vals →
      (vals s).length = (Spec.Aes.blocksSig.words Arm.abi.ptrBits).length := by
  intro s vals hv
  obtain rfl := Option.some.inj (hv.symm.trans (rfl : Arm.abi.args _ = some (armArgs Spec.Aes.blocksSig)))
  exact armArgs_length Spec.Aes.blocksSig s

/-- What a run writes of `scratch`, from the blocks functions' bound. -/
theorem written_of {s s' : State}
    (h : ∀ i, scratchUsed ≤ i → i < 2048 →
      s'.mem (State.addr (stackArg s 0) + BitVec.ofNat 64 i) =
        s.mem (State.addr (stackArg s 0) + BitVec.ofNat 64 i)) :
    Sig.writtenWithin Arm.abi Spec.Aes.blocksSig [("scratch", scratchUsed)] s s' := by
  simp [Sig.writtenWithin, Arm.abi, Spec.Aes.blocksSig, Sig.words, Param.words, ArgWord.bits, IntTy.bits,
    Sig.arrays, Arm.reduceClassify, Arm.Loc.val, Elem.size]
  exact h

theorem enc_written : ∀ s t s',
    (Spec.Aes.blocksSig.contract abi (pre 32) (post 32 enc) false 0 none).pre s →
      Exec isa Impl.Aes.Arm.encryptBlocks s t s' →
        Sig.writtenWithin Arm.abi Spec.Aes.blocksSig [("scratch", scratchUsed)] s s' :=
  fun s _ _ hs he => written_of fun _ h1 h2 =>
    Proof.Aes.Arm.Ecb.blocks_scratch Proof.Aes.Arm.Ecb.encrypt2_cryptOk
      (Proof.Aes.Arm.Ecb.encryptBlocks_implies.pre s hs) he h1 h2

theorem dec_written : ∀ s t s',
    (Spec.Aes.blocksSig.contract abi (pre 32) (post 32 dec) false 0 none).pre s →
      Exec isa Impl.Aes.Arm.decryptBlocks s t s' →
        Sig.writtenWithin Arm.abi Spec.Aes.blocksSig [("scratch", scratchUsed)] s s' :=
  fun s _ _ hs he => written_of fun _ h1 h2 =>
    Proof.Aes.Arm.Ecb.blocks_scratch Proof.Aes.Arm.Ecb.decrypt2_cryptOk
      (Proof.Aes.Arm.Ecb.decryptBlocks_implies.pre s hs) he h1 h2

theorem wiped_verified {g : List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {body : Prog isa}
    (h : Verified target body (Spec.Aes.blocksSig.contract abi (pre 32) (post 32 g) false 0 none))
    (hw : ∀ s t s', (Spec.Aes.blocksSig.contract abi (pre 32) (post 32 g) false 0 none).pre s →
      Exec isa body s t s' → Sig.writtenWithin Arm.abi Spec.Aes.blocksSig [("scratch", scratchUsed)] s s')
    (hd : armStack body = 0) :
    Verified target (wiped name body) (Spec.Aes.blocksSig.contract abi (pre 32) (ecbPost 32 g) false 24 none) :=
  Verified.callWipeStackTail' (post := postTail 32 g scratchUsed) (post' := ecbPost 32 g)
    (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("data", .slice true (.array .u8 16) "n")]) (ps₂ := []) (nm := "scratch") (e := .u64)
    (kk := 256) (n := scratchUsed) (i := 4) (k := 1) (off := 0)
    (Verified.tail_of_written h hw args_length) Proof.Zeroize.Arm.verified
    (by decide) (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide)
    (by rw [hd]) (by decide) (Nat.zero_le _)
    (pre_local 32) (postTail_local 32 g _) (postTail_out 32 g (by decide)) (wipedTail 32 g _) (sat g)

theorem encrypt_verified : Verified target encrypt (Spec.AesEcb.encryptContract abi 24) :=
  wiped_verified (Proof.Aes.encryptBlocks_keyed Proof.Aes.Arm.Ecb.encryptBlocks_verified) enc_written
    (by decide)

theorem decrypt_verified : Verified target decrypt (Spec.AesEcb.decryptContract abi 24) :=
  wiped_verified (Proof.Aes.decryptBlocks_keyed Proof.Aes.Arm.Ecb.decryptBlocks_verified) dec_written
    (by decide)

end VG.Proof.AesEcb.Arm
