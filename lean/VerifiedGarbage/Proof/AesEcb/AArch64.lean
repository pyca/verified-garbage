module

public import VerifiedGarbage.Proof.AesEcb.Wipe
public import VerifiedGarbage.Proof.Aes.AArch64.BlocksVariant
public import VerifiedGarbage.Proof.Framework.AArch64.CallWipe
public import VerifiedGarbage.Proof.Zeroize.AArch64Wide
import VerifiedGarbage.Proof.Framework.AArch64.Depth
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.AArch64.Clears
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
public import VerifiedGarbage.Impl.AesEcb.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.SideFill
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# AES-ECB on AArch64

For each implementation of the blocks functions (`BlocksImpl`),
`vg_aes_ecb_encrypt` and `vg_aes_ecb_decrypt` as emitted are
`Impl.AesEcb.AArch64.Fn.blocks` of its functions. Where it needs no `scratch`,
and so writes nothing in it, they are its code (`encrypt_free`,
`decrypt_free`) with the vector registers it writes cleared; otherwise a call
of it by `callWipe`, which then zeroes the whole of `scratch` with
`vg_zeroize` (`encrypt_verified`, `decrypt_verified`), then the cleanup that
clears the registers it may write and zeroes its 32 bytes of stack (its
postcondition reads the memory on return only within the buffers,
`wipedOk`). Either way they leave the whole of `scratch` as it was, or all of it
zero (`encrypt_wipes`, `decrypt_wipes`), and so meet their contract in constant
time and return without secret residue (`encrypt_scrubbed`,
`decrypt_scrubbed`), and which bytes of `scratch` are zero is public
(`encrypt_public`, `decrypt_public`).
-/

@[expose] public section

namespace VG.Proof.AesEcb.AArch64

open VG VG.AArch64 VG.Proof.Aes.AArch64

theorem depth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.aarch64Depth = 0 := by
  induction c <;> simp_all [Code.noFrames, Code.aarch64Depth]

/-- A call of `name`, whose code is `body`, then of `vg_zeroize` on the
2048 bytes of `scratch` (`Impl.AesEcb.AArch64.wiped`). -/
abbrev wiped (name : String) (body : Prog isa) : Prog isa := Impl.AesEcb.AArch64.wiped name body

/-- `vg_aes_ecb_encrypt` from `v`'s `vg_aes_encrypt_blocks`, wiping `scratch`. -/
def encrypt (v : BlocksImpl) : Prog isa := wiped v.enc.name v.enc.code

/-- `vg_aes_ecb_decrypt` from `v`'s `vg_aes_decrypt_blocks`, wiping `scratch`. -/
def decrypt (v : BlocksImpl) : Prog isa := wiped v.dec.name v.dec.code

theorem encBlocks (v : BlocksImpl) :
    Verified target v.enc.code (Spec.Aes.blocksSig.contract abi (pre 64) (post 64 enc) false 0 none) :=
  Proof.Aes.encryptBlocks_keyed (Verified.of_correct v.encOk v.encCt Aese.encryptBlocks_implies)

theorem decBlocks (v : BlocksImpl) :
    Verified target v.dec.code (Spec.Aes.blocksSig.contract abi (pre 64) (post 64 dec) false 0 none) :=
  Proof.Aes.decryptBlocks_keyed (Verified.of_correct v.decOk v.decCt Aese.decryptBlocks_implies)

theorem sat (g : List Byte → Spec.Aes.State → Spec.Aes.State) :
    ∃ s, (Spec.Aes.blocksSig.contract abi (pre 64) (ecbPost 64 g 2048) false 32 none).pre s := by
  implies_sat [Spec.Aes.blocksSig, pre, AArch64.abi, AArch64.argRegs] [blocksSat] using blocksSat

theorem zeroize_depth : 16 * Impl.Zeroize.AArch64.zeroizeWide.aarch64Depth ≤ 0 := by
  rw [depth_of_noFrames (by decide)]

theorem wiped_verified {g : List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {body : Prog isa}
    (h : Verified target body (Spec.Aes.blocksSig.contract abi (pre 64) (post 64 g) false 0 none))
    (hd : body.noFrames = true) :
    Verified target (wiped name body) (Spec.Aes.blocksSig.contract abi (pre 64) (ecbPost 64 g 2048) false 32 none) :=
  Verified.callWipe' (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("data", .slice true (.array .u8 16) "n")]) (ps₂ := []) (nm := "scratch") (e := .u64)
    (k := 256) (n := 2048) (i := 4) h Proof.Zeroize.AArch64.wideVerified (by decide) rfl rfl rfl
    (by decide) (by decide) (by rw [depth_of_noFrames hd]) Proof.Zeroize.AArch64.wide_noDit zeroize_depth
    (Nat.zero_le _)
    (pre_local 64) (post_local 64 g) (post_out 64 g) (AesEcb.wiped 64 g) (sat g)

theorem encrypt_verified (v : BlocksImpl) :
    Verified target (encrypt v) (wipedContract enc 2048 abi 32) :=
  wiped_verified (encBlocks v) v.encNoFrames

theorem decrypt_verified (v : BlocksImpl) :
    Verified target (decrypt v) (wipedContract dec 2048 abi 32) :=
  wiped_verified (decBlocks v) v.decNoFrames

theorem args_length : ∀ s vals,
    abi.args ((Spec.Aes.blocksSig.words abi.ptrBits).map (·.bits abi.ptrBits)) = some vals →
      (vals s).length = (Spec.Aes.blocksSig.words abi.ptrBits).length := by
  intro s vals hv
  obtain rfl := Option.some.inj (hv.symm.trans (rfl : abi.args _ = some (regArgs Spec.Aes.blocksSig)))
  exact regArgs_length Spec.Aes.blocksSig s (by decide)

theorem encrypt_free (v : BlocksImpl) (h : v.scratch = 0) :
    Verified target v.enc.code (wipedContract enc 0 abi) :=
  Verified.ecb_of_unwritten (encBlocks v) (v.encFree h) args_length

theorem decrypt_free (v : BlocksImpl) (h : v.scratch = 0) :
    Verified target v.dec.code (wipedContract dec 0 abi) :=
  Verified.ecb_of_unwritten (decBlocks v) (v.decFree h) args_length

theorem wipedOk (g : List Byte → Spec.Aes.State → Spec.Aes.State) :
    Scrub.ScrubAllOk (wipedContract g 2048 abi 32) 32 (Spec.Aes.blocksSig.retBits abi.ptrBits) :=
  Scrub.scrubAllOk_regs (sig := Spec.Aes.blocksSig) (by decide) (W := 32) (by decide) (Nat.le_refl _)
    (ecbPost_out _ g 2048)

private theorem wiped_scrubbed {k : Contract isa} {name : String} {body : Prog isa}
    (hv : Verified target (wiped name body) k) (hok : Scrub.ScrubAllOk k 32 0)
    (hs : Scrub.sideAll (fun i => !i.writesDit) body = true) (hd : body.noFrames = true) :
    VerifiedScrubbed target (Impl.Scrub.AArch64.scrubOf 32 0 (wiped name body)) k 0 :=
  Scrub.verifiedScrubbedOfFill (n := name) (e := Impl.AesEcb.AArch64.wiped "" (.block [])) hv hok
    (by kernel_rfl) hs (depth_of_noFrames hd) (by kernel_rfl) (by decide)
    (Nat.le_of_ble_eq_true (by kernel_rfl)) (.inl rfl)

/-- `vg_aes_ecb_encrypt` over `v`, as emitted: its code with the vector
registers it writes cleared where it needs no `scratch`, the call wiping
`scratch`, then its cleanup, otherwise. -/
theorem encrypt_wipes (v : BlocksImpl) :
    VerifiedScrubbed target (Impl.AesEcb.AArch64.Fn.blocks v.enc)
      (wipedContract enc (if v.scratch = 0 then 0 else 2048) abi (if v.scratch = 0 then 0 else 32)) 0 := by
  unfold Impl.AesEcb.AArch64.Fn.blocks
  rw [v.encScratch_eq]
  by_cases h : v.scratch = 0
  · simp only [h, ↓reduceIte]
    exact ⟨Clears.Verified.withClears (encrypt_free v h) v.encVecsOk, v.encRes h _, fun ty _ h => by cases ty <;> cases h⟩
  · simp only [h, ↓reduceIte]
    exact wiped_scrubbed (encrypt_verified v) (wipedOk enc) (Scrub.sideAll_noDit_of_calleeSide v.encScrub)
      v.encNoFrames

theorem encrypt_scrubbed (v : BlocksImpl) :
    VerifiedScrubbed target (Impl.AesEcb.AArch64.Fn.blocks v.enc)
      (Spec.AesEcb.encryptContract abi (if v.scratch = 0 then 0 else 32)) 0 :=
  encrypt_imp (encrypt_wipes v) id

theorem encrypt_public (v : BlocksImpl) :
    Spec.AesEcb.scratchOut.Of abi (Impl.AesEcb.AArch64.Fn.blocks v.enc)
      (Spec.AesEcb.encryptContract abi (if v.scratch = 0 then 0 else 32)) :=
  scratch_public (encrypt_wipes v)

/-- `vg_aes_ecb_decrypt` over `v`, as emitted. -/
theorem decrypt_wipes (v : BlocksImpl) :
    VerifiedScrubbed target (Impl.AesEcb.AArch64.Fn.blocks v.dec)
      (wipedContract dec (if v.scratch = 0 then 0 else 2048) abi (if v.scratch = 0 then 0 else 32)) 0 := by
  unfold Impl.AesEcb.AArch64.Fn.blocks
  rw [v.decScratch_eq]
  by_cases h : v.scratch = 0
  · simp only [h, ↓reduceIte]
    exact ⟨Clears.Verified.withClears (decrypt_free v h) v.decVecsOk, v.decRes h _, fun ty _ h => by cases ty <;> cases h⟩
  · simp only [h, ↓reduceIte]
    exact wiped_scrubbed (decrypt_verified v) (wipedOk dec) (Scrub.sideAll_noDit_of_calleeSide v.decScrub)
      v.decNoFrames

theorem decrypt_scrubbed (v : BlocksImpl) :
    VerifiedScrubbed target (Impl.AesEcb.AArch64.Fn.blocks v.dec)
      (Spec.AesEcb.decryptContract abi (if v.scratch = 0 then 0 else 32)) 0 :=
  decrypt_imp (decrypt_wipes v) id

theorem decrypt_public (v : BlocksImpl) :
    Spec.AesEcb.scratchOut.Of abi (Impl.AesEcb.AArch64.Fn.blocks v.dec)
      (Spec.AesEcb.decryptContract abi (if v.scratch = 0 then 0 else 32)) :=
  scratch_public (decrypt_wipes v)

end VG.Proof.AesEcb.AArch64
