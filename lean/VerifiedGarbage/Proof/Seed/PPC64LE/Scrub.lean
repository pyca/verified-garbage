module

public import VerifiedGarbage.Impl.Seed.PPC64LE.Fn
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Seed.Contract
public import VerifiedGarbage.Spec.Seed.Cbc
public import VerifiedGarbage.Spec.Seed.Cfb
public import VerifiedGarbage.Spec.Seed.CfbFinal
public import VerifiedGarbage.Spec.Seed.Ofb
public import VerifiedGarbage.Spec.Seed.OfbFinal
public import VerifiedGarbage.Proof.Seed.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Seed.PPC64LE.Frame
public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Seed.PPC64LE.Verified
import VerifiedGarbage.Proof.Seed.Scratch
import VerifiedGarbage.Proof.Seed.CbcScratch
import VerifiedGarbage.Proof.Seed.FbScratch
import VerifiedGarbage.Proof.Modes.CfbFinalScratch
import VerifiedGarbage.Proof.Framework.Lit

/-!
# SEED on PPC64LE, without secret residue

Key expansion and the CBC, CFB128 and OFB functions zero their whole frame
themselves before they release it (`withStackScratchWiped`), and have no
frames of their own inside it, so they need only the clearing of the
volatile registers they write after them (`PPC64LE.Scrub.verifiedScrubbedWiped`).
ECB, whose wiped frame holds the frame of the call it makes, is followed by
`Impl.Scrub.PPC64LE.scrubTail` with its stack wiped (`PPC64LE.Scrub.verifiedScrubbedAll`).
Their postconditions read the memory on return only within their buffers, by
the target-independent lemmas RISC-V's and x86-64's proofs use
(`Proof/Seed/RISCV64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub

/-! ## Postconditions -/

theorem expandKeyOut (stack : Nat) : PostOut (Spec.Seed.expandKeyContract PPC64LE.abi stack) (Spec.Seed.expandKeySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.expandKeyPostOut_local _)

theorem ecbEncryptOut (stack : Nat) : PostOut (Spec.Seed.ecbContract PPC64LE.abi .encrypt stack) (Spec.Seed.ecbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.ecbPostOut_local _ .encrypt)

theorem ecbDecryptOut (stack : Nat) : PostOut (Spec.Seed.ecbContract PPC64LE.abi .decrypt stack) (Spec.Seed.ecbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.ecbPostOut_local _ .decrypt)

theorem cbcEncryptOut (stack : Nat) : PostOut (Spec.Seed.cbcEncryptChainedContract PPC64LE.abi stack) (Spec.Seed.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.cbcEncChainedPostOut_local _)

theorem cbcDecryptOut (stack : Nat) : PostOut (Spec.Seed.cbcDecryptChainedContract PPC64LE.abi stack) (Spec.Seed.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.cbcDecChainedPostOut_local _)

theorem cfbEncryptOut (stack : Nat) : PostOut (Spec.Seed.cfbEncryptContract PPC64LE.abi stack) (Spec.Seed.cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.cfbEncPostOut_local _)

theorem cfbEncryptFinalOut (stack : Nat) : PostOut (Spec.Seed.cfbEncryptFinalContract PPC64LE.abi stack) (Spec.Seed.cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.encFinalPost_local _)

theorem cfbDecryptOut (stack : Nat) : PostOut (Spec.Seed.cfbDecryptContract PPC64LE.abi stack) (Spec.Seed.cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.cfbDecPostOut_local _)

theorem cfbDecryptFinalOut (stack : Nat) : PostOut (Spec.Seed.cfbDecryptFinalContract PPC64LE.abi stack) (Spec.Seed.cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.decFinalPost_local _)

theorem ofbOut (stack : Nat) : PostOut (Spec.Seed.ofbContract PPC64LE.abi stack) (Spec.Seed.ofbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.ofbPostOut_local _)

theorem ofbFinalOut (stack : Nat) : PostOut (Spec.Seed.ofbFinalContract PPC64LE.abi stack) (Spec.Seed.ofbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.ofbFinalPost_local _)

/-! ## The functions as emitted -/

/-- `vg_seed_expand_key` as emitted (`Impl.Seed.PPC64LE.Fn.expandKey`) meets its
contract in constant time and returns without secret residue. -/
theorem expandKey_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Seed.PPC64LE.Fn.expandKey
      (Spec.Seed.expandKeyContract PPC64LE.abi 1072) 0 :=
  verifiedScrubbedWiped (api := Spec.Seed.expandKeyApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1072 .r5 130 Impl.Seed.PPC64LE.expandKey
      verified := Proof.Seed.PPC64LE.expandKey_framed }
    1072 .r5 130 Impl.Seed.PPC64LE.expandKey
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩ rfl (expandKeyOut _) (by dsimp only; lit_decide)

/-- `vg_seed_ecb_encrypt` as emitted (`Impl.Seed.PPC64LE.Fn.ecbEncrypt`) meets its
contract in constant time and returns without secret residue. -/
theorem ecbEncrypt_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Seed.PPC64LE.Fn.ecbEncrypt
      (Spec.Seed.ecbContract PPC64LE.abi Spec.Seed.Direction.encrypt 1168) 0 :=
  verifiedScrubbedAll (api := Spec.Seed.ecbEncryptApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1120 .r6 136 (Impl.Seed.PPC64LE.ecbCall .encrypt)
      verified := Proof.Seed.PPC64LE.ecbCall_framed .encrypt }
    1168 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (ecbEncryptOut _)
    (by dsimp only; lit_decide)

/-- `vg_seed_ecb_decrypt` as emitted (`Impl.Seed.PPC64LE.Fn.ecbDecrypt`) meets its
contract in constant time and returns without secret residue. -/
theorem ecbDecrypt_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Seed.PPC64LE.Fn.ecbDecrypt
      (Spec.Seed.ecbContract PPC64LE.abi Spec.Seed.Direction.decrypt 1168) 0 :=
  verifiedScrubbedAll (api := Spec.Seed.ecbDecryptApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1120 .r6 136 (Impl.Seed.PPC64LE.ecbCall .decrypt)
      verified := Proof.Seed.PPC64LE.ecbCall_framed .decrypt }
    1168 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (ecbDecryptOut _)
    (by dsimp only; lit_decide)

/-- `vg_seed_cbc_encrypt_chained` as emitted
(`Impl.Seed.PPC64LE.Fn.cbcEncryptChained`) meets its contract in constant time
and returns without secret residue. -/
theorem cbcEncryptChained_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Seed.PPC64LE.Fn.cbcEncryptChained
      (Spec.Seed.cbcEncryptChainedContract PPC64LE.abi 1184) 0 :=
  verifiedScrubbedWiped (api := Spec.Seed.cbcEncryptChainedApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 Impl.Seed.PPC64LE.cbcEncryptChained
      verified := Proof.Seed.PPC64LE.cbcEnc_framed Proof.Seed.PPC64LE.Modes.cbcEncryptChained_verified }
    1184 .r7 144 Impl.Seed.PPC64LE.cbcEncryptChained
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩ rfl (cbcEncryptOut _) (by dsimp only; lit_decide)

/-- `vg_seed_cbc_decrypt_chained` as emitted
(`Impl.Seed.PPC64LE.Fn.cbcDecryptChained`) meets its contract in constant time
and returns without secret residue. -/
theorem cbcDecryptChained_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Seed.PPC64LE.Fn.cbcDecryptChained
      (Spec.Seed.cbcDecryptChainedContract PPC64LE.abi 1424) 0 :=
  verifiedScrubbedWiped (api := Spec.Seed.cbcDecryptChainedApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1424 .r7 174 Impl.Seed.PPC64LE.cbcDecryptChained
      verified := Proof.Seed.PPC64LE.cbcDec_framed Proof.Seed.PPC64LE.Modes.cbcDecryptChained_verified }
    1424 .r7 174 Impl.Seed.PPC64LE.cbcDecryptChained
    ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩ rfl (cbcDecryptOut _) (by dsimp only; lit_decide)

/-- `vg_seed_cfb128_encrypt` as emitted (`Impl.Seed.PPC64LE.Fn.cfbEncrypt`) meets
its contract in constant time and returns without secret residue. -/
theorem cfbEncrypt_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Seed.PPC64LE.Fn.cfbEncrypt
      (Spec.Seed.cfbEncryptContract PPC64LE.abi 1184) 0 :=
  verifiedScrubbedWiped (api := Spec.Seed.cfbEncryptApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 Impl.Seed.PPC64LE.cfbEncrypt
      verified := Proof.Seed.PPC64LE.cfbEnc_framed Proof.Seed.PPC64LE.Modes.cfbEncrypt_verified }
    1184 .r7 144 Impl.Seed.PPC64LE.cfbEncrypt
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩ rfl (cfbEncryptOut _) (by dsimp only; lit_decide)

/-- `vg_seed_cfb128_decrypt` as emitted (`Impl.Seed.PPC64LE.Fn.cfbDecrypt`) meets
its contract in constant time and returns without secret residue. -/
theorem cfbDecrypt_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Seed.PPC64LE.Fn.cfbDecrypt
      (Spec.Seed.cfbDecryptContract PPC64LE.abi 1424) 0 :=
  verifiedScrubbedWiped (api := Spec.Seed.cfbDecryptApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1424 .r7 174 Impl.Seed.PPC64LE.cfbDecrypt
      verified := Proof.Seed.PPC64LE.cfbDec_framed Proof.Seed.PPC64LE.Modes.cfbDecrypt_verified }
    1424 .r7 174 Impl.Seed.PPC64LE.cfbDecrypt
    ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩ rfl (cfbDecryptOut _) (by dsimp only; lit_decide)

/-- `vg_seed_cfb128_encrypt_final` as emitted
(`Impl.Seed.PPC64LE.Fn.cfbEncryptFinal`) meets its contract in constant time
and returns without secret residue. -/
theorem cfbEncryptFinal_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Seed.PPC64LE.Fn.cfbEncryptFinal
      (Spec.Seed.cfbEncryptFinalContract PPC64LE.abi 1184) 0 :=
  verifiedScrubbedWiped (api := Spec.Seed.cfbEncryptFinalApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 Impl.Seed.PPC64LE.cfbEncryptFinal
      verified := Proof.Seed.PPC64LE.FbFinal.cfbEncryptFinal_framed }
    1184 .r7 144 Impl.Seed.PPC64LE.cfbEncryptFinal
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩ rfl (cfbEncryptFinalOut _) (by dsimp only; lit_decide)

/-- `vg_seed_cfb128_decrypt_final` as emitted
(`Impl.Seed.PPC64LE.Fn.cfbDecryptFinal`) meets its contract in constant time
and returns without secret residue. -/
theorem cfbDecryptFinal_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Seed.PPC64LE.Fn.cfbDecryptFinal
      (Spec.Seed.cfbDecryptFinalContract PPC64LE.abi 1184) 0 :=
  verifiedScrubbedWiped (api := Spec.Seed.cfbDecryptFinalApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 Impl.Seed.PPC64LE.cfbDecryptFinal
      verified := Proof.Seed.PPC64LE.FbFinal.cfbDecryptFinal_framed }
    1184 .r7 144 Impl.Seed.PPC64LE.cfbDecryptFinal
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩ rfl (cfbDecryptFinalOut _) (by dsimp only; lit_decide)

/-- `vg_seed_ofb` as emitted (`Impl.Seed.PPC64LE.Fn.ofb`) meets its contract in
constant time and returns without secret residue. -/
theorem ofb_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Seed.PPC64LE.Fn.ofb
      (Spec.Seed.ofbContract PPC64LE.abi 1184) 0 :=
  verifiedScrubbedWiped (api := Spec.Seed.ofbApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 Impl.Seed.PPC64LE.ofb
      verified := Proof.Seed.PPC64LE.ofb_framed Proof.Seed.PPC64LE.Modes.ofb_verified }
    1184 .r7 144 Impl.Seed.PPC64LE.ofb
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩ rfl (ofbOut _) (by dsimp only; lit_decide)

/-- `vg_seed_ofb_final` as emitted (`Impl.Seed.PPC64LE.Fn.ofbFinal`) meets its
contract in constant time and returns without secret residue. -/
theorem ofbFinal_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Seed.PPC64LE.Fn.ofbFinal
      (Spec.Seed.ofbFinalContract PPC64LE.abi 1184) 0 :=
  verifiedScrubbedWiped (api := Spec.Seed.ofbFinalApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 Impl.Seed.PPC64LE.ofbFinal
      verified := Proof.Seed.PPC64LE.FbFinal.ofbFinal_framed }
    1184 .r7 144 Impl.Seed.PPC64LE.ofbFinal
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩ rfl (ofbFinalOut _) (by dsimp only; lit_decide)

end VG.Proof.Seed.PPC64LE.Scrub
