module

public import VerifiedGarbage.Proof.AesXts.AArch64.Aes.Top
public import VerifiedGarbage.Spec.Xts.Contract
public import VerifiedGarbage.Proof.Xts.Contract
meta import VerifiedGarbage.Proof.Xts.Contract
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesXts.AArch64.Verified
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
meta import VerifiedGarbage.Proof.AesXts.AArch64.Aes.Top
meta import VerifiedGarbage.Spec.Xts.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.AesXts.AArch64.Verified
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Aes.AArch64.CodeLit

/-!
# One-pass XTS-AES on AArch64: `Verified`

Correctness (`crypt_wp` with `encFn` or `decFn`, whose setups load the round
keys, `encSetup_ok'` and `decSetup_ok'`), the registers preserved (no
instruction writes a callee-saved one), constant time (`taint_decide`: only
the pointers, `rounds` and `n` reach a branch or an address), and the shared
contracts of `Spec/Xts/Contract.lean`, from the same contracts
`modeAArch64 (xtsMode enc)` as the functions calling a block function
(`AArch64/Verified.lean`).
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Aes

open VG VG.AArch64
open VG.Impl.AesXts.AArch64Aes (encrypt decrypt)
open VG.Proof.AesCbc.AArch64 (modeAArch64)
open VG.Proof.Aes.AArch64.Aese (encFn decFn)

theorem encFn_F : encFn.F = stF true := rfl

theorem decFn_F : decFn.F = stF false := rfl

theorem encrypt_keepsV : encrypt.allInstrs keepsV = true := by lit_decide

theorem decrypt_keepsV : decrypt.allInstrs keepsV = true := by lit_decide

theorem encrypt_noFrames : encrypt.noFrames = true := by lit_decide

theorem decrypt_noFrames : decrypt.noFrames = true := by lit_decide

theorem encrypt_correct (s : State) (hs : (modeAArch64 (AesXts.xtsMode true)).pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode true)).post s s' := by
  obtain ⟨t, s', he, h₂, h₁⟩ := WP.gprs (rs := preserved)
    (crypt_wp encFn true encFn_F (fun _ hp => encSetup_ok' hp) hs) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he encrypt_keepsV⟩, h₂⟩

theorem decrypt_correct (s : State) (hs : (modeAArch64 (AesXts.xtsMode false)).pre s) :
    ∃ t s', Exec isa decrypt s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode false)).post s s' := by
  obtain ⟨t, s', he, h₂, h₁⟩ := WP.gprs (rs := preserved)
    (crypt_wp decFn false decFn_F (fun _ hp => decSetup_ok' hp) hs) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he decrypt_keepsV⟩, h₂⟩

theorem encrypt_ct (enc : Bool) : ConstantTime isa (modeAArch64 (AesXts.xtsMode enc)).pre
    (modeAArch64 (AesXts.xtsMode enc)).pub encrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem decrypt_ct (enc : Bool) : ConstantTime isa (modeAArch64 (AesXts.xtsMode enc)).pre
    (modeAArch64 (AesXts.xtsMode enc)).pub decrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem encrypt_verified : Verified AArch64.target encrypt (Proof.Xts.aesEncryptContract AArch64.abi) :=
  Proof.AesXts.AArch64.encrypt_verified_of encrypt_correct (encrypt_ct true)

theorem decrypt_verified : Verified AArch64.target decrypt (Proof.Xts.aesDecryptContract AArch64.abi) :=
  Proof.AesXts.AArch64.decrypt_verified_of decrypt_correct (decrypt_ct false)

end VG.Proof.AesXts.AArch64.Aes
